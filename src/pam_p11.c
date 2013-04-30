/*
 * PKCS#11 PAM Login Module with support for GOST algorithms
 * Copyright (C) 2003 Mario Strasser <mast@gmx.net>,
 * modified by Kirill Romanovskiy <romanovskiy.k@gmail.com>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 */

#include <syslog.h>
#include <ctype.h>
#include <string.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#include <dlfcn.h>
#include <stddef.h>

#include <openssl/engine.h>
#include <openssl/x509.h>

#include <pkcs11/rtpkcs11.h>
#include "pam_helper.h"

#define PAM_SM_AUTH
#define PAM_SM_ACCOUNT
#define PAM_SM_SESSION
#define PAM_SM_PASSWORD
#include <security/pam_appl.h>
#include <security/pam_modules.h>
#ifdef HAVE_SECURITY_PAM_EXT_H
#include <security/pam_ext.h>
#else
#define pam_syslog(handle, level, msg ...) syslog(level, ## msg)
#endif

#ifndef PAM_EXTERN
#define PAM_EXTERN extern
#endif

#define LOGNAME "pam-p11-gost" 

#define RANDOM_SOURCE "/dev/urandom"
#define RANDOM_SIZE 128
#define MAX_SIGSIZE 256

extern int match_user(X509* x509, const char* login);

static CK_ATTRIBUTE valueTemplate[] = {{CKA_VALUE, NULL_PTR, 0}};
static CK_ATTRIBUTE idTemplate[] = {{CKA_ID, NULL_PTR, 0}};

static CK_OBJECT_CLASS certificateClass = CKO_CERTIFICATE;
static CK_CERTIFICATE_TYPE certificateType = CKC_X_509;
static CK_ATTRIBUTE certificateAttributes[] = {
	{CKA_CLASS, &certificateClass, sizeof(certificateClass)},
	{CKA_CERTIFICATE_TYPE, &certificateType, sizeof(certificateType)}
};

static CK_OBJECT_CLASS privateKeyClass = CKO_PRIVATE_KEY;
static CK_KEY_TYPE keyType = CKK_GOSTR3410;
static CK_ATTRIBUTE privateKeyTemplate[] = {
	{CKA_CLASS, &privateKeyClass, sizeof(privateKeyClass)},
	{CKA_KEY_TYPE, &keyType, sizeof(keyType)},
	{CKA_ID, NULL_PTR, 0}
};

CK_MECHANISM gost3410HashSignMech = {CKM_GOSTR3410_WITH_GOSTR3411, NULL_PTR, 0};
const CK_ULONG kMaxObjectCount = 100;

#define numof(arr)  (sizeof(arr) / sizeof((arr)[0]))

PAM_EXTERN int pam_sm_authenticate(pam_handle_t* pamh, int flags, int argc, const char** argv)
{
	int rv = -1;
	const char* user;
	char* pin;
	char password_prompt[64];

	struct pam_conv* conv;
	struct pam_message msg;
	struct pam_response* resp;
	struct pam_message*(msgp[1]);

	EVP_PKEY* publicKey;
	unsigned char randomData[RANDOM_SIZE];
	int fd;
	unsigned int i;

	void* pkcs11Module;
	CK_C_GetFunctionList pkcsGetFunctionList;
	CK_FUNCTION_LIST_PTR pkcs;
	CK_ULONG slotCount;
	CK_SLOT_ID_PTR slotIds = NULL;
	CK_SLOT_ID slot;
	CK_SESSION_HANDLE session;
	CK_TOKEN_INFO tokenInfo;

	CK_ULONG certificateCount = 0;
	CK_ULONG certificateSize = 0;
	CK_OBJECT_HANDLE certificateObjects[kMaxObjectCount];
	CK_OBJECT_HANDLE certificateHandle;
	unsigned char* certificateValue = NULL;
	X509* x509Certificate = NULL;

	CK_UTF8CHAR_PTR certificateId = NULL;
	CK_ULONG certificateIdLength;

	CK_ULONG privateKeyCount = 0;
	CK_OBJECT_HANDLE privateKeyObjects[kMaxObjectCount];
	CK_OBJECT_HANDLE privateKeyHandle;

	CK_ULONG signatureLength = 0;
	CK_BYTE_PTR signature = NULL;

	ENGINE* gostEngine;
	if (argc != 1) {
		pam_syslog(pamh, LOG_ERR, "need pkcs11 module as argument");
		return PAM_ABORT;
	}

#ifndef NDEBUG
	CRYPTO_malloc_init();
	CRYPTO_mem_ctrl(CRYPTO_MEM_CHECK_ON);
#endif
	ENGINE_load_builtin_engines();
	gostEngine = ENGINE_by_id("gost");
	if (!gostEngine) {
		goto opensslEngineCleanup;
	}
	if (!ENGINE_init(gostEngine)) {
		goto opensslGostEngineFree;
	}
	ENGINE_set_default(gostEngine, ENGINE_METHOD_ALL);
	OpenSSL_add_all_algorithms();

	// get PAM username
	rv = pam_get_user(pamh, &user, NULL);
	if (rv != PAM_SUCCESS) {
		pam_syslog(pamh, LOG_ERR, "pam_get_user() failed %s", pam_strerror(pamh, rv));
		return PAM_USER_UNKNOWN;
	}

	pkcs11Module = dlopen(argv[0], RTLD_NOW);
	if (!pkcs11Module) {
		pam_syslog(pamh, LOG_ERR, "failed to load PKCS#11 library");
		return PAM_AUTHINFO_UNAVAIL;
	}
	pkcsGetFunctionList = (CK_C_GetFunctionList)dlsym(pkcs11Module, "C_GetFunctionList");
	PKCS_checkerr(rv, "failed to load PKCS#11 library", dlFinish)
	pkcsGetFunctionList(&pkcs);
	rv = pkcs->C_Initialize(NULL);
	PKCS_checkerr_ex(rv, pamh, "C_Initialize", dlFinish);
	rv = pkcs->C_GetSlotList(CK_TRUE, NULL_PTR, &slotCount);
	PKCS_checkerr_ex(rv, pamh, "C_GetSlotList", pkcs11Finish);

	if (slotCount != 1) {
		if (slotCount == 0)
			pam_syslog(pamh, LOG_ERR, "no token available");
		else
			pam_syslog(pamh, LOG_ERR, "use only one token");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11Finish;
	}
	slotIds = (CK_SLOT_ID*)OPENSSL_malloc(slotCount * sizeof(CK_SLOT_ID));
	if (!slotIds) {
		pam_syslog(pamh, LOG_ERR, "out of memory");
		goto pkcs11Finish;
	}
	rv = pkcs->C_GetSlotList(CK_TRUE, slotIds, &slotCount);
	PKCS_checkerr_ex(rv, pamh, "C_GetSlotList", pkcs11Finish);
	slot = slotIds[0];
	rv = pkcs->C_GetTokenInfo(slot, &tokenInfo);
	PKCS_checkerr_ex(rv, pamh, "C_GetTokenInfo", pkcs11Finish);
	rv = pkcs->C_OpenSession(slot, (CKF_SERIAL_SESSION | CKF_RW_SESSION), NULL, NULL, &session);
	PKCS_checkerr_ex(rv, pamh, "C_OpenSession", pkcs11Finish);
	rv = pkcs->C_FindObjectsInit(session, certificateAttributes, numof(certificateAttributes));
	PKCS_checkerr_ex(rv, pamh, "C_FindObjectsInit", pkcs11SessionFinish);
	rv = pkcs->C_FindObjects(session, certificateObjects, kMaxObjectCount, &certificateCount);
	PKCS_checkerr_ex(rv, pamh, "C_FindObjects", pkcs11SessionFinish);
	rv = pkcs->C_FindObjectsFinal(session);
	PKCS_checkerr_ex(rv, pamh, "C_FindObjectsFinal", pkcs11SessionFinish);

	if (certificateCount == 0) {
		pam_syslog(pamh, LOG_ERR, "no certificates found on token");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	for (i = 0; i < certificateCount; i++) {
		certificateHandle = certificateObjects[i];
		rv = pkcs->C_GetAttributeValue(session, certificateHandle, valueTemplate, numof(valueTemplate));
		PKCS_checkerr_ex(rv, pamh, "C_GetAttributeValue", pkcs11SessionFinish);
		certificateSize = valueTemplate[0].ulValueLen;
		certificateValue = (unsigned char*)OPENSSL_malloc(certificateSize);
		if (!certificateValue) {
			pam_syslog(pamh, LOG_ERR, "out of memory");
			goto pkcs11SessionFinish;
		}
		valueTemplate[0].pValue = certificateValue;
		rv = pkcs->C_GetAttributeValue(session, certificateHandle, valueTemplate, numof(valueTemplate));
		PKCS_checkerr_ex(rv, pamh, "C_GetAttributeValue", pkcs11SessionFinish);

		do {
			const unsigned char* data = certificateValue;
			x509Certificate = d2i_X509(NULL, &data, certificateSize);
			if (!x509Certificate) {
				pam_syslog(pamh, LOG_ERR, "failed to decode certificate");
				continue;
			}
		} while (0);
		// check whether the certificate matches the user
		rv = match_user(x509Certificate, user);
		if (rv < 0) {
			pam_syslog(pamh, LOG_ERR, "match_user() failed");
			rv = PAM_AUTHINFO_UNAVAIL;
			goto pkcs11SessionFinish;
		} else if (rv == 0) {
			/* this is not the cert we are looking for */
			x509Certificate = NULL;
			OPENSSL_free(certificateValue);
			certificateValue = NULL;
		} else {
			break;
		}
	}
	if (!x509Certificate) {
		pam_syslog(pamh, LOG_ERR, "matching certificate not found");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}

	rv = pkcs->C_GetAttributeValue(session, certificateHandle, idTemplate, numof(idTemplate));
	PKCS_checkerr_ex(rv, pamh, "C_GetAttributeValue", pkcs11SessionFinish);
	certificateIdLength = idTemplate[0].ulValueLen;
	certificateId = (CK_UTF8CHAR_PTR)OPENSSL_malloc(certificateIdLength * sizeof(CK_UTF8CHAR));
	if (!certificateId) {
		pam_syslog(pamh, LOG_ERR, "out of memory");
		goto pkcs11SessionFinish;
	}
	idTemplate[0].pValue = certificateId;
	rv = pkcs->C_GetAttributeValue(session, certificateHandle, idTemplate, numof(idTemplate));
	PKCS_checkerr_ex(rv, pamh, "C_GetAttributeValue", pkcs11SessionFinish);

	// get token PIN via PAM
	msgp[0] = &msg;
	rv = pam_get_item(pamh, PAM_AUTHTOK, (void*)&pin);
	if (rv == PAM_SUCCESS && pin) {
		pin = strdup(pin);
	} else {
		sprintf(password_prompt, "PIN for token %.32s: ", tokenInfo.label);
		msg.msg_style = PAM_PROMPT_ECHO_OFF;
		msg.msg = password_prompt;
		rv = pam_get_item(pamh, PAM_CONV, (const void**)&conv);
		PAM_checkerr(rv, pamh, "failed to get password from user", pkcs11SessionFinish);
		if ((conv == NULL) || (conv->conv == NULL)) {
			rv = PAM_AUTHINFO_UNAVAIL;
			goto pkcs11SessionFinish;
		}
		rv = conv->conv(1, (const struct pam_message**)msgp, &resp, conv->appdata_ptr);
		PAM_checkerr(rv, pamh, "failed to get password from user", pkcs11SessionFinish);
		if ((resp == NULL) || (resp[0].resp == NULL)) {
			rv = PAM_AUTHINFO_UNAVAIL;
			goto pkcs11SessionFinish;
		}
		pin = strdup(resp[0].resp);
		memset(resp[0].resp, 0, strlen(resp[0].resp));
		free(&resp[0]);
	}
	rv = pkcs->C_Login(session, CKU_USER, (CK_UTF8CHAR*)pin, pin ? strlen(pin) : 0);
	memset(pin, 0, strlen(pin));
	free(pin);
	if (rv != CKR_OK) {
		if (rv == CKR_PIN_INCORRECT)
			pam_syslog(pamh, LOG_ERR, "Incorrect PIN entered");
		else
			pam_syslog(pamh, LOG_ERR, "C_Login failed with error 0x%08X", rv);
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	// get private key by certificate id
	privateKeyTemplate[2].pValue = certificateId;
	privateKeyTemplate[2].ulValueLen = certificateIdLength;
	rv = pkcs->C_FindObjectsInit(session, privateKeyTemplate, numof(privateKeyTemplate));
	PKCS_checkerr_ex(rv, pamh, "C_FindObjectsInit", pkcs11SessionFinish);
	rv = pkcs->C_FindObjects(session, privateKeyObjects, kMaxObjectCount, &privateKeyCount);
	PKCS_checkerr_ex(rv, pamh, "C_FindObjects", pkcs11SessionFinish);
	rv = pkcs->C_FindObjectsFinal(session);
	PKCS_checkerr_ex(rv, pamh, "C_FindObjectsFinal", pkcs11SessionFinish);

	if (privateKeyCount != 1) {
		if (privateKeyCount == 0)
			pam_syslog(pamh, LOG_ERR, "private key not found on token");
		else
			pam_syslog(pamh, LOG_ERR, "multiple matching private keys found");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	privateKeyHandle = privateKeyObjects[0];

	fd = open(RANDOM_SOURCE, O_RDONLY);
	if (fd < 0) {
		pam_syslog(pamh, LOG_ERR, "fatal: cannot open RANDOM_SOURCE: ");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	rv = read(fd, randomData, RANDOM_SIZE);
	if (rv < 0) {
		pam_syslog(pamh, LOG_ERR, "fatal: read from random source failed: ");
		close(fd);
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	if (rv < RANDOM_SIZE) {
		pam_syslog(pamh, LOG_ERR, "fatal: read returned less than %d<%d bytes\n", rv, RANDOM_SIZE);
		close(fd);
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	close(fd);

	rv = pkcs->C_SignInit(session, &gost3410HashSignMech, privateKeyHandle);
	PKCS_checkerr_ex(rv, pamh, "C_SignInit", pkcs11SessionFinish);
	rv = pkcs->C_Sign(session, randomData, RANDOM_SIZE, NULL_PTR, &signatureLength);
	PKCS_checkerr_ex(rv, pamh, "C_Sign", pkcs11SessionFinish);

	signature = (CK_BYTE_PTR)OPENSSL_malloc(signatureLength);
	if (!signature) {
		pam_syslog(pamh, LOG_ERR, "out of memory");
		goto pkcs11SessionFinish;
	}
	rv = pkcs->C_Sign(session, randomData, RANDOM_SIZE, signature, &signatureLength);
	PKCS_checkerr_ex(rv, pamh, "C_Sign", pkcs11SessionFinish);

	publicKey = X509_get_pubkey(x509Certificate);
	if (publicKey == NULL) {
		pam_syslog(pamh, LOG_ERR, "could not extract public key");
		rv = PAM_AUTHINFO_UNAVAIL;
		goto pkcs11SessionFinish;
	}
	const EVP_MD* md = EVP_get_digestbyname("md_gost94");
	if (!md) {
		pam_syslog(pamh, LOG_ERR, "failed to get gost digest");
		goto pkcs11SessionFinish;
	}
	EVP_MD_CTX* mdctx = EVP_MD_CTX_create();
	if (!mdctx) {
		pam_syslog(pamh, LOG_ERR, "failed to init gost digest");
		goto pkcs11SessionFinish;
	}
	rv = EVP_VerifyInit_ex(mdctx, md, gostEngine);
	if (rv == 0) {
		pam_syslog(pamh, LOG_ERR, "EVP_VerifyInit_ex failed");
		goto pkcs11SessionFinish;
	}
	rv = EVP_VerifyUpdate(mdctx, randomData, RANDOM_SIZE);
	if (rv == 0) {
		pam_syslog(pamh, LOG_ERR, "EVP_VerifyUpdate failed");
		goto pkcs11SessionFinish;
	}
	rv = EVP_VerifyFinal(mdctx, signature, signatureLength, publicKey);
	if (rv == -1) {
		pam_syslog(pamh, LOG_ERR, "EVP_VerifyFinal failed");
		goto pkcs11SessionFinish;
	}
	rv = PAM_SUCCESS;

pkcs11SessionFinish:
	pkcs->C_CloseSession(session);
pkcs11Finish:
	pkcs->C_Finalize(NULL);
dlFinish:
	dlclose(pkcs11Module);
opensslFinish:
	if (slotIds)
		OPENSSL_free(slotIds);
	if (certificateValue)
		OPENSSL_free(certificateValue);
	if (certificateId)
		OPENSSL_free(certificateId);
	if (signature)
		OPENSSL_free(signature);
opensslGostEngineFinish:
	ENGINE_finish(gostEngine);
opensslGostEngineFree:
	ENGINE_free(gostEngine);
opensslEngineCleanup:
	ENGINE_cleanup();

	return rv;
}

PAM_EXTERN int pam_sm_setcred(pam_handle_t* pamh, int flags, int argc,
                              const char** argv)
{
	/* Actually, we should return the same value as pam_sm_authenticate(). */
	return PAM_SUCCESS;
}

PAM_EXTERN int pam_sm_acct_mgmt(pam_handle_t* pamh, int flags, int argc,
                                const char** argv)
{
	pam_syslog(pamh, LOG_WARNING,
	           "Function pam_sm_acct_mgmt() is not implemented in this module");
	return PAM_SERVICE_ERR;
}

PAM_EXTERN int pam_sm_open_session(pam_handle_t* pamh, int flags, int argc,
                                   const char** argv)
{
	pam_syslog(pamh, LOG_WARNING,
	           "Function pam_sm_open_session() is not implemented in this module");
	return PAM_SERVICE_ERR;
}

PAM_EXTERN int pam_sm_close_session(pam_handle_t* pamh, int flags, int argc,
                                    const char** argv)
{
	pam_syslog(pamh, LOG_WARNING,
	           "Function pam_sm_close_session() is not implemented in this module");
	return PAM_SERVICE_ERR;
}

PAM_EXTERN int pam_sm_chauthtok(pam_handle_t* pamh, int flags, int argc,
                                const char** argv)
{
	pam_syslog(pamh, LOG_WARNING,
	           "Function pam_sm_chauthtok() is not implemented in this module");
	return PAM_SERVICE_ERR;
}

#ifdef PAM_STATIC
/* static module data */
struct pam_module _pam_group_modstruct = {
	"pam-p11-gost",
	pam_sm_authenticate,
	pam_sm_setcred,
	pam_sm_acct_mgmt,
	pam_sm_open_session,
	pam_sm_close_session,
	pam_sm_chauthtok
};
#endif

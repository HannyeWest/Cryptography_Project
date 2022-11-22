/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#ifdef __linux__
#include <bsd/stdlib.h>
#elif __APPLE__
#include <stdlib.h>
#else
#include <stdlib.h>
#endif
#include <string.h>
#include <gmp.h>
#include "pkcs.h"
#include "sha2.h"

#include <stdio.h>
#include <math.h>

/*
 * rsa_generate_key() - generates RSA keys e, d and n in octet strings.
 * If mode = 0, then e = 65537 is used. Otherwise e will be randomly selected.
 * Carmichael's totient function Lambda(n) is used.
 */
void rsa_generate_key(void *_e, void *_d, void *_n, int mode)
{
    mpz_t p, q, lambda, e, d, n, gcd;
    gmp_randstate_t state;

    /*
     * Initialize mpz variables
     */
    mpz_inits(p, q, lambda, e, d, n, gcd, NULL);
    gmp_randinit_default(state);
    gmp_randseed_ui(state, arc4random());
    /*
     * Generate prime p and q such that 2^(RSAKEYSIZE-1) <= p*q < 2^RSAKEYSIZE
     */
    do {
        do {
            mpz_urandomb(p, state, RSAKEYSIZE/2);
            mpz_setbit(p, 0);
            mpz_setbit(p, RSAKEYSIZE/2-1);
        } while (mpz_probab_prime_p(p, 50) == 0);
        do {
            mpz_urandomb(q, state, RSAKEYSIZE/2);
            mpz_setbit(q, 0);
            mpz_setbit(q, RSAKEYSIZE/2-1);
        } while (mpz_probab_prime_p(q, 50) == 0);
        mpz_mul(n, p, q);
    } while (!mpz_tstbit(n, RSAKEYSIZE-1));
    /*
     * Generate e and d using Lambda(n)
     */
    mpz_sub_ui(p, p, 1);
    mpz_sub_ui(q, q, 1);
    mpz_lcm(lambda, p, q);
    if (mode == 0)
        mpz_set_ui(e, 65537);
    else do {
        mpz_urandomb(e, state, RSAKEYSIZE);
        mpz_gcd(gcd, e, lambda);
    } while (mpz_cmp(e, lambda) >= 0 || mpz_cmp_ui(gcd, 1) != 0);
    mpz_invert(d, e, lambda);
    /*
     * Convert mpz_t values into octet strings
     */
    mpz_export(_e, NULL, 1, RSAKEYSIZE/8, 1, 0, e);
    mpz_export(_d, NULL, 1, RSAKEYSIZE/8, 1, 0, d);
    mpz_export(_n, NULL, 1, RSAKEYSIZE/8, 1, 0, n);
    /*
     * Free the space occupied by mpz variables
     */
    mpz_clears(p, q, lambda, e, d, n, gcd, NULL);
}

/*
 * rsa_cipher() - compute m^k mod n
 * If m >= n then returns PKCS_MSG_OUT_OF_RANGE, otherwise returns 0 for success.
 */
static int rsa_cipher(void *_m, const void *_k, const void *_n)
{
    mpz_t m, k, n;

    /*
     * Initialize mpz variables
     */
    mpz_inits(m, k, n, NULL);
    /*
     * Convert big-endian octets into mpz_t values
     */
    mpz_import(m, RSAKEYSIZE/8, 1, 1, 1, 0, _m);
    mpz_import(k, RSAKEYSIZE/8, 1, 1, 1, 0, _k);
    mpz_import(n, RSAKEYSIZE/8, 1, 1, 1, 0, _n);
    /*
     * Compute m^k mod n
     */
    if (mpz_cmp(m, n) >= 0) {
        mpz_clears(m, k, n, NULL);
        return PKCS_MSG_OUT_OF_RANGE;
    }
    mpz_powm(m, m, k, n);
    /*
     * Convert mpz_t m into the octet string _m
     */
    mpz_export(_m, NULL, 1, RSAKEYSIZE/8, 1, 0, m);
    /*
     * Free the space occupied by mpz variables
     */
    mpz_clears(m, k, n, NULL);
    return 0;
}

static void Hash(unsigned char *msg, int len, unsigned char *dest, int sha2_ndx)
{
  if(sha2_ndx == SHA224) sha224(msg, len, dest);
  else if(sha2_ndx == SHA256) sha256(msg, len, dest);
  else if(sha2_ndx == SHA384) sha384(msg, len, dest);
  else if(sha2_ndx == SHA512) sha512(msg, len, dest);
  else if(sha2_ndx == SHA512_224) sha512_224(msg, len, dest);
  else sha512_256(msg, len, dest);
}

static int MGF(unsigned char *mgfSeed, unsigned int seedLen, int maskLen, unsigned char *mask, int sha2_ndx){
  // define hLen
  unsigned int hLen = 0;
  if(sha2_ndx == SHA224 || sha2_ndx == SHA512_224) hLen = SHA224_DIGEST_SIZE;
  else if(sha2_ndx == SHA256 || sha2_ndx == SHA512_256) hLen = SHA256_DIGEST_SIZE;
  else if(sha2_ndx == SHA384) hLen = SHA384_DIGEST_SIZE;
  else if(sha2_ndx == SHA512) hLen = SHA384_DIGEST_SIZE;

  if(maskLen > 0x100000000*hLen) return PKCS_MSG_TOO_LONG;

  unsigned char *T = NULL, C[4];
  T = (unsigned char *) malloc(seedLen + 4);
  memcpy(T, mgfSeed, seedLen);
  int len = maskLen / hLen + (maskLen % hLen == 0 ? 0 : 1);
  for(int counter=0; counter<len; counter++){
    // counter -> octet string
    C[0] = (unsigned char) ((counter >> 24) & 0xff);
		C[1] = (unsigned char) ((counter >> 16) & 0xff);
		C[2] = (unsigned char) ((counter >>  8) & 0xff);
		C[3] = (unsigned char) (counter & 0xff);
    memcpy(T + seedLen, C, 4);

    if (counter*hLen + hLen < maskLen) {
      Hash(T, seedLen + 4, mask + counter*hLen, sha2_ndx);
    } else {
      unsigned char tHash[hLen];
      Hash(T, seedLen + 4, tHash, sha2_ndx);
      int diff = maskLen - counter*hLen;
      memcpy(mask + counter*hLen, tHash, diff);
      break;
    }
  }
  return 0;
}

/*
 * rsaes_oaep_encrypt() - RSA encrytion with the EME-OAEP encoding method
 * 길이가 len 바이트인 메시지 m을 공개키 (e,n)으로 암호화한 결과를 c에 저장한다.
 * label은 데이터를 식별하기 위한 라벨 문자열로 NULL을 입력하여 생략할 수 있다.
 * sha2_ndx는 사용할 SHA-2 해시함수 색인 값으로 SHA224, SHA256, SHA384, SHA512,
 * SHA512_224, SHA512_256 중에서 선택한다. c의 크기는 RSAKEYSIZE와 같아야 한다.
 * 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int rsaes_oaep_encrypt(const void *m, size_t mLen, const void *label, const void *e, const void *n, void *c, int sha2_ndx)
{
  unsigned char *EM = NULL, *maskedSeed = NULL, *maskedDB = NULL, *seedMask = NULL, *dbMask = NULL, *DB = NULL, *seed = NULL;
  unsigned int hLen = 0;

  // 1. Length Checking
  if(strlen(label) >= LIMIT_L) return PKCS_LABEL_TOO_LONG;

  // define hLen
  if(sha2_ndx == SHA224 || sha2_ndx == SHA512_224) hLen = SHA224_DIGEST_SIZE;
  else if(sha2_ndx == SHA256 || sha2_ndx == SHA512_256) hLen = SHA256_DIGEST_SIZE;
  else if(sha2_ndx == SHA384) hLen = SHA384_DIGEST_SIZE;
  else if(sha2_ndx == SHA512) hLen = SHA384_DIGEST_SIZE;

  if(mLen > (RSAKEYSIZE/8 - 2*hLen -2)) return PKCS_MSG_TOO_LONG;

  // 2. EME-OAEP encoding
  EM = (unsigned char *) malloc(RSAKEYSIZE/8);
  DB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); maskedDB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); dbMask = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1);
  seed = (unsigned char *) malloc(hLen); maskedSeed = (unsigned char *) malloc(hLen); seedMask = (unsigned char *) malloc(hLen);

  // generate lHash
  Hash((unsigned char*)label, strlen(label), DB, sha2_ndx);

  // generate PS
  memset(DB + hLen, 0x00, RSAKEYSIZE/8 - mLen - 2*hLen - 2);

  // concatenate All
  DB[RSAKEYSIZE/8 - mLen - hLen - 2] = 0x01;
  memcpy(DB + RSAKEYSIZE/8 - mLen - hLen - 1, (unsigned char*)m, mLen);
  // generate seed
  arc4random_buf(seed, hLen);

  // masking
  MGF(seed, hLen, RSAKEYSIZE/8 - hLen - 1, dbMask, sha2_ndx);
  for(int i = 0; i < RSAKEYSIZE/8 - hLen - 1; i++) maskedDB[i] = (DB[i] ^ dbMask[i]);

  MGF(maskedDB, RSAKEYSIZE/8 - hLen - 1, hLen, seedMask, sha2_ndx);
  for(int i = 0; i < hLen; i++) maskedSeed[i] = (seed[i] ^ seedMask[i]);

  EM[0] = 0x00;
  memcpy (EM + 1, maskedSeed, hLen);
  memcpy (EM + 1 + hLen, maskedDB, RSAKEYSIZE/8 - hLen - 1);
  memcpy(c, EM, RSAKEYSIZE/8);

  // 3. RSA encrytion
  rsa_cipher(c, e, n);
  return 0;
}

/*
 * rsaes_oaep_decrypt() - RSA decrytion with the EME-OAEP encoding method
 * 암호문 c를 개인키 (d,n)을 사용하여 원본 메시지 m과 길이 len을 회복한다.
 * label과 sha2_ndx는 암호화할 때 사용한 것과 일치해야 한다.
 * 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int rsaes_oaep_decrypt(void *m, size_t *mLen, const void *label, const void *d, const void *n, const void *c, int sha2_ndx)
{
  unsigned char *EM = NULL, *maskedSeed = NULL, *maskedDB = NULL, *seedMask = NULL, *dbMask = NULL, *DB = NULL, *lHash = NULL, *seed = NULL;
  unsigned int hLen = 0;

  // unsigned int cLen = sizeof(c);
  // printf("~~~~~-1~~~~\n");
  // printf("%d ~~\n", cLen);

  // define hLen
  if(sha2_ndx == SHA224 || sha2_ndx == SHA512_224) hLen = SHA224_DIGEST_SIZE;
  else if(sha2_ndx == SHA256 || sha2_ndx == SHA512_256) hLen = SHA256_DIGEST_SIZE;
  else if(sha2_ndx == SHA384) hLen = SHA384_DIGEST_SIZE;
  else if(sha2_ndx == SHA512) hLen = SHA384_DIGEST_SIZE;

  // 1. Length Checking
  if(strlen(label) >= LIMIT_L) return PKCS_LABEL_TOO_LONG;
  // if(cLen != RSAKEYSIZE/8) return PKCS_MSG_OUT_OF_RANGE;
  if(RSAKEYSIZE/8 < 2*hLen + 2) return PKCS_MSG_OUT_OF_RANGE;

  // 2. EME-OAEP encoding
  EM = (unsigned char *) malloc(RSAKEYSIZE/8);
  DB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); maskedDB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); dbMask = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1);
  seed = (unsigned char *) malloc(hLen); maskedSeed = (unsigned char *) malloc(hLen); seedMask = (unsigned char *) malloc(hLen);
  lHash = (unsigned char *) malloc(hLen);

  // generate lHash
  Hash((unsigned char*)label, strlen(label), lHash, sha2_ndx);

  // 2. RSA decrytion
  memcpy(EM, c, RSAKEYSIZE/8);
  rsa_cipher(EM, d, n);

  // 3. EME-OAEP decoding
  if(EM[0] != 0x00) return PKCS_INITIAL_NONZERO;

  memcpy(maskedSeed, EM + 1, hLen);
  memcpy(maskedDB, EM + hLen + 1, RSAKEYSIZE/8 - hLen - 1);

  MGF(maskedDB, RSAKEYSIZE/8 - hLen - 1, hLen, seedMask, sha2_ndx);
  for(int i = 0; i < hLen; i++) seed[i] = (maskedSeed[i] ^ seedMask[i]);

  MGF(seed, hLen, RSAKEYSIZE/8 - hLen - 1, dbMask, sha2_ndx);
  for(int i = 0; i < RSAKEYSIZE/8 - hLen - 1; i++) DB[i] = (maskedDB[i] ^ dbMask[i]);

  for(int i=0; i<hLen; i++){
    if(DB[i] != lHash[i]) return PKCS_HASH_MISMATCH;
  }

  int index = -1;
  for(int i=hLen; i<(RSAKEYSIZE/8 - hLen - 1); i++){
    if(DB[i] == 0x01){
      index = i;
      break;
    }
  }
  if(index == -1 || index == (RSAKEYSIZE/8 - hLen - 2)) return PKCS_INVALID_PS;

  *mLen = RSAKEYSIZE/8 - hLen - 2 - index;
  memcpy(m, DB+index+1, *mLen);

  return 0;
}

/*
 * rsassa_pss_sign - RSA Signature Scheme with Appendix
 * 길이가 len 바이트인 메시지 m을 개인키 (d,n)으로 서명한 결과를 s에 저장한다.
 * s의 크기는 RSAKEYSIZE와 같아야 한다. 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int rsassa_pss_sign(const void *m, size_t mLen, const void *d, const void *n, void *s, int sha2_ndx)
{
  unsigned char *EM = NULL, *maskedDB = NULL, *H = NULL, *M = NULL, *mHash = NULL, *DB = NULL, *dbMask = NULL, *salt = NULL;
  unsigned int hLen = 0;

  // 1. Length Checking
  if(mLen >= LIMIT_L) return PKCS_MSG_TOO_LONG;

  // define hLen
  if(sha2_ndx == SHA224 || sha2_ndx == SHA512_224) hLen = SHA224_DIGEST_SIZE;
  else if(sha2_ndx == SHA256 || sha2_ndx == SHA512_256) hLen = SHA256_DIGEST_SIZE;
  else if(sha2_ndx == SHA384) hLen = SHA384_DIGEST_SIZE;
  else if(sha2_ndx == SHA512) hLen = SHA384_DIGEST_SIZE;

  // 2. ESMA-PSS encoding
  EM = (unsigned char *) malloc(RSAKEYSIZE/8); maskedDB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); H = (unsigned char *) malloc(hLen);
  M = (unsigned char *) malloc(8+2*hLen); mHash = (unsigned char *) malloc(hLen);
  salt = (unsigned char *) malloc(hLen);
  DB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); dbMask= (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1);

  // generate mHash
  Hash((unsigned char*)m, mLen, mHash, sha2_ndx);

  if(RSAKEYSIZE/8 < 2*hLen + 2) return PKCS_MSG_OUT_OF_RANGE;

  arc4random_buf(salt, hLen);

  memset(M, 0x00, 8);
  memcpy(M + 8, mHash, hLen);
  memcpy(M + 8 + hLen, salt, hLen);

  // generate H
  Hash(M, 2*hLen + 8, H, sha2_ndx);

  memset(DB, 0x00, RSAKEYSIZE/8 - 2*hLen - 2);
  DB[RSAKEYSIZE/8 - 2*hLen - 2] = 0x01;
  memcpy(DB + RSAKEYSIZE/8 - 2*hLen - 1, salt, hLen);

  MGF(H, hLen, RSAKEYSIZE/8 - hLen - 1, dbMask, sha2_ndx);

  for(int i = 0; i < RSAKEYSIZE/8 - hLen - 1; i++) maskedDB[i] = (DB[i] ^ dbMask[i]);
  if (maskedDB[0] >> 7 != 0) maskedDB[0] = maskedDB[0] & 0x7f;

  memcpy(EM, maskedDB, RSAKEYSIZE/8 - hLen - 1);
  memcpy(EM + RSAKEYSIZE/8 - hLen - 1, H, hLen);
  EM[RSAKEYSIZE/8-1] = 0xbc;

  memcpy(s, EM, RSAKEYSIZE/8);
  rsa_cipher(s, d, n);
  return 0;
}

/*
 * rsassa_pss_verify - RSA Signature Scheme with Appendix
 * 길이가 len 바이트인 메시지 m에 대한 서명이 s가 맞는지 공개키 (e,n)으로 검증한다.
 * 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int rsassa_pss_verify(const void *m, size_t mLen, const void *e, const void *n, const void *s, int sha2_ndx)
{
  unsigned char *EM = NULL, *maskedDB = NULL, *H = NULL, *M = NULL, *mHash = NULL, *DB = NULL, *dbMask = NULL, *verifyH = NULL, *salt = NULL;
  unsigned int hLen = 0;

  // 1. Length Checking
  if(mLen >= LIMIT_L) return PKCS_MSG_TOO_LONG;

  // define hLen
  if(sha2_ndx == SHA224 || sha2_ndx == SHA512_224) hLen = SHA224_DIGEST_SIZE;
  else if(sha2_ndx == SHA256 || sha2_ndx == SHA512_256) hLen = SHA256_DIGEST_SIZE;
  else if(sha2_ndx == SHA384) hLen = SHA384_DIGEST_SIZE;
  else if(sha2_ndx == SHA512) hLen = SHA384_DIGEST_SIZE;

  // 2. ESMA-PSS encoding
  EM = (unsigned char *) malloc(RSAKEYSIZE/8); maskedDB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); H = (unsigned char *) malloc(hLen);
  M = (unsigned char *) malloc(8+2*hLen); mHash = (unsigned char *) malloc(hLen); verifyH = (unsigned char *) malloc(hLen);
  salt = (unsigned char *) malloc(hLen);
  DB = (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1); dbMask= (unsigned char *) malloc(RSAKEYSIZE/8-hLen-1);

  // generate mHash
  Hash((unsigned char*)m, mLen, mHash, sha2_ndx);

  memcpy(EM, s, RSAKEYSIZE/8);
  rsa_cipher(EM, e, n);

  if(RSAKEYSIZE/8 < 2*hLen + 2) return PKCS_MSG_OUT_OF_RANGE;
  if(EM[RSAKEYSIZE/8-1] != 0xbc) return PKCS_INVALID_LAST;
  if (EM[0] >> 7 != 0) return PKCS_INVALID_INIT;

  memcpy(maskedDB, EM, RSAKEYSIZE/8 - hLen - 1);

  memcpy(H, EM + RSAKEYSIZE/8 - hLen - 1, hLen);
  MGF(H, hLen, RSAKEYSIZE/8 - hLen - 1, dbMask, sha2_ndx);

  for(int i = 0; i < RSAKEYSIZE/8 - hLen - 1; i++) DB[i] = (maskedDB[i] ^ dbMask[i]);
  DB[0] &= 0b1111111;

  if(DB[RSAKEYSIZE/8 - 2*hLen - 2] != 0x01) return PKCS_INVALID_PD2;

  memcpy(salt, DB + RSAKEYSIZE/8 - 2*hLen - 1 , hLen);

  memset(M, 0x00, 8);
  memcpy(M + 8, mHash, hLen);
  memcpy(M + 8 + hLen, salt, hLen);

  // generate H
  Hash(M, 2*hLen + 8, verifyH, sha2_ndx);

  for(int i=0; i<hLen; i++){
    if(H[i] != verifyH[i]) return PKCS_HASH_MISMATCH;
  }

  return 0;
}

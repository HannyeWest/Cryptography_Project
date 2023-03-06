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
#include <gmp.h>
#include "ecdsa.h"
#include "sha2.h"

static mpz_t p, n, Gx, Gy;

inline static void *matchingHash(int sha2_ndx) {
  switch (sha2_ndx) {
    case SHA224:
      return sha224;
    case SHA256:
      return sha256;
    case SHA384:
      return sha384;
    case SHA512:
      return sha512;
    case SHA512_224:
      return sha512_224;
    case SHA512_256:
      return sha512_256;
    default:
      return NULL;
  }
}

inline static int hashLen(int sha2_ndx) {
  switch (sha2_ndx) {
    case SHA224: case SHA512_224:
      return SHA224_DIGEST_SIZE;
    case SHA256: case SHA512_256:
      return SHA256_DIGEST_SIZE;
    case SHA384:
      return SHA384_DIGEST_SIZE;
    case SHA512:
      return SHA512_DIGEST_SIZE;
    default:
      return 0;
  }
}

/*
 * Initialize 256 bit ECDSA parameters
 * 시스템파라미터 p, n, G의 공간을 할당하고 값을 초기화한다.
 */
void ecdsa_p256_init(void)
{
  // mpz_t Gx, Gy;
  mpz_inits(p, n, Gx, Gy, NULL);

  mpz_set_str(p, "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF", 16);
  mpz_set_str(n, "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551", 16);

  mpz_set_str(Gx, "6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296", 16);
  mpz_set_str(Gy, "4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5", 16);
}

/*
 * Clear 256 bit ECDSA parameters
 * 할당된 파라미터 공간을 반납한다.
 */
void ecdsa_p256_clear(void)
{
  mpz_clears(p, n, Gx, Gy, NULL);
}

// 계산은 모두 mod p를 해야하기 때문에 따로 inline function 으로 구현
inline static void p256_mul(mpz_t r, mpz_t a, mpz_t b)
{
  mpz_t t;
  mpz_init(t);
  mpz_mul(t, a, b);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

inline static void p256_mul_ui(mpz_t r, mpz_t a, unsigned long int b)
{
  mpz_t t;
  mpz_init(t);
  mpz_mul_ui(t, a, b);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

inline static void p256_sub(mpz_t r, mpz_t a, mpz_t b)
{
  mpz_t t;
  mpz_init(t);
  mpz_sub(t, a, b);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

inline static void p256_sub_ui(mpz_t r, mpz_t a, unsigned long int b)
{
  mpz_t t;
  mpz_init(t);
  mpz_sub_ui(t, a, b);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

inline static void p256_div(mpz_t r, mpz_t a, mpz_t b)
{
  mpz_t t;
  mpz_init(t);
  mpz_invert(t, b, p);
  mpz_mul(t, a, t);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

inline static void p256_div_ui(mpz_t r, mpz_t a, unsigned long int b)
{
  mpz_t t;
  mpz_init(t);
  mpz_set_ui(t, b);
  mpz_invert(t, t, p);
  mpz_mul(t, a, t);
  mpz_mod(r, t, p);
  mpz_clear(t);
}

static void p256_ecc_addition(mpz_t x3, mpz_t y3, mpz_t x1, mpz_t y1, mpz_t x2, mpz_t y2){
  // lambda 식과 여러 temp 저장 위한 변수
  mpz_t lambda, t, tx1, ty1, tx2, ty2;
  mpz_inits(lambda, t, tx1, ty1, tx2, ty2, NULL);

  mpz_set(tx1, x1);
  mpz_set(ty1, y1);
  mpz_set(tx2, x2);
  mpz_set(ty2, y2);

  // lambda = (y1-y2)/(x1-x2)
  p256_sub(lambda, ty1, ty2);
  p256_sub(t, tx1, tx2);
  p256_div(lambda, lambda, t);

  // x3 = lambda^2-x1-x2
  p256_mul(x3, lambda, lambda);
  p256_sub(x3, x3, tx1);
  p256_sub(x3, x3, tx2);
  // y3 = lambda(x1-x3)-y1
  p256_sub(y3, tx1, x3);
  p256_mul(y3, lambda, y3);
  p256_sub(y3, y3, ty1);

  mpz_clears(lambda, t, tx1, ty1, tx2, ty2, NULL);
}

static void p256_ecc_doubling(mpz_t x3, mpz_t y3, mpz_t x, mpz_t y){
  // lambda 식 저장 위한 변수
  mpz_t lambda;
  mpz_init(lambda);

  // lambda = 3*x^2 + a / 2*y
  p256_mul(lambda, x, x);
  p256_mul_ui(lambda, lambda, 3);
  p256_sub_ui(lambda, lambda, 3);
  p256_div(lambda, lambda, y);
  p256_div_ui(lambda, lambda, 2);

  // x3 = lambda^2 - 2*x
  p256_mul(x3, lambda, lambda);
  p256_sub(x3, x3, x);
  p256_sub(x3, x3, x);
  // y3 = lambda*(x-x3)-y
  p256_sub(y3, x, x3);
  p256_mul(y3, lambda, y3);
  p256_sub(y3, y3, y);

  mpz_clear(lambda);
}

static void p256_ecc_multiplication(mpz_t d, mpz_t Qx, mpz_t Qy, mpz_t init_x, mpz_t init_y){
  mpz_t ex, ey, x, y;
  mpz_inits(ex, ey, x, y, NULL);

  mpz_set(ex, init_x);
  mpz_set(ey, init_y);

  // r = 0;
  mpz_set_ui(Qx, 0);
  mpz_set_ui(Qy, 0);

  // double addition
  mp_bitcnt_t offset = mpz_scan1(d, 0), bit_idx = 0;

  while(offset != -1) {
    // doubling
    while(bit_idx < offset){
      p256_ecc_doubling(x, y, ex, ey);
      mpz_set(ex, x);
      mpz_set(ey, y);
      bit_idx++;
    }
    offset = mpz_scan1(d, bit_idx + 1);

    // 더하는 값이 다른 경우
    if(mpz_cmp_ui(Qx, 0) == 0 && mpz_cmp_ui(Qy, 0) == 0) {
        mpz_set(Qx, ex);
        mpz_set(Qy, ey);
    } else p256_ecc_addition(Qx, Qy, Qx, Qy, ex, ey);
  }
  mpz_clears(ex, ey, x, y, NULL);
}

/*
 * ecdsa_p256_key() - generates Q = dG
 * 사용자의 개인키와 공개키를 무작위로 생성한다.
 */
void ecdsa_p256_key(void *d, ecdsa_p256_t *Q)
{
  mpz_t _d, Qx, Qy;
  gmp_randstate_t state;

  mpz_inits(_d, Qx, Qy, NULL);
  gmp_randinit_default(state);
  gmp_randseed_ui(state, arc4random());

  do {
    mpz_urandomb(_d, state, ECDSA_P256/8);
  } while (mpz_probab_prime_p(_d, 50) == 0);

  p256_ecc_multiplication(_d, Qx, Qy, Gx, Gy);

  mpz_export(d, NULL, 1, ECDSA_P256/8, 1, 0, _d);
  mpz_export(Q->x, NULL, 1, ECDSA_P256/8, 1, 0, Qx);
  mpz_export(Q->y, NULL, 1, ECDSA_P256/8, 1, 0, Qy);
  mpz_clears(_d, Qx, Qy, NULL);
}

/*
 * ecdsa_p256_sign(msg, len, d, r, s) - ECDSA Signature Generation
 * 길이가 len 바이트인 메시지 m을 개인키 d로 서명한 결과를 r, s에 저장한다.
 * sha2_ndx는 사용할 SHA-2 해시함수 색인 값으로 SHA224, SHA256, SHA384, SHA512,
 * SHA512_224, SHA512_256 중에서 선택한다. r과 s의 길이는 256비트이어야 한다.
 * 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int ecdsa_p256_sign(const void *msg, size_t len, const void *d, void *_r, void *_s, int sha2_ndx)
{
  size_t hLen = hashLen(sha2_ndx);
  unsigned char mHash[hLen];

  void (* hash) (const unsigned char *, size_t, unsigned char *) = matchingHash(sha2_ndx);
  hash(msg, len, mHash);

  mpz_t e, k, r, s, x1, y1, _d, kinv;
  mpz_inits(e, k, r, s, x1, y1, _d, kinv, NULL);
  mpz_import(_d, ECDSA_P256 / 8, 1, 1, 1, 0, d);

  if(hLen > ECDSA_P256/8){
    unsigned char longHash[ECDSA_P256/8];
    for (int i = 0; i < ECDSA_P256/8; i++) {
      longHash[i] = mHash[i];
    }
    mpz_import(e, ECDSA_P256/8, 1, 1, 1, 0, longHash);
  } else mpz_import(e, hLen, 1, 1, 1, 0, mHash);


  do { // s = 0 -> go step 1
      do { // r = 0 -> go step 1
          gmp_randstate_t state;
          gmp_randinit_default(state);
          gmp_randseed_ui(state, arc4random());
          mpz_urandomm(k, state, n);
          // mpz_set_str(k, "09F634B188CEFD98E7EC88B1AA9852D734D0BC272F7D2A47DECC6EBEB375AAD4", 16);

          // 1. curve (x, y) = kG
          p256_ecc_multiplication(k, x1, y1, Gx, Gy);
          // 2. r = x mod n
          mpz_mod(r, x1, n);
      } while(mpz_cmp_ui(r, 0) == 0);
      // 3. s = kinv(e+rd) mod n
      mpz_invert(kinv, k, n);
      mpz_mul(_d, _d, r);
      mpz_add(e, e, _d);
      mpz_mul(s, kinv, e);
      mpz_mod(s, s, n);
  } while (mpz_cmp_ui(s, 0) == 0);

  mpz_export(_r, NULL, 1, ECDSA_P256 / 8, 1, 0, r);
  mpz_export(_s, NULL, 1, ECDSA_P256 / 8, 1, 0, s);
  mpz_clears(e, k, r, s, x1, y1, _d, kinv, NULL);
  return 0;
}


/*
 * ecdsa_p256_verify(msg, len, Q, r, s) - ECDSA signature veryfication
 * It returns 0 if valid, nonzero otherwise.
 * 길이가 len 바이트인 메시지 m에 대한 서명이 (r,s)가 맞는지 공개키 Q로 검증한다.
 * 성공하면 0, 그렇지 않으면 오류 코드를 넘겨준다.
 */
int ecdsa_p256_verify(const void *msg, size_t len, const ecdsa_p256_t *_Q, const void *_r, const void *_s, int sha2_ndx)
{
  // 입력 MSG 한도 초과
  if(len >= 0x2000000000000000) return ECDSA_MSG_TOO_LONG;

  // r,s [1, n-1]
  mpz_t r, s;
  mpz_inits(r, s, NULL);

  mpz_import(r, ECDSA_P256 / 8, 1, 1, 1, 0, _r);
  mpz_import(s, ECDSA_P256 / 8, 1, 1, 1, 0, _s);

  if(mpz_cmp_ui(r, 1) < 0 || mpz_cmp(r, n) >=0) return ECDSA_SIG_INVALID;
  if(mpz_cmp_ui(s, 1) < 0 || mpz_cmp(s, n) >=0) return ECDSA_SIG_INVALID;

  size_t hLen = hashLen(sha2_ndx);
  unsigned char mHash[hLen];

  void (* hash) (const unsigned char *, size_t, unsigned char *) = matchingHash(sha2_ndx);
  hash(msg, len, mHash);

  mpz_t e, u1, u2, Qx, Qy, x1, y1, x2, y2, Ox, Oy;
  mpz_inits(e, u1, u2, Qx, Qy, x1, y1, x2, y2, Ox, Oy, NULL);

  mpz_import(Qx, ECDSA_P256 / 8, 1, 1, 1, 0, _Q->x);
  mpz_import(Qy, ECDSA_P256 / 8, 1, 1, 1, 0, _Q->y);

  if(hLen > ECDSA_P256/8){
    unsigned char longHash[ECDSA_P256/8];
    for (int i = 0; i < ECDSA_P256/8; i++) {
      longHash[i] = mHash[i];
    }
    mpz_import(e, ECDSA_P256/8, 1, 1, 1, 0, longHash);
  } else mpz_import(e, hLen, 1, 1, 1, 0, mHash);

  mpz_invert(s, s, n);

  mpz_mul(u1, e, s);
  mpz_mod(u1, u1, n);

  mpz_mul(u2, r, s);
  mpz_mod(u2, u2, n);

  p256_ecc_multiplication(u1, x1, y1, Gx, Gy);
  p256_ecc_multiplication(u2, x2, y2, Qx, Qy);
  p256_ecc_addition(x1, y1, x1, y1, x2, y2);

  // (x1, y1) = O
  p256_ecc_multiplication(n, Ox, Oy, Gx, Gy);
  if(mpz_cmp(x1, Ox) == 0 && mpz_cmp(y1, Oy) == 0) return ECDSA_SIG_INVALID;
  mpz_mod(x1, x1, n);
  if(mpz_cmp(r, x1) != 0) return ECDSA_SIG_MISMATCH;
  mpz_clears(r, s, e, u1, u2, Qx, Qy, x1, y1, x2, y2, Ox, Oy, NULL);
  return 0;
}

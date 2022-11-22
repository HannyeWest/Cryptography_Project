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
#include "mRSA.h"
/*
 * mod_add() - computes a + b mod m
 */
static uint64_t mod_add(uint64_t a, uint64_t b, uint64_t m)
{
  if(a >= (m - b)) return (a - (m - b)) % m;
  else return (a + b) % m;
}

/*
 * mod_mul() - computes a * b mod m
 */
static uint64_t mod_mul(uint64_t a, uint64_t b, uint64_t m)
{
  uint64_t r = 0;
  while (b > 0) {
    if (b & 1) r = mod_add(r % m, a % m, m);
    b = b >> 1;
    a = mod_add(a % m, a % m, m);
  }
  return r;
}

/*
 * mod_pow() - computes a^b mod m
 */
static uint64_t mod_pow(uint64_t a, uint64_t b, uint64_t m)
{
  uint64_t r = 1;
  while (b > 0){
    if (b & 1) r = mod_mul(r % m, a % m, m);
    b = b >> 1;
    a = mod_mul(a % m, a % m, m);
  }
  return r;
}

/*
 * gcd() - Euclidean algorithm
 */
static uint64_t gcd(uint64_t a, uint64_t b)
{
  if(a == 0) return b; // a가 0일때 처리
  if(b == 0) return a; // b가 0일때 처리

  // 유클리드 알고리즘 gcd(a,b) = gcd(b,a mod b)를 사용
  uint64_t n;
  while(b != 0){
    n = a % b;
    a = b;
    b = n;
  }
  return a;
}

/*
 * mul_inv() - computes multiplicative inverse a^-1 mod m
 * It returns 0 if no inverse exist.
 */
static uint64_t mul_inv(uint64_t a, uint64_t m)
{
  uint64_t d0 = a, d1 = m; // d0, d1 초기화
  uint64_t x0 = 1, x1 = 0; // x0, x1 초기화

  int iter = 1; // 갱신이 되는 횟수 check

  uint64_t temp_x, temp_d, q;

  while(d1 != 0){
    q = d0 / d1; // 몫 저장
    temp_d = d0 % d1; // d(next) 저장

    // 부호가 없기 때문에 위 처럼 -로 계산하면 underflow 따라서 +로 계산
    temp_x = x0 + q*x1; // x(n) 저장

    x0 = x1, x1 = temp_x, d0 = d1, d1 = temp_d; // d(n), x(n) 갱신
    iter = -iter; // 전부 +로 계산하므로, -계산되는 횟수 저장
  }

  if(d0 == 1){ // d(k) 가 1일때 역이 존재한다.
    if(iter < 0) return (m-x0); // 음수 처리
    else return x0;
  } else return 0;
}

/*
 * Miller-Rabin Primality Testing against small sets of bases
 *
 * if n < 2^64,
 * it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, and 37.
 *
 * if n < 3317044064679887385961981,
 * it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, and 41.
 */
static const uint64_t a[BASELEN] = {2,3,5,7,11,13,17,19,23,29,31,37};

/*
 * miller_rabin() - Miller-Rabin Primality Test (deterministic version)
 *
 * n > 3, an odd integer to be tested for primality
 * It returns 1 if n is prime, 0 otherwise.
 */
static int miller_rabin(uint64_t n)
{
  // n<=3, n > 3 짝수인 경우 처리
  if(n == 2 || n == 3) return PRIME;
  if(n < 2 || n%2 == 0) return COMPOSITE;

  // Small sets of bases 활용해 제거
  for(int i=0; i<BASELEN; i++){
    if(n%a[i] == 0){
      if(n == a[i]) return PRIME;
      else return COMPOSITE;
    }
  }
  if(n < a[BASELEN-1]) return COMPOSITE;

  // k와 q 찾기
  int k = 0;
  uint64_t q = (n-1);
  while(!(q & 1)){
    q >>= 1;
    k++;
  }

  for(int i=0; i<BASELEN; i++){
    // if a^q mod n = 1 then return (“inconclusive");
    // j가 0일때, if( (a^q)^(2^j) mod n = n-1 ) then return (“inconclusive")
    uint64_t x = mod_pow(a[i], q, n);
    if(x == 1 || x == (n-1)) continue;

    // for j = 1 to k–1 do
    //   if( (a^q)^(2^j) mod n = n-1 ) then return (“inconclusive")
    int flag = 0; // 소수인 조건 check위한 변수
    for(int j=0; j<k; j++){
      uint64_t exp_k = 1 << j; // (a^q)^(2^j) mod n
      if(mod_pow(x, exp_k, n) == (n-1)){ // n-1 이라면 소수
        flag = 1;
        break;
      }
    }
    if(!flag) return COMPOSITE;
  }
	return PRIME;
}

/*
 * mRSA_generate_key() - generates mini RSA keys e, d and n
 *
 * Carmichael's totient function Lambda(n) is used.
 *       𝜆(𝑛)=lcm(𝑝−1,𝑞−1) = (𝑝−1)(𝑞−1) / gcd(𝑝 − 1, 𝑞 − 1)
 */
void mRSA_generate_key(uint64_t *e, uint64_t *d, uint64_t *n)
{
  // 길이가 32 비트 내 외인 임의의 두 소수 𝑝와 𝑞를 생성
  uint32_t p, q;
  uint64_t shift_p, shift_q;
  while(1){
    p = arc4random(); q = arc4random();
    if(miller_rabin(p) == PRIME && miller_rabin(q) == PRIME && p != q){
      shift_p = p; shift_q = q;
      // RSA 모듈러스 𝑛값은 263 ≤ 𝑛 < 264을 만족 해야한다.
      if((shift_p * shift_q) >= MINIMUM_N) break;
    }
  }
  *n = shift_p * shift_q;
  // Carmichael's totient function Lambda(n) is used.
  uint64_t lambda_n = ((shift_p-1) * (shift_q-1)) / gcd(shift_p-1, shift_q-1);
  // 키의 길이가 64 바이트인 RSA 공개 키 (𝑒, 𝑛)과 개인 키 (𝑑,𝑛)을 생성한다.
  while (1){
    arc4random_buf(e, sizeof(uint64_t));
    if(gcd(*e, lambda_n) == 1) break;
  }
  *d = mul_inv(*e, lambda_n);
}

/*
 * mRSA_cipher() - compute m^k mod n
 *
 * If data >= n then returns 1 (error), otherwise 0 (success).
 */
int mRSA_cipher(uint64_t *m, uint64_t k, uint64_t n)
{
  // 𝑚 ≥ 𝑛이면 𝑚이 값의 범위를 넘었으므로 오류로 처리
  if(*m >= n) return 1;
  else *m = mod_pow(*m, k, n);

  if(*m >= n) return 1;
  else return 0;
}

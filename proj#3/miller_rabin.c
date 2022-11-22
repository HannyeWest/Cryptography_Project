/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#include "miller_rabin.h"

/*
 * mod_add() - computes a+b mod m
 * a와 b가 m보다 작다는 가정하에서 a+b >= m이면 결과에서 m을 빼줘야 하므로
 * 오버플로가 발생하지 않도록 a-(m-b)를 계산하고, 그렇지 않으면 그냥 a+b를 계산하면 된다.
 * a+b >= m을 검사하는 과정에서 오버플로가 발생할 수 있으므로 a >= m-b를 검사한다.
 */
uint64_t mod_add(uint64_t a, uint64_t b, uint64_t m)
{
  if(a >= (m - b)) return (a - (m - b)) % m;
  else return (a + b) % m;
}

/*
 * mod_sub() - computes a-b mod m
 * 만일 a < b이면 결과가 음수가 되므로 m을 더해서 양수로 만든다.
 */
uint64_t mod_sub(uint64_t a, uint64_t b, uint64_t m)
{
  if(a < b) return (a + (m - b)) % m;
  else return (a - b) % m;
}

/*
 * mod_mul() - computes a*b mod m
 * a*b에서 오버플로가 발생할 수 있기 때문에 덧셈을 사용하여 빠르게 계산할 수 있는
 * "double addition" 알고리즘을 사용한다. 그 알고리즘은 다음과 같다.
 *     r = 0;
 *     while (b > 0) {
 *         if (b & 1)
 *             r = mod_add(r, a, m);
 *         b = b >> 1;
 *         a = mod_add(a, a, m);
 *     }
 */
uint64_t mod_mul(uint64_t a, uint64_t b, uint64_t m)
{
  uint64_t r = 0;
  while (b > 0) {
    if (b & 1) r = mod_add(r, a, m);
    b = b >> 1;
    a = mod_add(a, a, m);
  }
  return r;
}

/*
 * mod_pow() - computes a^b mod m
 * a^b에서 오버플로가 발생할 수 있기 때문에 곱셈을 사용하여 빠르게 계산할 수 있는
 * "square multiplication" 알고리즘을 사용한다. 그 알고리즘은 다음과 같다.
 *     r = 1;
 *     while (b > 0) {
 *         if (b & 1)
 *             r = mod_mul(r, a, m);
 *         b = b >> 1;
 *         a = mod_mul(a, a, m);
 *     }
 */
uint64_t mod_pow(uint64_t a, uint64_t b, uint64_t m)
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
 * Miller-Rabin Primality Testing against small sets of bases
 *
 * if n < 2^64,
 * it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, and 37.
 *
 * if n < 3,317,044,064,679,887,385,961,981,
 * it is enough to test a = 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, and 41.
 */
const uint64_t a[BASELEN] = {2,3,5,7,11,13,17,19,23,29,31,37};

/*
 * miller_rabin() - Miller-Rabin Primality Test (deterministic version)
 *
 * n > 3, an odd integer to be tested for primality
 * It returns PRIME if n is prime, COMPOSITE otherwise.
 */

int miller_rabin(uint64_t n)
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

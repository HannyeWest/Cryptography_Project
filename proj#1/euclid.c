/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#include "euclid.h"

/*
 * gcd() - Euclidean algorithm
 *
 * 유클리드 알고리즘 gcd(a,b) = gcd(b,a mod b)를 사용하여 최대공약수를 계산한다.
 * 만일 a가 0이면 b가 최대공약수가 된다. 그 반대도 마찬가지이다.
 * a, b가 모두 음이 아닌 정수라고 가정한다.
 * 재귀함수 호출을 사용하지 말고 while 루프를 사용하여 구현하는 것이 빠르고 좋다.
 */
int gcd(int a, int b)
{
  if(a == 0) return b; // a가 0일때 처리
  if(b == 0) return a; // b가 0일때 처리

  // 유클리드 알고리즘 gcd(a,b) = gcd(b,a mod b)를 사용
  int n;
  while(b != 0){
    n = a % b;
    a = b;
    b = n;
  }
  return a;
}

/*
 * xgcd() - Extended Euclidean algorithm
 *
 * 확장유클리드 알고리즘은 두 수의 최대공약수 gcd(a,b) = ax + by 식을
 * 만족하는 x와 y를 계산하는 알고리즘이다. 강의노트를 참조하여 구현한다.
 * a, b가 모두 음이 아닌 정수라고 가정한다.
 */
int xgcd(int a, int b, int *x, int *y)
{
  int x0 = 1, x1 = 0; // x0, x1 초기화
  int y0 = 0, y1 = 1; // y0, y1 초기화
  int d0 = a, d1 = b; // d0, d1 초기화

  int q, temp_d, temp_x, temp_y;
  while(d1 != 0){
    q = d0 / d1; // 몫 저장
    temp_d = d0 % d1; // d(next) 저장
    d0 = d1, d1 = temp_d; // d(n) 갱신
    temp_x = x0 - q*x1; // x(next) 저장
    x0 = x1, x1 = temp_x; // x(n) 갱신
    temp_y = y0 - q*y1; // y(next) 저장
    y0 = y1, y1 = temp_y; // y(n) 갱신
  }

  *x = x0; // x 입력
  *y = y0; // y 입력
  return d0;
}

/*
 * mul_inv() - computes multiplicative inverse a^-1 mod m
 *
 * 모듈로 m에서 a의 곱의 역인 a^-1 mod m을 구한다.
 * 만일 역이 존재하지 않으면 0을 리턴한다.
 * 확장유클리드 알고리즘을 변형하여 구현한다. 강의노트를 참조한다.
 */
int mul_inv(int a, int m)
{
  // d(k)가 1일때, 1 = a*x(k) + b*y(k)
  // 양변에 mod b를 하면, 1 = a*x(k)
  // 따라서 a^-1 mod b = x(k)
  //
  int d0 = a, d1 = m; // d0, d1 초기화
  int x0 = 1, x1 = 0; // x0, x1 초기화

  int q, temp_d, temp_x;
  while (d1 > 1) {
    q = d0 / d1; // 몫 저장
    temp_d = d0 - q*d1; // d(n) 저장
    d0 = d1, d1 = temp_d; // d(n) 갱신
    temp_x = x0 - q*x1; // x(n) 저장
    x0 = x1, x1 = temp_x; // x(n) 갱신
  }
  // d(k) 가 1일때 역이 존재한다.
  if(d1 == 1) return (x1>0 ? x1 : x1+m); // 음수 처리
  else return 0;
}

/*
 * umul_inv() - computes multiplicative inverse a^-1 mod m
 *
 * 입력이 unsigned 64 비트 정수일 때 모듈로 m에서 a의 곱의 역인 a^-1 mod m을 구한다.
 * 만일 역이 존재하지 않으면 0을 리턴한다. 확장유클리드 알고리즘을 변형하여 구현한다.
 * 입출력 모두가 unsigned 64 비트 정수임에 주의한다.
 */
uint64_t umul_inv(uint64_t a, uint64_t m)
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

// 
// uint64_t umul_inv(uint64_t a, uint64_t m) {
//   uint64_t d0 = a, d1 = m, x0 = 1, x1 = 0, q, temp1;
//   uint8_t f0 = 1, f1 = 1, temp2; // 변수 x 의 부호에 대한 정보를 가지는 변수 f
//   while (d1 > 1) {
//     q = d0 / d1;
//     d0 = d0 - q * d1;
//     if(f1 != f0) { // 서로 부호가 다르면 x0와 q * x1의 값과 상관 없이 부호가 결정됨.
//       x0 = x0 + q * x1;
//       f0 = !f1;
//     } else { // 서로 부호가 같다면 x0와 q * x1의 값을 비교하여 부호를 결정함.
//       if(x0 >= q * x1) {
//         x0 = x0 - q * x1;
//         f0 = f1;
//       }
//       else {
//         x0 = q * x1 - x0;
//         f0 = !f1;
//       }
//     }
//     temp1 = d0; d0 = d1; d1 = temp1;
//     temp1 = x0; x0 = x1; x1 = temp1;
//     temp2 = f0; f0 = f1; f1 = temp2;
//   }
//   if (d1 == 1) {
//       if(f1 == 0) return m - x1;
//       else return x1;
//   } else return 0;
// }

/*
 * gf16_mul(a, b) - a * b mod x^16+x^5+x^3+x+1
 *
 * 15차식 다항식 a와 b를 곱하고 결과를 16차식 x^16+x^5+x^3+x+1로 나눈 나머지를 계산한다.
 * x^16 = x^5+x^3+x+1 (mod x^16+x^5+x^3+x+1) 특성을 이용한다.
 */
uint16_t gf16_mul(uint16_t a, uint16_t b)
{
  uint16_t r = 0;
  while(b > 0){
    if(b & 1) r = r ^ a;
    b = b >> 1;
    a = ((a << 1) ^ ((a >> 15) & 1 ? 0x002B : 0));
    // x^16 = x^5+x^3+x+1 (mod x^16+x^5+x^3+x+1) 특성을 이용
  }
  return r;
}

/*
 * gf16_pow(a,b) - a^b mod x^16+x^5+x^3+x+1
 *
 * 15차식 다항식 a를 b번 지수승한 결과를 16차식 x^16+x^5+x^3+x+1로 나눈 나머지를 계산한다.
 * gf16_mul()과 "Square Multiplication" 알고리즘을 사용하여 구현한다.
 */
uint16_t gf16_pow(uint16_t a, uint16_t b)
{
  // (a*a) mod b => (a mod b * a mod b) mod b
  uint16_t r = 1;
  while (b > 0) {
    if(b & 1) r = gf16_mul(r, a);
    b = b >> 1;
    a = gf16_mul(a, a);
  }
  return r;
}

/*
 * gf16_inv(a) - a^-1 mod x^16+x^5+x^3+x+1
 *
 * 모둘러 x^16+x^5+x^3+x+1에서 a의 역을 구한다.
 * 역을 구하는 가장 효율적인 방법은 다항식 확장유클리드 알고리즘을 사용하는 것이다.
 * 다만 여기서는 복잡성을 피하기 위해 느리지만 알기 쉬운 지수를 사용하여 구현하였다.
 */
uint16_t gf16_inv(uint16_t a)
{
    return gf16_pow(a, 0xfffe);
}

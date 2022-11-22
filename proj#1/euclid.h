/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#ifndef _EUCLID_H_
#define _EUCLID_H_

#include <stdint.h>

int gcd(int a, int b);
int xgcd(int a, int b, int *x, int *y);
int mul_inv(int a, int m);
uint64_t umul_inv(uint64_t a, uint64_t m);
uint16_t gf16_mul(uint16_t a, uint16_t b);
uint16_t gf16_pow(uint16_t a, uint16_t b);
uint16_t gf16_inv(uint16_t a);

#endif

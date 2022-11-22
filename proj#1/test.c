/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#ifdef __linux__
#include <bsd/stdlib.h>
#elif __APPLE__
#include <stdlib.h>
#else
#include <stdlib.h>
#endif
#include "euclid.h"

/*
 * 함수가 올르게 동작하는지 검증하기 위한 메인 함수로 수정해서는 안 된다.
 */
int main(void)
{
    int a, b, x, y, d, count;
    uint64_t m, ai, a1, a2;

    /*
     * 기본 gcd 시험
     */
    printf("========== 기본 gcd 시험 ==========\n");
    a = 28; b = 0;
    printf("gcd(%d,%d) = %d\n", a, b, gcd(a,b));
    a = 0; b = 32;
    printf("gcd(%d,%d) = %d\n", a, b, gcd(a,b));
    a = 41370; b = 22386;
    printf("gcd(%d,%d) = %d\n", a, b, gcd(a,b));
    a = 22386; b = 41371;
    printf("gcd(%d,%d) = %d\n", a, b, gcd(a,b));

    /*
     * 기본 xgcd, mul_inv 시험
     */
    printf("========== 기본 xgcd, mul_inv 시험 ==========\n");
    a = 41370; b = 22386;
    d = xgcd(a, b, &x, &y);
    printf("%d = %d * %d + %d * %d\n", d, a, x, b, y);
    printf("%d^-1 mod %d = %d, %d^-1 mod %d = %d\n", a, b, mul_inv(a,b), b, a, mul_inv(b,a));
    a = 41371; b = 22386;
    d = xgcd(a, b, &x, &y);
    printf("%d = %d * %d + %d * %d\n", d, a, x, b, y);
    printf("%d^-1 mod %d = %d, %d^-1 mod %d = %d\n", a, b, mul_inv(a,b), b, a, mul_inv(b,a));

    /*
     * 난수 a와 b를 발생시켜 xgcd를 계산하고, 최대공약수가 1이면 역이 존재하므로
     * 여기서 얻은 a^-1 mod b와 b^-1 mod a를 mul_inv를 통해 확인한다.
     * 이 과정을 여러번 반복하여 올바른지 확인한다.
     */
    printf("========== 무작위 xgcd, mul_inv 시험 ==========\n");
    count = 0;
    do {
        arc4random_buf(&a, sizeof(int)); a &= 0x7fffffff;
        arc4random_buf(&b, sizeof(int)); b &= 0x7fffffff;
        d = xgcd(a, b, &x, &y);
        if (d == 1) {
            if (x < 0)
                x = x + b;
            else
                y = y + a;
            if (x != mul_inv(a, b) || y != mul_inv(b, a)) {
                printf("FAILED: a = %d, b = %d, x = %d, y = %d", a, b, x, y);
                return 1;
            }
        }
        if (++count % 0xffff == 0) {
            printf(".");
            fflush(stdout);
        }
    } while (count < 0xffffff);
    printf(".....PASSED\n");

    /*
     * GF(2^16)에서 기본 a*b 시험
     */
    printf("========== 기본 GF(2^16) a*b 시험 ==========\n");
    a = 3; b = 7;
    printf("%d * %d = %d\n", a, b, gf16_mul(a,b));
    a = 65535; b = 12345;
    printf("%d * %d = %d\n", a, b, gf16_mul(a,b));

    /*
     * GF(2^16)에서 a를 1부터 65535까지 a^-1를 구하고 a * a^-1 = 1인지 확인한다.
     */
    printf("========== 전체 GF(2^16) a*b 시험 ==========\n");
    for (a = 1; a < 65536; ++a) {
        b = gf16_inv(a);
        if (gf16_mul(a,b) != 1) {
            printf("FAILED: a = %d, b = %d\n", a, b);
            return 1;
        }
        else if (a % 0xff == 0) {
            printf(".");
            fflush(stdout);
        }
    }
    printf(".....PASSED\n");

    /*
     * 기본 umul_inv 시험
     */
    printf("========== 기본 umul_inv 시험 ==========\n");
    a = 5; m = 9223372036854775808ULL;
    ai = umul_inv(a, m);
    printf("a = %d, m = %"PRIu64", a^-1 mod m = %"PRIu64, a, m, ai);
    if (ai != 5534023222112865485ULL) {
        printf(".....FAILED\n");
        return 1;
    }
    else
        printf(".....PASSED\n");
    a = 17; m = 9223372036854775808ULL;
    ai = umul_inv(a, m);
    printf("a = %d, m = %"PRIu64", a^-1 mod m = %"PRIu64, a, m, ai);
    if (ai != 8138269444283625713ULL) {
        printf(".....FAILED\n");
        return 1;
    }
    else
        printf(".....PASSED\n");
    a = 85; m = 9223372036854775808ULL;
    ai = umul_inv(a, m);
    printf("a = %d, m = %"PRIu64", a^-1 mod m = %"PRIu64, a, m, ai);
    if (ai != 9006351518340545789ULL) {
        printf(".....FAILED\n");
        return 1;
    }
    else
        printf(".....PASSED\n");

    /*
     * 난수 m과 m보다 작은 a1을 선택한 후 ai = umul_inv(a1, m)을 계산한다.
     * ai이 0이 아니면 역의 역, 즉 a2 = umul_inv(ai, m)가 a1과 일치하는지 검사한다.
     * 이 과정을 여러번 반복하여 올바른지 확인한다.
     */
    printf("========== 무작위 umul_inv 시험 ==========\n");
    count = 0;
    do {
        arc4random_buf(&a1, sizeof(uint64_t));
        arc4random_buf(&m, sizeof(uint64_t));
        a1 %= m;
        if ((ai = umul_inv(a1, m)) == 0)
            continue;
        a2 = umul_inv(ai, m);
        if (a1 != a2) {
            printf("FAILED: a1 = %"PRIu64", a2 = %"PRIu64", m = %"PRIu64"\n", a1, a2, m);
            return 1;
        }
        if (++count % 0xffff == 0) {
            printf(".");
            fflush(stdout);
        }
    } while (count < 0xffffff);
    printf(".....PASSED\n");

    return 0;
}

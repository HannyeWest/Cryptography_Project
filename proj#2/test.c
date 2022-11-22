/*
 * Copyright 2020-2022. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었다.
 */
#include <stdio.h>
#include <string.h>
#include <time.h>
#ifdef __linux__
#include <bsd/stdlib.h>
#elif __APPLE__
#include <stdlib.h>
#else
#include <stdlib.h>
#endif
#include "aes.h"

/*
 *  ================= 128 비트 AES 검증 데이터 =================
 *  <키>: 0f 15 71 c9 47 d9 e8 59 0c b7 ad d6 af 7f 67 98
 *  <라운드 키>:
 *  0f 15 71 c9 47 d9 e8 59 0c b7 ad d6 af 7f 67 98
 *  dc 90 37 b0 9b 49 df e9 97 fe 72 3f 38 81 15 a7
 *  d2 c9 6b b7 49 80 b4 5e de 7e c6 61 e6 ff d3 c6
 *  c0 af df 39 89 2f 6b 67 57 51 ad 06 b1 ae 7e c0
 *  2c 5c 65 f1 a5 73 0e 96 f2 22 a3 90 43 8c dd 50
 *  58 9d 36 eb fd ee 38 7d 0f cc 9b ed 4c 40 46 bd
 *  71 c7 4c c2 8c 29 74 bf 83 e5 ef 52 cf a5 a9 ef
 *  37 14 93 48 bb 3d e7 f7 38 d8 08 a5 f7 7d a1 4a
 *  48 26 45 20 f3 1b a2 d7 cb c3 aa 72 3c be 0b 38
 *  fd 0d 42 cb 0e 16 e0 1c c5 d5 4a 6e f9 6b 41 56
 *  b4 8e f3 52 ba 98 13 4e 7f 4d 59 20 86 26 18 76
 *  <평문>: 01 23 45 67 89 ab cd ef fe dc ba 98 76 54 32 10
 *  <암호문>: ff 0b 84 4a 08 53 bf 7c 69 34 ab 43 64 14 8f b9
 */

/*
 * 128 비트 AES 검증용 벡터값
 */
uint8_t key[KEYLEN] = {0x0f,0x15,0x71,0xc9,0x47,0xd9,0xe8,0x59,0x0c,0xb7,0xad,0xd6,0xaf,0x7f,0x67,0x98};
uint32_t rkey[RNDKEYLEN] = {0xc971150f,0x59e8d947,0xd6adb70c,0x98677faf,0xb03790dc,0xe9df499b,0x3f72fe97,0xa7158138,0xb76bc9d2,0x5eb48049,0x61c67ede,0xc6d3ffe6,0x39dfafc0,0x676b2f89,0x6ad5157,0xc07eaeb1,0xf1655c2c,0x960e73a5,0x90a322f2,0x50dd8c43,0xeb369d58,0x7d38eefd,0xed9bcc0f,0xbd46404c,0xc24cc771,0xbf74298c,0x52efe583,0xefa9a5cf,0x48931437,0xf7e73dbb,0xa508d838,0x4aa17df7,0x20452648,0xd7a21bf3,0x72aac3cb,0x380bbe3c,0xcb420dfd,0x1ce0160e,0x6e4ad5c5,0x56416bf9,0x52f38eb4,0x4e1398ba,0x20594d7f,0x76182686};
uint8_t ptxt[BLOCKLEN] = {0x01,0x23,0x45,0x67,0x89,0xab,0xcd,0xef,0xfe,0xdc,0xba,0x98,0x76,0x54,0x32,0x10};
uint8_t ctxt[BLOCKLEN] = {0xff,0x0b,0x84,0x4a,0x08,0x53,0xbf,0x7c,0x69,0x34,0xab,0x43,0x64,0x14,0x8f,0xb9};

int main(void)
{
    uint32_t roundKey[RNDKEYLEN];
    uint8_t *p, buf[BLOCKLEN];
    int i, count;
    clock_t start, end;
    double cpu_time;

    /*
     * 라운드 키 생성 시험
     */
    printf("<키>\n");
    for (i = 0; i < KEYLEN; ++i)
        printf("%02x ", key[i]);
    printf("\n<라운드 키>\n");
    KeyExpansion(key, roundKey);
    for (i = 0; i < RNDKEYLEN; ++i) {
        p = (uint8_t *)(roundKey+i);
        printf("%02x %02x %02x %02x ", p[0], p[1], p[2], p[3]);
        if ((i+1)%4 == 0)
            printf("\n");
    }
    if (memcmp(roundKey, rkey, RNDKEYLEN*sizeof(uint16_t))) {
        printf(".....FAILED: 라운드 키 불일치\n");
        return 1;
    }
    /*
     * 암호문 생성 시험
     */
    printf("---\n<평문>\n");
    for (i = 0; i < BLOCKLEN; ++i)
        printf("%02x ", ptxt[i]);
    memcpy(buf, ptxt, BLOCKLEN);
    Cipher(buf, roundKey, ENCRYPT);
    printf("\n<암호문>\n");
    for (i = 0; i < BLOCKLEN; ++i)
        printf("%02x ", buf[i]);
    if (memcmp(buf, ctxt, BLOCKLEN)) {
        printf(".....FAILED: 암호문 불일치\n");
        return 1;
    }
    /*
     * 복호문 생성 시험
     */
    Cipher(buf, roundKey, DECRYPT);
    printf("\n<복호문>\n");
    for (i = 0; i < BLOCKLEN; ++i)
        printf("%02x ", buf[i]);
    if (memcmp(buf, ptxt, BLOCKLEN)) {
        printf(".....FAILED: 복호문 불일치\n");
        return 1;
    }
    /*
     * 역암호문 생성 및 복호화 시험
     */
    Cipher(buf, roundKey, DECRYPT);
    printf("\n<역암호문>\n");
    for (i = 0; i < BLOCKLEN; ++i)
        printf("%02x ", buf[i]);
    Cipher(buf, roundKey, ENCRYPT);
    printf("\n<복호문>\n");
    for (i = 0; i < BLOCKLEN; ++i)
        printf("%02x ", buf[i]);
    printf(".....PASSED\n");
    /*
     * 키와 평문을 무작위로 선택해서 암복호화를 여러번 수행하고 CUP 시간을 측정한다.
     */
    printf("---\nAES 성능시험"); fflush(stdout);
    start = clock();
    count = 0;
    do {
        arc4random_buf(key, KEYLEN);
        KeyExpansion(key, roundKey);
        arc4random_buf(ptxt, BLOCKLEN);
        memcpy(buf, ptxt, BLOCKLEN);
        for (i = 0; i < 0x0ff; ++i)
            Cipher(buf, roundKey, ENCRYPT);
        for (i = 0; i < 0x1fe; ++i)
            Cipher(buf, roundKey, DECRYPT);
        for (i = 0; i < 0x0ff; ++i)
            Cipher(buf, roundKey, ENCRYPT);
        if (memcmp(buf, ptxt, BLOCKLEN)) {
            printf(".....FAILED: 복호문 불일치\n");
            return 1;
        }
        if (++count % 0xff == 0) {
            printf(".");
            fflush(stdout);
        }
    } while (count < 0xfff);
    end = clock();
    cpu_time = ((double)(end - start)) / CLOCKS_PER_SEC;
    printf(".....PASSED\nCPU 사용시간 = %.4f초\n", cpu_time);

    return 0;
}

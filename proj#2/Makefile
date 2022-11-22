#
# Copyright 2020-2022. Heekuck Oh, all rights reserved
# 이 파일은 한양대학교 ERICA 소프트웨어학부 재학생을 위해 만들었다.
#
CC = gcc
CFLAGS = -Wall -O3
CLIBS =
#
OS := $(shell uname -s)
ifeq ($(OS), Linux)
	CLIBS += -lbsd
endif
ifeq ($(OS), Darwin)
#    CLIBS +=
endif
#
all: test.o aes.o
	$(CC) -o test test.o aes.o $(CLIBS)

test.o: test.c aes.h
	$(CC) $(CFLAGS) -c test.c

aes.o: aes.c aes.h
	$(CC) $(CFLAGS) -c aes.c

clean:
	rm -rf *.o
	rm -rf test

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
all: test.o euclid.o
	$(CC) -o test test.o euclid.o $(CLIBS)

test.o: test.c euclid.h
	$(CC) $(CFLAGS) -c test.c

euclid.o: euclid.c euclid.h
	$(CC) $(CFLAGS) -c euclid.c

clean:
	rm -rf *.o
	rm -rf test

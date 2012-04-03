
# C scaffolding for hdfa.
# Just for testing.
# peteg42 at gmail dot com, April 2010.

CFLAGS += -Wall -pedantic -std=c99 -O2
CFLAGS += -ggdb

all: dfa-driver

bitsets.o: bitsets.c bitsets.h

dfa.o: dfa.c dfa.h bitsets.h qsort.h

dfa-driver.o: dfa-driver.c dfa.h

dfa-driver: dfa-driver.o bitsets.o dfa.o qsort.o

qsort.o: qsort.c qsort.h

clean:
	rm -f dfa-driver *.o

# tests: test
# 	./test Tests/graphs/*

# C scaffolding for hdfa.
# Just for testing.
# peteg42 at gmail dot com, April 2010.

CFLAGS += -Wall -pedantic -std=c99 -O2
CFLAGS += -ggdb

all: test

bitsets.o: bitsets.c bitsets.h

dfa.o: dfa.c dfa.h bitsets.h

test.o: test.c dfa.h

test: bitsets.o dfa.o test.o

clean:
	rm -f test *.o

tests: test
	./test Tests/graphs/*

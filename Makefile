CC = gcc
AR = ar

CFLAGS = -O3 -Wall -g -I .
LDFLAGS = -L. -lhungarian -lm

all: libhungarian.a hungarian_test 

hungarian_test: hungarian_test.c $(HUNGARIANLIB)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

libhungarian.a: hungarian.o
	$(AR) cr $@ hungarian.o

%.o: %.c %.h
	$(CC) $(CFLAGS) -c $<
clean:
	rm -f *.o *.a hungarian_test

CFLAGS += -Wall -Wextra -O2 -finline-functions
LDFLAGS += -lssl -lcrypto -lpthread

all: sand-leek

clean:
	rm -vf sand-leek

.PHONY: all clean


#!/bin/bash

TESTS="loadstore1 loadstore2 loadstore3"
FAILED="no"
FAILEDTESTS=""

for T in $TESTS; do
	echo -n "Running $T ... "
	python "$T.py" > "$T.tmp"
	if diff "$T.tmp" "$T.output"; then
		echo "OK"
	else
		FAILED="yes";
		FAILEDTESTS="$T $FAILEDTESTS"
		echo "$T FAILED!";
	fi
	rm "$T.tmp"
done

if [ ! -z "$FAILEDTESTS" ]; then
	echo "Tests failed: $FAILEDTESTS" 1>&2
fi
[ $FAILED = "no" ]

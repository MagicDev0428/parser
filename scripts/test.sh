#!/usr/bin/env bash
spesh=$1
for f in tests/*.t; do
	echo "$f"
	rm -f test.log
	$spesh "$f" -e >> test.log
	if [ $? != 0 ]; then
		echo "test failed, see test.log"
		tail -n5 test.log
		exit 1
	fi
done
echo "all tests passed."
rm -f test.log
exit 0

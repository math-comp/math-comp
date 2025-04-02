#! /bin/bash

# Parses the output of `rocq -time`
# Options:
# --hb : filters out non-hb commands |- mutually exclusive, the last one 
# --no-hb : filtours out hb commands |  encountered takes precedence
# --import : filters out non import commands |- mutually exclusive, the last one
# --no-import : filters out import commands  |  encountered takes precedence
# --diff : takes two performance files and compares them
#
# Output:
# - without --diff: the total time on the first line and the list of times for
#   each command sorted in decreasing order on the second line
# - with --diff: the total compilation time of file1 (resp. file2) on line 1
#   (resp. 2), their difference (file1-file2) on line 3 and the list, for each
#   command, of the difference of the compilation time of file1 and of file2 on
#   this command, sorted in decreasing order

HB=0
IMPORT=0
DIFF=0

TEMP=$(mktemp)
TEMP2=$(mktemp)

while [ True ]; do
	if [ "$1" = "--hb" ]; then
		HB=1
		shift 1
	elif [ "$1" = "--no-hb" ]; then
		HB=2
		shift 1
	elif [ "$1" = "--import" ]; then
		IMPORT=1
		shift 1
	elif [ "$1" = "--no-import" ]; then
		IMPORT=2
		shift 1
	elif [ "$1" = "--diff" ]; then
		DIFF=1
		shift 1
	else
		break
	fi
done

filter () {
	cat $1 | nl -s ' ' | grep secs > TEMP2

	if [ "$HB" = "0" ]; then
		cat TEMP2 > TEMP
	elif [ "$HB" = "1" ]; then
		cat TEMP2 | grep -e 'HB' -e 'type=' > TEMP
	elif [ "$HB" = "2" ]; then
		cat TEMP2 | sed -E '/HB|type=/d'  > TEMP
	else
		echo "Internal error 1"
	fi

	if [ "$IMPORT" = "0" ]; then
		cat TEMP > TEMP2
	elif [ "$IMPORT" = "1" ]; then
		cat TEMP | grep -e 'Import' -e 'Export' > TEMP2
	elif [ "$IMPORT" = "2" ]; then
		cat TEMP | sed -E '/Import|Export/d'  > TEMP2
	else
		echo "Internal error 1"
	fi

	cat TEMP2 | sed 's/^ *\([0-9]*\).* \([0-9]*\)\.\([0-9]*\) secs.*$/\1 \2.\3000/' > TEMP
}

if [ "$DIFF" = "0" ]; then
	filter $1
	cat TEMP | sed 's/^\([0-9]*\) \([0-9]*\)\.\(...\).*$/\1\
\2\3/' | python3 -c "import sys;
data=list(map(int, sys.stdin));
times=[(data[i+1], data[i]) for i in range(0, len(data), 2)];
times.sort();
times.reverse();
print(sum([i for i, _ in times]));
print(times)"
else
  TEMP3=$(mktemp)

	filter $2
	mv TEMP TEMP3
	filter $1

	paste TEMP TEMP3 | sed 's/^ *\([0-9]*\) \([0-9]*\).\(...\)[0-9]*\t[0-9]* \([0-9]*\).\(...\).*$/\1\
\2\3\
\4\5/' |
python3 -c "import sys;
data=list(map(int, sys.stdin));
print(sum([data[i+1] for i in range(0, len(data), 3)]));
print(sum([data[i+2] for i in range(0, len(data), 3)]));
times=[(data[i+1]-data[i+2], data[i]) for i in range(0, len(data), 3)];
times.sort();
print(sum([i for i, _ in times]));
print(times)"

fi




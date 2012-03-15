[ $# == 1 ] || {
	echo "usage error" >&2
	exit 1
}

find . -name '*.go' | while read f; do
	grep $1 $f | while read line; do
		echo $(basename $f): $line
	done
done

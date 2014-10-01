go install norstrulde/lumgua || exit 1
cp go/bin/lumgua . || exit 1

make -s lispin server || exit 1

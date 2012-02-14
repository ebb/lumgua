bash refresh.bash >/dev/null || exit 1
./server >server.log 2>&1 & SERVERPID=$!
./lumgua lumgua | tee lumgua.log
kill $SERVERPID
wait

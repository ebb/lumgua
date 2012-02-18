bash refresh.bash || exit 1
./server >server.log 2>&1 & SERVERPID=$!
sleep 1 # XXX laziness
./lumgua lumgua 2>&1 | tee lumgua.log
kill $SERVERPID
wait

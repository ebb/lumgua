bash refresh.bash || exit 1
./server >server.log 2>&1 &
sleep 0.1 # XXX laziness
$GOPATH/bin/lumgua lumgua 2>&1 | tee lumgua.log
wait

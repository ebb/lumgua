rsync -a --delete gopath/* $HOME/support/gopath/src/norstrulde/lumgua
go install norstrulde/lumgua

make -s lispin server

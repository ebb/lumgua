include $(GOROOT)/src/Make.inc

server: server.$(O)
	$(LD) -o $@ $<

server.$(O): server.go
	$(GC) -o $@ $<

lispin: lispin.$(O)
	$(LD) -o $@ $<

lispin.$(O): lispin.go
	$(GC) -o $@ $<

lumgua: lumgua.$(O)
	$(LD) -o $@ $<

lumgua.$(O): lumgua.go
	$(GC) -o $@ $<

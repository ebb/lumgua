package main

import (
	"flag"
	"log"
	. "norstrulde/lumgua/loader"
)

var address *string = flag.String("a", ":8082", "address")

func main() {
	flag.Parse()
	for _, name := range flag.Args() {
		err := LoadSourceFile(*address, name)
		if err != nil {
			log.Fatalln(err)
		}
	}
}

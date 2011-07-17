package main

import (
	"bytes"
	"flag"
	"http"
	"log"
	"io/ioutil"
	"os"
)

var address *string = flag.String("a", ":8082", "address")

const url = "http://localhost:8082/eval"

func main() {
	flag.Parse()
	url := "http://" + *address + "/eval"
	text, err := ioutil.ReadAll(os.Stdin)
	if err != nil {
		log.Fatal("stdin fail: " + err.String())
	}
	response, err := http.Post(url, "text/plain", bytes.NewBuffer(text))
	if err != nil {
		log.Fatal("http post fail: " + err.String())
	}
	defer response.Body.Close()
	_, err = ioutil.ReadAll(response.Body)
	if err != nil {
		log.Fatal("http post fail: " + err.String())
	}
	if response.StatusCode == 200 {
		println("groovy!")
		return
	}
	println("hrm.. http status: \"" + response.Status + "\"")
}

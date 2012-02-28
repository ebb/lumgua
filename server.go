package main

import (
	"flag"
	"fmt"
	"net/http"
	"io"
	"io/ioutil"
	"os"
	"os/signal"
	"time"
)

var address *string = flag.String("a", ":8082", "address")
var evalChan chan []byte

func put(r *http.Request) {
	f, _ := os.Create("./" + r.URL.Path)
	io.Copy(f, r.Body)
}

func get(w http.ResponseWriter, r *http.Request) {
	f, _ := os.Open("./" + r.URL.Path)
	io.Copy(w, f)
}

func rootHandler(w http.ResponseWriter, r *http.Request) {
	switch r.Method {
	case "GET":
		get(w, r)
	case "PUT":
		put(r)
	}
}

func logHandler(_ http.ResponseWriter, r *http.Request) {
	if r.Method != "POST" {
		return
	}
	io.Copy(os.Stdout, r.Body)
}

func evalHandler(w http.ResponseWriter, r *http.Request) {
	switch r.Method {
	case "GET":
		w.Header().Set("Content-Type", "text/plain; charset=utf-8")
		timeoutChan := time.After(10 * 1000 * 1000 * 1000)
		select {
		case text := <-evalChan:
			_, err := w.Write(text)
			if err != nil {
				println(err.Error())
			}
		case <-timeoutChan:
		}
	case "POST":
		text, err := ioutil.ReadAll(r.Body)
		if err != nil {
			w.WriteHeader(http.StatusInternalServerError)
			return
		}
		evalChan <- text
	}
}

func signalHandler() {
	c := make(chan os.Signal, 1)
	signal.Notify(c, os.Interrupt)
	<-c
	fmt.Fprintln(os.Stderr, "Exiting due to interrupt signal.")
	os.Exit(0)
}

func init() {
	evalChan = make(chan []byte, 1)
}

func main() {
	flag.Parse()
	http.HandleFunc("/", rootHandler)
	http.HandleFunc("/log", logHandler)
	http.HandleFunc("/eval", evalHandler)
	println("Listening on", *address)
	go signalHandler()
	err := http.ListenAndServe(*address, nil)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
	}
}

all: fmt build run

deps:
	opam install dune reason ocaml-lsp-server

clean:
	dune clean 

fmt:
	refmt */*.re --in-place
	refmt */*.rei --in-place
	
build:
	dune build bin/main.exe

run: 
	_build/default/bin/main.exe
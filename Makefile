all: fmt build

fmt:
	refmt */*.re --in-place
	refmt */*.rei --in-place
	
build:
	dune build bin/main.exe

clean:
	dune clean 

deps:
	opam install dune reason incr_dom ocaml-lsp-server

run: 
	_build/default/bin/main.exe
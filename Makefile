all: ocaml sml

ocaml: bench.ml integration.ml generic_search.ml queens.ml
	 ocamlopt unix.cmxa bench.ml generic_search.ml queens.ml -o queens
	ocamlopt -I "$(shell ocamlfind query zarith)" unix.cmxa zarith.cmxa bench.ml integration.ml -o integration

sml: queens.cm integration.cm xor.cm
	ml-build queens.cm
	ml-build integration.cm
	ml-build xor.cm

clean:
	rm -f *.o *.cmi *.cmx
	rm -f *.x86-linux
	rm -f queens integration

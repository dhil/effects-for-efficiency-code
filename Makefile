all: sml

sml: queens.cm integration.cm
	ml-build queens.cm
	ml-build integration.cm

clean:
	rm -f *.o *.cmi *.cmx
	rm -f *.x86-linux
	rm -f queens integration

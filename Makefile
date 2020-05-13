all: sml

smlnj: platform_smlnj.sml queens.cm integration.cm
	cp platform_smlnj.sml platform.sml
	ml-build queens.cm
	ml-build integration.cm

clean:
	rm -f *.o *.cmi *.cmx
	rm -f *.x86-linux
	rm -f queens integration

all: sml

smlnj: platform_smlnj.sml queens.cm integration.cm
	cp platform_smlnj.sml platform.sml
	ml-build queens.cm
	ml-build integration.cm

mlton: platform_mlton.sml queens.mlb integration.mlb
	mlton queens.mlb
	mlton integration.mlb

clean:
	rm -f *.o *.cmi *.cmx
	rm -f *.x86-linux
	rm -f queens integration

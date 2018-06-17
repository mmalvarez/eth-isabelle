ALL: llllc

llllc : FourL.ml
	ocamlc -o llllc unix.cma nums.cma FourL.ml ../FourLShim.ml

clean :
	rm llllc

cleanGenerated :
	rm FourL.ml

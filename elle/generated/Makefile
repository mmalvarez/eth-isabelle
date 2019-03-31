ALL: llllc

llllc : FourL.ml
	ocamlc -o llllc unix.cma nums.cma FourL.ml ../FourLShim.ml

llllc_opt: FourL.ml
	ocamlopt -o llllc_opt unix.cmxa nums.cmxa FourL.ml ../FourLShim.ml

clean :
	rm llllc llllc_opt

cleanGenerated :
	rm FourL.ml

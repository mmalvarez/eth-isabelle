(* from RosettaCode *)
let load_file f =
	let ic = open_in f in
	let n = in_channel_length ic in
	let s = String.create n in
	really_input ic s 0 n;
	close_in ic;
	(s);;

(* first argv argument is the file name.
TODO: handle parsing of options later, probably in Isabelle *)
let main =
	if Array.length Sys.argv > 1 then
		let content = load_file (Sys.argv. (1)) in
	        let out = FourL.FourL.compiler content in
	        (match out with
	         None -> prerr_endline "ERROR: compilation error"
	         | Some outs -> print_endline outs
                )
	else prerr_endline "ERROR: no filename specified";;

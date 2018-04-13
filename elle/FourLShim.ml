open FourL;;

let rec isaNumToOcamlNum n =
match n with
One -> 1
| Bit0 n' -> 2 * isaNumToOcamlNum n'
| Bit1 n' -> 2 * isaNumToOcamlNum n' + 1

let isaCharToOcamlChar c =
match c with
Zero_char -> Char.chr 0
| Char n -> Char.chr (isaNumToOcamlNum n)

let isaStrToOcamlCharList s = List.map isaCharToOcamlChar s

(* from stackoverflow *)
let ocamlCharListToOcamlStr cl = String.concat "" (List.map (String.make 1) cl)

let isaStrToOcamlStr s = isaStrToOcamlCharList (ocamlCharListToOcamlStr s)

(* from stackoverflow *)
let ocamlStrToOcamlCharList s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let rec ocamlNumToIsaNum n =
if n = 0 || n = 1 then One (* n = 0 should not happen *)
else if n % 2 = 0 then Bit0 (ocamlNumToIsaNum (n/2))
else Bit1 (ocamlNumToIsaNum ((n - 1)/2))

let ocamlCharToIsaChar n =
    match (Char.code n) with
    0 -> Zero_char
    | _ -> Char (ocamlNumToIsaNum n)

let ocamlCharListToIsaCharList s = List.map ocamlCharToIsaChar s

let ocamlStrToIsaCharList s =
  ocamlCharListToIsaCharList (ocamlStrToOcamlCharList s)

(* remaining to do - argument parsing*)

let main =
  match (compiler (explode "()")) with
    None -> print_string "nope\n"
   | Some s -> print_string "yep\n"

(* Idea: we want to *)

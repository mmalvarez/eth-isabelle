theory FourLExtract
  imports Main ElleSyntax ElleCompiler FourL ElleUtils String "~~/src/HOL/Library/Code_Char"
begin

definition compilerFuel where "compilerFuel = 100"

value "hexwrite [Evm.byteFromNat 125]"

(*
definition compiler_string :: "string \<Rightarrow> string option" where
"compiler_string s =
  (case llll_parse_complete s of
   None \<Rightarrow> None
  | Some l4 \<Rightarrow>
   ( case pipeline (llll_compile l4) compilerFuel of
      None \<Rightarrow> None
      | Some wl \<Rightarrow> Some (hexwrite wl)
   ))"
*)
definition compiler :: "String.literal \<Rightarrow> String.literal option" where
"compiler l =
  (case fourL_compiler_string (String.literal.explode l) of
   None \<Rightarrow> None
  | Some s \<Rightarrow> Some (String.implode s))"

export_code String.literal.explode

(*declare equal_literal_def [code del]*)
value "String.implode ''a''"

value "compiler (String.implode ''a'')"
(*
export_code  compiler in SML
module_name FourL file "./generated/FourL.sml"
*)
(* need a "code-printing" tweak
- use OCaml strings, not char lists
- use OCaml ints, not strs *)

value "compiler (String.implode ''(seq 1 2)'')"



export_code compiler in OCaml
module_name FourL file "./generated/FourL.ml"
(*
export_code compiler in Haskell
module_name FourL file "./generated/"
*)

end
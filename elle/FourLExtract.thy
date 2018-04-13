theory FourLExtract
  imports Main ElleSyntax ElleCompiler FourL ElleUtils
begin

definition compilerFuel where "compilerFuel = 100"

value "hexwrite [Evm.byteFromNat 125]"

definition compiler :: "string \<Rightarrow> string option" where
"compiler s =
  (case llll_parse_complete s of
   None \<Rightarrow> None
  | Some l4 \<Rightarrow>
   ( case pipeline (llll_compile l4) compilerFuel of
      None \<Rightarrow> None
      | Some wl \<Rightarrow> Some (hexwrite wl)
   ))"

export_code compiler in SML
module_name FourL file "./generated/FourL.sml"

export_code compiler in OCaml
module_name FourL file "./generated/FourL.ml"


end
theory LLLL2
  
  imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm"
  
begin
  
  (* LLLL, mark 2 *)

(* don't mix up de Bruijn indices with sizes *)
  
type_synonym idx = int
  
datatype ll1 =
  L "inst"
  (* de-Bruijn style approach to local binders *)
  | LLab "idx"
  | LJmp "idx"
  | LJmpI "idx"
  (* sequencing nodes also serve as local binders *)
  | LSeq "ll1 list"
    
datatype ll2 =
  L "int * inst * int"
  | LLab "int * idx * int"
  | LJmp "int * idx * int"
  | LJmpI "int * idx * int"
  | LSeq "int * (int * ll2 * int) list * int"

(* first pass, storing sizes *)
fun ll_phase1 :: "ll1 \<Rightarrow> int \<Rightarrow> (ll2 * int)" and
    ll_phase1_seq :: "ll1 list \<Rightarrow> int \<Rightarrow> (int * ll2 * int) list"
  where
  "ll_phase1 (ll1.L inst) i = (ll2.L (i, inst, i + size_inst inst), i + size_inst inst)"
| "ll_phase1 (ll1.LLab idx) i = (ll2.LLab (i, idx, i), i)" (* labels take no room *)
| "ll_phase1 (ll1.LJmp idx) i = (ll2.LJmp (i, idx, i + 4), i + 4)" (* jumps take at least 4 bytes *)
| "ll_phase1 (ll1.LJmpI idx) i = (ll2.LJmpI (i, idx, i + 4), i + 4)"
| "ll_phase1 (ll1.LSeq ls i) =
   (let (ls', i') = ll_phase1_seq ls' i in
   ll2.LSeq i ls' i')"
  
datatype ll3 =
  L "int * inst * int"
  | LLab "int * path3 * int"
  | LJmp "int * idx * int"
  | LJmpI "int * idx * int"
  | LSeq "int * (int * ll3 * int) list * int"
and path3 =
  Top (* needs an int argument ? *)
  | Node "int * (int * ll3 * int)list * int * path3 * (int * ll3 * int) list * int"
  
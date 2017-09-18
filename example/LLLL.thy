theory LLLL
  
  imports Main "../ContractSem" "../RelationalSem" "../ProgramInAvl" "../Hoare/Hoare" "../lem/Evm"
  
begin
  
datatype llexp1 =
    L "inst"
    | LSeq "llexp1" "llexp1"
    (* tag on if marks what number the jump dests are *)
    | LIf "llexp1" "llexp1" (* branch on top stack element *)

(* Q: have an optional tag on "if"
   to mark which number occurrence the dests are
*)
      
datatype llexp2 =
  L2 "inst"
  | L2Seq "llexp2" "llexp2"
  | L2If "llexp2" "llexp2" "int" (* int marks order, for resolving dests *)

datatype llexp_jumpTag =
  LJIf
  | LJMerge
    
datatype llexp3 =
  L3 "inst"
  | L3Seq "llexp3" "llexp3"
  | L3Jump "int" "llexp_jumpTag"
  | L3JumpI "int" "llexp_jumpTag"
  | L3JumpDest "int" "llexp_jumpTag"
    
datatype llexp4 =
  L4 "inst"
  | L4Jump "int" "llexp_jumpTag"
  | L4JumpI "int" "llexp_jumpTag"
  | L4JumpDest "int" "llexp_jumpTag"
    
(* translate the expression without resolving jumps
   second component of result is the listing of jump locations
   in order
 *)
(* fun ll_pass1 :: "llexp1 \<Rightarrow> llexp2" *)
(* the int serves to distinguish different joint points later *)
fun ll_pass1_rec :: "llexp1 \<Rightarrow> int \<Rightarrow> (llexp2 * int)" where
  "ll_pass1_rec (L e) i =
   (L2 e, i)"
| "ll_pass1_rec (LSeq c1 c2) i =
  
  (let (c1', i') = ll_pass1_rec c1 i in
   let (c2', i'') = ll_pass1_rec c2 i' in
   (L2Seq c1' c2', i''))"
| "ll_pass1_rec (LIf c1 c2) i =
  (let (c1', i') = ll_pass1_rec c1 i in
   let (c2', i'') = ll_pass1_rec c2 i' in
   (L2If c1' c2' i'', i'' + 1))"
  
definition ll_pass1 :: "llexp1 \<Rightarrow> llexp2" where
  "ll_pass1 e =
   (let (e', _) = ll_pass1_rec e 0 in
    e')"
  
(* fun ll_pass2 :: llexp2 \<Rightarrow> llexp3 *)
  
function ll_pass2_rec :: "llexp2 \<Rightarrow> llexp3" where
  "ll_pass2_rec (L2 e) = L3 e"
| "ll_pass2_rec (L2Seq e1 e2) = L3Seq (ll_pass2_rec e1) (ll_pass2_rec e2)"
| "ll_pass2_rec (L2If e1 e2 i) = 
   L3Seq (L3JumpI i LJIf)
   (L3Seq (ll_pass2_rec e2)
    (L3Seq (L3Jump i LJMerge)
     (L3Seq (L3JumpDest i LJIf)
      (L3Seq (ll_pass2_rec e1)
             (L3JumpDest i LJMerge)))))"
by pat_completeness auto

(* we need an auxiliary function to get the byte encoding *)
  
(* fun ll_pass3 :: llexp3 \<Rightarrow> llexp4 list *)
(* removes sequencing, could be more efficient *)
function ll_pass3_rec :: "llexp3 \<Rightarrow> llexp4 list" where
  "ll_pass3_rec (L3 e) = [L4 e]"
| "ll_pass3_rec (L3Seq e1 e2) = (ll_pass3_rec e1) @ (ll_pass3_rec e2)"
| "ll_pass3_rec (L3Jump i t) = [L4Jump i t]"
| "ll_pass3_rec (L3JumpI i t) = [L4JumpI i t]"
| "ll_pass3_rec (L3JumpDest i t) = [L4JumpDest i t]"
by pat_completeness auto
  
(* Final pass for resolving actual jump locations *) 
(* fun ll_pass4 :: llexp4 list \<Rightarrow> inst list *)

(* encoded size of instruction *)
definition inst_size :: "inst \<Rightarrow> int" where
  "inst_size c = length (inst_code c)"

(* Problem: size of jump instructions is undetermined *)
definition ll4_size :: "llexp4 \<Rightarrow> int" where
  "ll4_size (L4 e) = inst_size (e)"
| "ll4_size (L4Jump _ _) =
inst_size JUMPI" (* TODO add push *)
| "ll4_size (L4JumpI _ _) =
inst_size JUMP" (* TODO add push *)
| "ll4_size (L4JumpDest _ _) = inst_size JUMPDEST"
  
(* the int argument here is what number byte we are on *)
(* output is list of tuples (dest_num, tag, bytes) where that inst is located *)
function ll_pass4_rec1 :: "llexp4 list \<Rightarrow> int \<Rightarrow> (int, tag, int) list" where
  "ll_pass4_rec1 [] i = []"
  "ll_pass4_rec1 (h # t) i = 
   let i' = ll4_size h in

"
  "ll_pass4_rec1 (L3 e) i = 

  
(* pass 2: convert to numbered jumps*)
definition ll_pass2_rec2 :: "llexp2 \<Rightarrow> ? \<Rightarrow>"
  
(* pass 3: convert to insts with dummy jump locations*)
  
(* pass 4: convert to insts with real jump locations *)
let (c11, 11) = ll_pass1_rec c1 i in
  
"
(* Q: we need some state:
   [int]
   int - number of jump dest seen so far
 *)
fun compile_llexp :: "llexp \<Rightarrow> [int] \<Rightarrow> ([inst], [int])" where
  "compile_llexp (L )"
| "compile_llexp (L i) x = ([i], x)"
| "compile_llexp (LIf e1 e2) = 
"
| "compile_llexp (LSeq e1 e2) int0 =
  let (ins1, int1) = compile_llexp e1 x int0
  let (ins2, int2) = compile_llexp 
"
  
  
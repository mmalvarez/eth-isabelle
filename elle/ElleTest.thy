theory ElleTest
  imports Main String ElleCompiler (*"ElleCorrect/Valid4"*)
begin

(* This file is now all about trying to output code *)
(* In order to run this from a shell script we need a makefile *)
value "''ABC''"

definition test1 :: string where
"test1 = ''DEFG''"

value "test1"


(* tests copied from example/LLLL.thy *)
value "ll_pass1 (ll1.LSeq [ll1.LLab 0, ll1.L (Arith ADD)])"
value "(inst_size (Arith ADD))"

value "ll_get_node ((0,0), ((llt.LSeq () [((0,0),llt.LLab () 0), ((0,0),llt.LLab () 1)]))::ll2t) [1]"
value "ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])) :: ll3"

value "(ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value "ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [], ll1.LSeq [ll1.LLab 1]])))"

definition prog1 where
  "prog1 = ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.LLab 0])))"
value prog1

definition prog2 where
  "prog2 = ll3_assign_label (ll3_init (ll_pass1 (ll1.LSeq [ll1.L (Arith ADD), ll1.LLab 0])))"  
  
value "(case prog2 of
        Some (_, LSeq _ lsdec) \<Rightarrow> ll3_get_label lsdec [1]
        | _ \<Rightarrow> None)"

definition src3 where
"src3 = ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [ll1.LJmp 1], ll1.LSeq [ll1.LLab 1]]"

definition prog3 where
"prog3 = ll3_assign_label (ll3_init (ll_pass1 (
ll1.LSeq [ll1.LSeq [ll1.LLab 0], ll1.LSeq [ll1.LJmp 1], ll1.LSeq [ll1.LLab 1]])))"

value prog3

value "(case prog3 of
Some p' \<Rightarrow> Some (check_ll3 p')
| _ \<Rightarrow> None)"

value "(Evm.log256floor 2048) + 1"

value prog3

value "(case prog3 of
        Some l \<Rightarrow> ll3_resolve_jump_wrap l
        | _ \<Rightarrow> JFail [666])"

value "(case prog3 of
        Some (_, LSeq e lsdec) \<Rightarrow> ll3_get_label lsdec e
        | _ \<Rightarrow> None)"
  
value "(case prog3 of
        Some (_, LSeq _ lsdec) \<Rightarrow> Some (ll3_inc_jump lsdec 0 [1,0])
        | _ \<Rightarrow> None)"

value "Word.word_rsplit ((Word256.word256FromNat 0) :: 256 word) :: 8 word list" 

value "(case prog3 of
        Some l \<Rightarrow> process_jumps_loop 40 l
        | _ \<Rightarrow> None)"

value "(case prog3 of
        Some l \<Rightarrow> (case (process_jumps_loop 40 l) of
                       Some l \<Rightarrow> Some (ll4_init l)
                       | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)"


value "(case prog3 of
        Some l \<Rightarrow> (case (process_jumps_loop 40 l) of
                       Some l \<Rightarrow> write_jump_targets [] (ll4_init l)
                       | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)"
(* ll3_resolve_jumps :: "ll3 list \<Rightarrow> ll4 list"*)

value "Word.word_of_int 1 :: 1 word"
value "Evm.byteFromNat 255"

value "Divides.divmod_nat 255 256"

(* full compiler tests *)
value "pipeline' src3 20"

value "pipeline src3 20"

definition progif :: ll1 where
"progif =
ll1.LSeq [
ll1.LSeq [
ll1.L ( Stack (PUSH_N [0])),
ll1.LJmpI 0,
ll1.L (Stack (PUSH_N [1])),
ll1.LJmp 1,
ll1.LLab 0,
ll1.L (Stack (PUSH_N [2])),
ll1.LLab 1
]]
"

value "pipeline' progif 30"

(* check of validate_jump_targets
new question: is validate_jump_targets enough to prove everything we need?
if so, why were we so concerned about valid3?
*)
value "(case (pipeline' progif 30) of
         None \<Rightarrow> None
        | Some s \<Rightarrow> Some (ll4_validate_jump_targets [] s))"

value "pipeline progif 30"

definition ll1_sem_test1 where
"ll1_sem_test1 = silly_ll1_sem (ll1.LSeq [ll1.LLab 0, ll1.LJmpI 0])"
value "ll1_sem_test1 20 (Some 0)"
value "ll1_sem_test1 20 (Some 3)"

definition ll1_sem_test2 where
"ll1_sem_test2 = silly_ll1_sem
  (ll1.LSeq [
    ll1.LSeq [ ll1.LJmpI 0,
               ll1.L (Arith SUB),
               ll1.LJmp 1, 
               ll1.LLab 0,
               ll1.L (Arith ADD),
               ll1.LLab 1 ]])"

value "ll1_sem_test2 100 (Some 0)"
value "ll1_sem_test2 100 (Some 1)"
value "ll1_sem_test2 100 (Some 2)"

definition ll1_sem_test2' where
"ll1_sem_test2' = silly_ll1_sem
  (ll1.LSeq [ll1.LJmpI 0,
               ll1.L (Arith ADD),
               ll1.LLab 0]) "

value "ll1_sem_test2' 100 (Some 0)"
value "ll1_sem_test2' 100 (Some 27)"

(* TODO: is this really testing what we want? *)
definition ll1_sem_test3 where
"ll1_sem_test3  = silly_ll1_sem
(ll1.LSeq [ll1.LSeq [ll1.LJmpI 1,
                     ll1.LLab 0,
                     ll1.L (Arith SUB),
                     ll1.LJmpI 1,
                     ll1.LJmp 0, ll1.LLab 1]])"
value "ll1_sem_test3 120 (Some 4)"
value "ll1_sem_test3 120 (Some 0)"

(* NB *)
value "ll1_sem_test3 9 (Some 15)"
value "ll1_sem_test3 10 (Some 15)"

(* test to ensure things are being run in correct order,
as well as check correctness for sequences without labels *)
definition ll1_sem_test4 where
"ll1_sem_test4 = silly_ll1_sem
(ll1.LSeq [ll1.L (Arith SUB), ll1.L (Arith ADD)])"

value "ll1_sem_test4 10 (Some 0)"
value "ll1_sem_test4 10 (Some 1)"


(* ensure invalid jumps crash *)
definition ll1_sem_test5 where
"ll1_sem_test5 = silly_ll1_sem
(ll1.LSeq [ll1.LJmpI 0])"

value "ll1_sem_test5 10 (Some 1)"


(* semantics tests *)
value   "elle_sem' (ll1.L (Stack (PUSH_N ([byteFromNat 0]))))
10 (ellest_init 42)"

value  "elle_sem' (ll1.LSeq [ll1.L (Stack (PUSH_N ([byteFromNat 1]))),
                                   ll1.L (Stack (PUSH_N ([byteFromNat 1]))),
                                   ll1.L (Arith ADD)])
10 (ellest_init 42)"

value  "program_sem (\<lambda> _ . ()) (prog_init_cctx [Stack (PUSH_N [byteFromNat 0])]) 20 Metropolis
(InstructionContinue (elle_init_vctx 42))"

value "elle_run (ll1.LSeq [ll1.LLab 0, ll1.L (Stack (PUSH_N [byteFromNat 0]))]) 100"
value "elle_run (ll1.LSeq [ll1.LLab 0, ll1.L (Stack (PUSH_N [byteFromNat 1])), ll1.LJmpI 0]) 100"
value "elle_run (ll1.LSeq [ll1.LLab 0, ll1.L (Stack (PUSH_N [byteFromNat 0])) , ll1.LJmpI 0 ]) 100"

end

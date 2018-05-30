theory ElleSemantics 
  imports Main "ElleSyntax"
begin

(* alternate gather_labels implementation for our surface syntax *)
fun gather_ll1_labels :: "ll1 \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> childpath list" 
and gather_ll1_labels_list :: "ll1 list \<Rightarrow> childpath \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> childpath list" where
"gather_ll1_labels (ll1.L _) _ _ = []"
| "gather_ll1_labels (ll1.LJmp _) _ _ = []"
| "gather_ll1_labels (ll1.LJmpI _) _ _ = []"
| "gather_ll1_labels (ll1.LLab n) cp d = 
     (if n = d then [cp] else [])"
| "gather_ll1_labels (ll1.LSeq ls) cp d =
   gather_ll1_labels_list ls cp 0 (d+1)"
| "gather_ll1_labels_list [] _ _ _ = []"
| "gather_ll1_labels_list (h#t) cp ofs d =
   gather_ll1_labels h (cp@[ofs]) (d) @
   gather_ll1_labels_list t cp (ofs+1) d"


(* TODO: need to check resources in LJmp, LJmpI, Label case *)
(* TODO: need to subtract off gas in LJmp, LJmpI, Label case *)
(* this will require adding more parameters *)

(* do instd and jmpd really need to return an option? *)

(* idk exactly what these next comments are for - maybe unnecessary *)
(* subtract_gas (meter_gas (PC JumpI) v c net)
((new_memory_consumption inst(vctx_memory_usage   v) (vctx_stack_default(( 0 :: int)) v) (vctx_stack_default(( 1 :: int)) v) (vctx_stack_default(( 2 :: int)) v) (vctx_stack_default(( 3 :: int)) v) (vctx_stack_default(( 4 :: int)) v) (vctx_stack_default(( 5 :: int)) v) (vctx_stack_default(( 6 :: int)) v))) *)

(* llinterp is instD, jmpD, jmpiD, labD *)
type_synonym 'a llinterp =
"((inst \<Rightarrow> 'a \<Rightarrow> 'a) *
  ('a \<Rightarrow> 'a) *
  ('a \<Rightarrow> (bool * 'a)) *
  ('a \<Rightarrow> 'a))
"

datatype 'a llresult =
  LRFail
  | LRNext 'a
  | LRJump 'a nat


(* need to deduct LRJump returned results?
*)

(* *)
fun ll1_sem :: 
  "ll1 \<Rightarrow>
   'a llinterp \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
   'a \<Rightarrow> 'a llresult" 
and ll1_list_sem ::
 "ll1 list \<Rightarrow>
   'a llinterp \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   'a \<Rightarrow> 'a llresult" 
where

(* list_sem cases *)

(* non seeking, nil means noop *)
 "ll1_list_sem [] intp n None x = LRNext x"
(* when seeking, nil means we failed to find something we should have *)
| "ll1_list_sem [] intp n (Some _) x = LRFail"

| "ll1_list_sem (h#t) intp n None x =
   (if n = 0 then LRFail
    else (case ll1_sem h intp (n - 1) None x of
          LRFail \<Rightarrow> LRFail
         | LRNext x' \<Rightarrow> ll1_list_sem t intp (n - 1) None x'
         | LRJump x' d \<Rightarrow> LRJump x' d))"

| "ll1_list_sem (h#t) intp n (Some d) x =
   (if n = 0 then LRFail else
   (case gather_ll1_labels h [] d of
    [] \<Rightarrow> ll1_list_sem t intp (n - 1) (Some d) x
    | _ \<Rightarrow> (case ll1_sem h intp (n - 1) (Some (Suc d)) x of
            LRFail \<Rightarrow> LRFail
            | LRNext x' \<Rightarrow> ll1_list_sem t intp (n - 1) None x'
            | LRJump x' d \<Rightarrow> LRJump x' d)))"


(* first, deal with scanning cases *)
(* TODO we should include semantics of the label itself
however this only changed the PC, we don't care about that *)

(* NB we only call ourselves in "seek" mode on a label when we are sure of finding a label *)
| "ll1_sem (ll1.LLab d) (instD, jmpD, jmpiD, labD) n (Some d') x = 
   (if d + 1 = d' then LRNext (labD x) else LRFail)"



| "ll1_sem (ll1.LSeq ls) intp n (Some d) x =
   (if n = 0 then LRFail
    else 
    (case ll1_list_sem ls intp (n - 1) (Some d) x of
          LRFail \<Rightarrow> LRFail
         | LRNext x' \<Rightarrow> LRNext x'
         | LRJump x' 0 \<Rightarrow> ll1_sem (ll1.LSeq ls) intp (n - 1) (Some 0) x'
         | LRJump x' n \<Rightarrow> LRJump x' (n - 1)))"

(*
| "ll1_sem (ll1.LSeq ls) intp n (Some d) scopes cont =
   (if n = 0 then LRFail
    else 
    ll1_list_sem ls intp (n - 1) (Some d)
       ((ll1_sem (ll1.LSeq ls) intp (n - 1) (Some 0) scopes cont)#scopes)
       cont)"
*)
(* for anything else, seeking is a no op *)
| "ll1_sem _ intp n (Some d) x = LRNext x"

(* "normal" (non-"scanning") cases *)
| "ll1_sem (ll1.L i) (instD, jmpD, jmpiD, labD) n None x =
   LRNext (instD i x)"
| "ll1_sem (ll1.LLab d) (instD, jmpD, jmpiD, labD) n None x = 
    LRNext (labD x)"
| "ll1_sem (ll1.LJmp d) (instD, jmpD, jmpiD, labD) n None x = 
    LRJump (jmpD x) d"
| "ll1_sem (ll1.LJmpI d) (instD, jmpD, jmpiD, labD) n None x =
(case (jmpiD x) of
        (True, s') \<Rightarrow> LRJump s' d
        | (False, s') \<Rightarrow> LRNext s')"

| "ll1_sem (ll1.LSeq ls) intp n None x =
   (if n = 0 then LRFail
    else
     (case ll1_list_sem ls intp (n - 1) None x of
           LRFail \<Rightarrow> LRFail
         | LRNext x' \<Rightarrow> LRNext x'
         | LRJump x' 0 \<Rightarrow> ll1_sem (ll1.LSeq ls) intp (n - 1) (Some 0) x'
         | LRJump x' n \<Rightarrow> LRJump x' (n - 1)))"




(* a sample instantiation of the parameters for our semantics *)
(* state is a single nat, ll1.L increments
except for SUB, which subtracts *)

fun silly_denote :: "inst \<Rightarrow> nat option \<Rightarrow> nat option" where
"silly_denote _ None = None"
| "silly_denote (Arith SUB) (Some 0) = None"
|"silly_denote (Arith SUB) (Some (Suc n)) = Some n"
|"silly_denote _ (Some n) = Some (Suc n)"

fun silly_jmpred :: "nat option \<Rightarrow> (bool * nat option)" where
"silly_jmpred None = (False, None)"
| "silly_jmpred (Some n) = (n \<noteq> 0, Some n)"

definition silly_interp :: "nat option llinterp" where
"silly_interp =
  (silly_denote, id, silly_jmpred, id)"

fun silly_ll1_sem :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
(* continuations corresponding to enclosing scopes *)
   nat option \<Rightarrow> nat option llresult" where
"silly_ll1_sem x n = ll1_sem x silly_interp n None"

(* our real Elle semantics, using EVM *)
(* type_synonym ellest = "variable_ctx * constant_ctx * network" *)

(* change this to use InstructionResult *)
(* also, we are going to have to copy-paste part of
next_state when defining elle_denote
*)
type_synonym ellest = "instruction_result * constant_ctx * network"

fun getctx :: "instruction_result \<Rightarrow> variable_ctx" where
"getctx (InstructionContinue v) = v"
| "getctx (InstructionToEnvironment _ v _) = v"

fun irmap :: "(variable_ctx \<Rightarrow> variable_ctx) \<Rightarrow> instruction_result \<Rightarrow> instruction_result" where
"irmap f (InstructionContinue v) = InstructionContinue (f v)"
| "irmap f (InstructionToEnvironment a v e) = 
           (InstructionToEnvironment a (f v) e)"

(* need a function that unwraps instruction result *)

fun setpc :: "ellest \<Rightarrow> nat \<Rightarrow> ellest" where
"setpc (e, e2, e3) n =
  (irmap (\<lambda> v . v \<lparr> vctx_pc := (int n) \<rparr>) e
  , e2
  , e3)"

fun clearprog :: "ellest \<Rightarrow> ellest" where
"clearprog (e1, e, e3) =
  (e1
  , (e \<lparr> cctx_program := empty_program \<rparr>)
  , e3)"

fun setprog :: "ellest \<Rightarrow> program \<Rightarrow> ellest" where
"setprog (e1, e2, e3) p =
  (e1
  , (e2 \<lparr> cctx_program := p \<rparr> )
  , e3
  )"

fun erreq :: "ellest \<Rightarrow> ellest \<Rightarrow> bool" where
"erreq (InstructionToEnvironment (ContractFail _) _ _, e12, e13) 
       (InstructionToEnvironment (ContractFail _) _ _, e22, e23) =
        (e12 = e22 \<and> e13 = e23)"
| "erreq a b = (a = b)"

(* throw away program and pc *)
(* then, if we have an error, ignore everything *)
definition elleq :: "ellest \<Rightarrow> ellest \<Rightarrow> bool" where
"elleq a b = erreq (setpc (clearprog a) 0) 
                   (setpc (clearprog b) 0)"

(* TODO: check that instruction is allowed *)
(* TODO: actually deal with InstructionToEnvironment reasonably *)
(* part of this copied from next_state *)
fun elle_instD :: "inst \<Rightarrow> ellest \<Rightarrow> ellest" where
"elle_instD i (ir, cc, n) =
    (case ir of
      InstructionToEnvironment _ _ _ \<Rightarrow> (ir, cc, n)
    | InstructionContinue v \<Rightarrow>
        if check_resources v cc (vctx_stack   v) i n then
          (instruction_sem v cc i n, cc, n)
        else 
          (InstructionToEnvironment (ContractFail
               ((case  inst_stack_numbers i of
                  (consumed, produced) =>
                  (if (((int (List.length(vctx_stack   v)) + produced) - consumed) \<le>( 1024 :: int)) then [] else [TooLongStack])
                   @ (if meter_gas i v cc n \<le>(vctx_gas   v) then [] else [OutOfGas])
                )
               ))
               v None
          , cc
          , n))"

fun elle_labD :: "ellest \<Rightarrow> ellest" where
"elle_labD est = elle_instD (Pc JUMPDEST) est"

(* use pieces of check_resources here:
- for jump, we just need the "meter_gas" statement
- for jmpI, we also need to make sure there is an item
on the stack
*)
(*
better idea: somehow do the resource calculations for push and jump?
- simulate pushing the address
- check resources for jump/jumpi in simulated state

this will handle the resource checks

for resource (gas) subtraction, we can then just subtract
"meter_gas" for push plus "meter_gas" for jump
*)

(* FOR JUMP steps are as follows.
1. Check to make sure we have more than Gmid gas
   - return outOfGas if not
2. Check to make sure we have an extra stack slot
   (because the EVM code will need one)
    - return a Stack Overflow error if we don't have one
3. Subtract off Gmid gas
*)


(* off by one in checking for stack overflow?
actually i think this is ok. we need to check for "greater than or equal to 1024" *)
fun elle_jumpD :: "ellest \<Rightarrow> ellest" where
"elle_jumpD (ir, cc, n) =
    (case ir of
      InstructionToEnvironment _ _ _ \<Rightarrow> (ir, cc, n)
    | InstructionContinue v \<Rightarrow>
        if      (vctx_gas v) < Gmid then
          (InstructionToEnvironment (ContractFail [OutOfGas]) v None, cc, n)
        else if int (List.length(vctx_stack   v)) \<ge> (1024 :: int) then 
          (InstructionToEnvironment (ContractFail [TooLongStack]) v None, cc, n)
        else
          (InstructionContinue (v \<lparr> vctx_gas := (vctx_gas v - Gmid) \<rparr>), cc, n))"


(* FOR JUMPI steps are as follows
1. Check for Ghigh gas
    - return outOfGas if not
2. Make sure we have an extra stack slot, AND there is an element
   at the top of the stack (condition)
   - Return TooShortStack or StackOverflow as appropriate
3. Subtract off Ghigh gas, remove top item from stack,
return a Boolean based on whether the item is 0


*)


(*

semantics of jump in Elle:
1. check to make sure we have enough stack space to do a push
2. check to make sure we have enough gas for a push
3. check to make sure we have enough resources for jump, after subtracting push's gas
4. consume jump gas

*)

fun elle_jumpiD :: "ellest \<Rightarrow> (bool * ellest)" where
"elle_jumpiD (ir, cc, n) =
    (case ir of
      InstructionToEnvironment _ _ _ \<Rightarrow> (False, (ir, cc, n))
    | InstructionContinue v \<Rightarrow>
        if      (vctx_gas v) < Ghigh then
          (False, (InstructionToEnvironment (ContractFail [OutOfGas]) v None, cc, n))
        else if int (List.length(vctx_stack   v)) \<ge> (1024 :: int) then 
          (False, (InstructionToEnvironment (ContractFail [TooLongStack]) v None, cc, n))
        else (case vctx_stack v of
          [] \<Rightarrow> (False, (InstructionToEnvironment (ContractFail [TooShortStack]) v None, cc, n))
          | cond#rest \<Rightarrow>
           let new_env = (InstructionContinue (v \<lparr> vctx_stack := rest, vctx_gas := (vctx_gas v - Ghigh) \<rparr>)) in
            strict_if (cond =(((word_of_int 0) ::  256 word)))
             (\<lambda> _ . (True, (new_env, cc, n) ))
             (\<lambda> _  . (False, (new_env, cc, n)))))"



definition elle_interp :: "ellest llinterp" where
"elle_interp =
(elle_instD
,elle_jumpD
,elle_jumpiD
,elle_labD)
"

(* TODO need to unpack correctly *)
(* NB we make no update to keep the PC correct *)
(* TODO: do we account for gas here?  I think we just need to
subtract off verylow*)

(* here we need to
- unpack state
- check if it is InstructionToEnvironment - if so don't touch it
- 
*)
definition elle_init_block :: "block_info"
  where
"elle_init_block =\<lparr>
block_blockhash = (\<lambda> x . x),
  block_coinbase = w160_0,
  block_timestamp = w256_0,
  block_number = w256_0,
  block_difficulty = w256_0,
  block_gaslimit = w256_0 
\<rparr>"

definition elle_init_vctx :: "int \<Rightarrow> variable_ctx"
  where "elle_init_vctx gas_in = 
\<lparr> vctx_stack = ([]), (* The stack is initialized for every invocation *)
    vctx_memory = empty_memory, (* The memory is also initialized for every invocation *)
     vctx_memory_usage =(( 0 :: int)), (* The memory usage is initialized. *)
     vctx_storage = empty_storage, (* The storage is taken from the account state *)
     vctx_pc =(( 0 :: int)), (* The program counter is initialized to zero *)
     vctx_balance = (\<lambda> (addr::address) . 
                         w256_0 (* can we get away with this *)),
     vctx_caller = w160_0, (* the caller is specified by the environment *)
     vctx_value_sent = w256_0, (* the sent value is specified by the environment *)
     vctx_data_sent = [], (* the sent data is specified by the environment *)
     vctx_storage_at_call = empty_storage, (* the snapshot of the storage is remembered in case of failure *)
     vctx_balance_at_call = (\<lambda> (addr::address) . 
                         w256_0 (* can we get away with this *)), (* the snapshot of the balance is remembered in case of failure *)
     vctx_origin = w160_0, (* assume a 0 gas price *)
     vctx_ext_program = (\<lambda> _ . empty_program), (* external programs are empty. *)
     vctx_block = elle_init_block, (* bogus block. *)
     vctx_gas = gas_in, (* parameter. *)
     vctx_account_existence = (\<lambda> _ . False), (* existence is chosen arbitrarily *)
     vctx_touched_storage_index = ([]),
     vctx_logs = ([]),
     vctx_refund =(( 0 :: int)), (* the origin of the transaction is arbitrarily chosen *)
     vctx_gasprice = w256_0
   \<rparr>"

definition elle_init_cctx :: constant_ctx
  where
"elle_init_cctx =
\<lparr> cctx_program = empty_program,
  cctx_this = w160_0,
  cctx_hash_filter = (\<lambda> _ . False)
\<rparr>"


definition ellest_init :: "int \<Rightarrow> ellest" where
"ellest_init g = (InstructionContinue (elle_init_vctx g), elle_init_cctx, Metropolis)"

fun elle_sem' :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel for elle jumps *)
  (* continuations corresponding to enclosing scopes *)
   (ellest \<Rightarrow> ellest llresult)" where
"elle_sem' x n = ll1_sem x elle_interp n None"

(* denote jmpd *)

(* TODO: build an ll' sem, using purge_ll_annot *)
fun ll'_sem ::  "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow>
   'a llinterp \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   ('a \<Rightarrow> 'a llresult)" where
"ll'_sem x =
  ll1_sem (ll_purge_annot x)"

fun ll'_sem' ::
  "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow>
   nat \<Rightarrow> (* fuel for elle jumps *)
   (ellest \<Rightarrow> ellest llresult)" where
"ll'_sem' x n = ll'_sem x elle_interp n None"

(* prove that if two lls are equal, throwing away annotations,
the semantics are also the same
use ll'_sem *)
lemma ll'_sem_same' :
"(! t2 . ll_purge_annot (t1 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll) = ll_purge_annot t2 \<longrightarrow>
  (! n depth x . ll'_sem t1 n depth x = ll'_sem t2 n depth x))
\<and>
(! q e q2 e2 ls2 . ll_purge_annot (q, LSeq e (ls :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list)) = ll_purge_annot (q2, LSeq e2 ls2) \<longrightarrow>
   (! n depth x . ll'_sem (q, LSeq e ls) n depth x = ll'_sem (q2, LSeq e2 ls2) n depth x))"
proof(induction rule:my_ll_induct)
case (1 q e i)
  then show ?case by auto
next
case (2 q e idx)
  then show ?case by auto
next
  case (3 q e idx n)
  then show ?case by auto
next
  case (4 q e idx n)
  then show ?case by auto
next
  case (5 q e l)
  then show ?case by auto
next
  case 6
  then show ?case by auto
next
  case (7 h l)
  then show ?case by auto
qed

lemma ll'_sem_same [rule_format]:
"(! t2 . ll_purge_annot (t1 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll) = ll_purge_annot t2 \<longrightarrow>
  (!  n depth x . ll'_sem t1 n depth x = ll'_sem t2 n depth x))"
  apply(insert ll'_sem_same')
  apply(auto)
  done

(* we probably need another one of these lemmas for ll_list_sem'? *)

(* idea: now we need to prove that the two semantics we have for an ll4
1. ll'_sem
2. program_sem ("to_program" (write_bytes out))

To do this we need to first fix the gas issue around jumps
in the ll/ll' semantics
*)

end
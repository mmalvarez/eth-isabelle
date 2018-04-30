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


fun ll1_sem :: 
  "ll1 \<Rightarrow>
   (inst \<Rightarrow> 'a \<Rightarrow> 'a option) \<Rightarrow> (* inst interpretation *)
   ('a \<Rightarrow> (bool * 'a) option) \<Rightarrow> (* whether JmpI should execute or noop in any given state *)
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   (('a \<Rightarrow> 'a option) list) \<Rightarrow>
   ('a \<Rightarrow> 'a option) \<Rightarrow> (* continuation *)
   ('a \<Rightarrow> 'a option)" 
and ll1_list_sem ::
 "ll1 list \<Rightarrow>
   (inst \<Rightarrow> 'a \<Rightarrow> 'a option) \<Rightarrow> (* inst interpretation *)
   ('a \<Rightarrow> (bool * 'a) option) \<Rightarrow> (* whether JmpI should execute or noop in any given state *)
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   (('a \<Rightarrow> 'a option) list) \<Rightarrow>
   ('a \<Rightarrow> 'a option) \<Rightarrow> (* continuation *)
   ('a \<Rightarrow> 'a option)" 
where

(* list_sem cases *)

(* non seeking, nil means noop *)
 "ll1_list_sem [] denote jmpd n None scopes cont = cont"
(* when seeking, nil means we failed to find something we should have *)
| "ll1_list_sem [] denote jmpd n (Some _) scopes cont = (\<lambda> _ . None)"

| "ll1_list_sem (h#t) denote jmpd n None scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else ll1_sem h denote jmpd (n - 1) None scopes
    (ll1_list_sem t denote jmpd (n - 1) None scopes cont))"

| "ll1_list_sem (h#t) denote jmpd n (Some d) ctx cont =
   (if n = 0 then (\<lambda> _ . None) else
   (case gather_ll1_labels h [] d of
    [] \<Rightarrow> ll1_list_sem t denote jmpd (n - 1) (Some d) ctx cont
   | _ \<Rightarrow> ll1_sem h denote jmpd (n - 1) (Some (Suc d)) ctx (ll1_list_sem t denote jmpd (n - 1) None ctx cont)))"


(* first, deal with scanning cases *)
(* TODO we should include semantics of the label itself *)

(* NB we only call ourselves in "seek" mode on a label when we are sure of finding a label *)
| "ll1_sem (ll1.LLab d) _ _ n (Some d') _ cont = 
   (if d + 1 = d' then cont
    else (\<lambda> s . None ))"

| "ll1_sem (ll1.LSeq ls) denote jmpd n (Some d) scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else 
    ll1_list_sem ls denote jmpd (n - 1) (Some d)
       ((ll1_sem (ll1.LSeq ls) denote jmpd (n - 1) (Some 0) scopes cont)#scopes)
       cont)"

(* for anything else, seeking is a no op *)
| "ll1_sem _ _ _ n (Some d) _ cont = cont"

(* "normal" (non-"scanning") cases *)
| "ll1_sem (ll1.L i) denote _ n None scopes cont =
  (\<lambda> s . case denote i s of
           Some r \<Rightarrow> cont r
          | None \<Rightarrow> None)"
| "ll1_sem (ll1.LLab d) denote _ n None scopes cont = cont"
| "ll1_sem (ll1.LJmp d) denote _ n None scopes cont = scopes ! d"
| "ll1_sem (ll1.LJmpI d) denote jmpd n None scopes cont =
(\<lambda> s . case (jmpd s) of
        None \<Rightarrow> None
        | Some (True, s') \<Rightarrow> ((scopes ! d) s')
        | Some (False, s') \<Rightarrow> cont s')"

(* new idea for Seq case *)
| "ll1_sem (ll1.LSeq ls) denote jmpd n None scopes cont =
   (if n = 0 then (\<lambda> _ . None)
    else
     ll1_list_sem ls denote jmpd (n - 1) None
      (* this scope continuation was ll1_sem before *)
      ((ll1_sem (ll1.LSeq ls) denote jmpd (n - 1) (Some 0) scopes cont)#scopes) cont)"

(* a sample instantiation of the parameters for our semantics *)
(* state is a single nat, ll1.L increments
except for SUB, which subtracts *)

fun silly_denote :: "inst \<Rightarrow> nat \<Rightarrow> nat option" where
"silly_denote (Arith SUB) 0 = None"
|"silly_denote (Arith SUB) (Suc n) = Some n"
|"silly_denote _ n = Some (Suc n)"

fun silly_jmpred :: "nat \<Rightarrow> (bool * nat) option" where
"silly_jmpred n = (Some (n \<noteq> 0, n))"

fun silly_ll1_sem :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel *)
(* continuations corresponding to enclosing scopes *)
   (nat \<Rightarrow> nat option) \<Rightarrow> (* continuation *)
   (nat \<Rightarrow> nat option)" where
"silly_ll1_sem x n c = ll1_sem x silly_denote silly_jmpred n None [] c"

(* our real Elle semantics, using EVM *)
type_synonym ellest = "variable_ctx * constant_ctx * network"

(* TODO: check that instruction is allowed *)
(* TODO: actually deal with InstructionToEnvironment reasonably *)
fun elle_denote :: "inst \<Rightarrow> ellest \<Rightarrow> ellest option" where
"elle_denote i (vc, cc, n) =
 (case instruction_sem vc cc i n of
  InstructionContinue vc' \<Rightarrow>
    Some(vc', cc, n)
  | InstructionToEnvironment _ vc' _ \<Rightarrow>
    Some(vc', cc, n))"

(* TODO need to unpack correctly *)
(* NB we make no update to keep the PC correct *)
fun elle_jmpd :: "ellest \<Rightarrow> (bool * ellest) option" where
"elle_jmpd (v, c, n) =
 (case (vctx_stack v) of
   cond # rest \<Rightarrow>
    (let new_env = (( v (| vctx_stack := (rest) |))) in
    strict_if (cond =(((word_of_int 0) ::  256 word)))
           (\<lambda> _ . Some (True, (new_env, c, n) ))
           (\<lambda> _ .Some (False, (new_env, c, n))))
  | _ \<Rightarrow> None)"

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
"ellest_init g = (elle_init_vctx g, elle_init_cctx, Metropolis)"

fun elle_sem' :: 
  "ll1 \<Rightarrow>
   nat \<Rightarrow> (* fuel for elle jumps *)
  (* continuations corresponding to enclosing scopes *)
   (ellest \<Rightarrow> ellest option) \<Rightarrow> (* continuation *)
   (ellest \<Rightarrow> ellest option)" where
"elle_sem' x n c = ll1_sem x elle_denote elle_jmpd n None [] c"

(* denote jmpd *)

(* TODO: build an ll' sem, using purge_ll_annot *)
fun ll'_sem ::  "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow>
   (inst \<Rightarrow> 'a \<Rightarrow> 'a option) \<Rightarrow> (* inst interpretation *)
   ('a \<Rightarrow> (bool * 'a) option) \<Rightarrow> (* whether JmpI should execute or noop in any given state *)
   nat \<Rightarrow> (* fuel *)
   nat option \<Rightarrow> (* depth, if we are scanning for a label *)
(* continuations corresponding to enclosing scopes *)
   (('a \<Rightarrow> 'a option) list) \<Rightarrow>
   ('a \<Rightarrow> 'a option) \<Rightarrow> (* continuation *)
   ('a \<Rightarrow> 'a option)" where
"ll'_sem x =
  ll1_sem (ll_purge_annot x)"

fun ll'_sem' ::
  "('lix, 'llx, 'ljx, 'ljix, 'lsx, 'ptx, 'pnx) ll \<Rightarrow>
   nat \<Rightarrow> (* fuel for elle jumps *)
  (* continuations corresponding to enclosing scopes *)
   (ellest \<Rightarrow> ellest option) \<Rightarrow> (* continuation *)
   (ellest \<Rightarrow> ellest option)" where
"ll'_sem' x n c = ll'_sem x elle_denote elle_jmpd n None [] c"

(* prove that if two lls are equal, throwing away annotations,
the semantics are also the same
use ll'_sem *)
lemma ll'_sem_same' :
"(! t2 . ll_purge_annot (t1 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll) = ll_purge_annot t2 \<longrightarrow>
  (! d jd n depth s c . ll'_sem t1 d jd n depth s c = ll'_sem t2 d jd n depth s c))
\<and>
(! q e q2 e2 ls2 . ll_purge_annot (q, LSeq e (ls :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll list)) = ll_purge_annot (q2, LSeq e2 ls2) \<longrightarrow>
   (! d jd n depth s c . ll'_sem (q, LSeq e ls) d jd n depth s c = ll'_sem (q2, LSeq e2 ls2) d jd n depth s c))"
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

lemma ll'_sem_same :
"(! t2 . ll_purge_annot (t1 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g) ll) = ll_purge_annot t2 \<longrightarrow>
  (! d jd n depth s c . ll'_sem t1 d jd n depth s c = ll'_sem t2 d jd n depth s c))"
  apply(insert ll'_sem_same')
  apply(auto)
  done

end
theory FourL
  imports Main ElleSyntax ElleCompiler ElleUtils
begin

(* deal with literals:
- strings (truncate to 32 bytes, left align)
- integers
- expressions
*)

(* Do we need isZero at this level?
   I think we only need to reflect it in the output ll1 code *)
datatype llllarith =
   LAPlus
   | LAMinus
   | LATimes
   | LADiv
   | LAMod
   | LAAnd
   | LAOr
   | LAXor
   | LANot
   | LAExp

datatype lllllogic =
  LLAnd
  | LLOr
  | LLNot

datatype llllcompare =
  LCEq
  | LCNeq
  | LCLt
  | LCLe
  | LCGt
  | LCGe

datatype stree =
  STStr "string"
  | STStrs "stree list"

(* TODO: add macro definitions with arguments
   the arguments will get compiled and filled in *)
(* TODO: how to handle scoping macros?
def and mac as defined here need a recursive llll argument
*)
datatype llll =
   L4L_Str "string"
   | L4L_Nat "nat"
(* now we handle defs/macros before the llll stage (parsing) *)
(*   | L4Def "string" "string list" *)
(*   | L4Mac "string" "llll list"  *)
   | L4I0 "inst"
   | L4I1 "inst" "llll"
   | L4I2 "inst" "llll" "llll"
  | L4Seq "llll list"
  | L4Arith "llllarith" "llll list"
  | L4Logic "lllllogic" "llll list"
  | L4Comp "llllcompare" "llll" "llll" (* all comparisons must be binary *)
  | L4When "llll" "llll"
  | L4If "llll" "llll" "llll"
  | L4While "llll" "llll"

(* Read in a string as a word list (truncate to 32 bytes)*)
(* TODO: need to explicitly pad with zeros? *)
(* i think we might not need to, let's see *)
fun truncate_string_sub :: "string \<Rightarrow> nat \<Rightarrow> 8 word list"
  where
 "truncate_string_sub [] (n) = 
    (if n = 0 then [] else byteFromNat 0 # truncate_string_sub [] (n-1))"
| "truncate_string_sub (h#t) (n) =
    (if n = 0 then [] else byteFromNat (String.char.nat_of_char h) #
   truncate_string_sub t (n-1))"

definition truncate_string :: "string \<Rightarrow> 8 word list"
  where "truncate_string s = truncate_string_sub s 32"

(* ints need to be right aligned (lowest sig bit) *)
(* output_address, from ElleCompiler, should work *)
(* note that this effectively means that
PUSHes are little-endian?
but no, numbers _are_ big endian in EVM
*)
definition intToBytes :: "int \<Rightarrow> 8 word list" where
"intToBytes i = output_address (Int.nat i)"

value "intToBytes 2049"

(* TODO: do we need raw?
If so, how do we get it?
Raw means we need to basically save the first non-void result *)

(* TODO: is this the right ("jnz") semantics? *)
(* Idea: literals translate into pushes *)
fun llll_compile :: "llll \<Rightarrow> ll1"
(*and llll_arith_compile :: "llllarith \<Rightarrow> ll1" *) where
"llll_compile (L4L_Str s) = ll1.L (Evm.inst.Stack (PUSH_N (truncate_string s)))"
| "llll_compile (L4L_Nat i) = ll1.L (Evm.inst.Stack (PUSH_N (intToBytes (int i))))"
| "llll_compile (L4I0 i) = ll1.L i"
| "llll_compile (L4I1 i l) = ll1.LSeq (llll_compile l # [ll1.L i])"
| "llll_compile (L4I2 i l1 l2) = ll1.LSeq (llll_compile l2 # llll_compile l1 # [ll1.L i])"
| "llll_compile (L4Seq l) = ll1.LSeq (map llll_compile l)"
| "llll_compile (L4When c l) =
   ll1.LSeq [llll_compile c, ll1.L (Arith ISZERO), ll1.LJmpI 0, llll_compile l, ll1.LLab 0]" (* wrong logic *)
| "llll_compile (L4If c l1 l2) = 
   ll1.LSeq [ ll1.LSeq [llll_compile c, ll1.LJmpI 0, llll_compile l2, ll1.LJmp 1, ll1.LLab 0, llll_compile l1, ll1.LLab 1]]"
(* TODO: we can have a more efficient loop *)
| "llll_compile (L4While c l) = 
   ll1.LSeq [
   ll1.LSeq [
   ll1.LSeq [ll1.LLab 0,
             llll_compile c, ll1.LJmpI 1,
             ll1.LJmp 2,
             ll1.LLab 1,
             llll_compile l,
             ll1.LJmp 0,
             ll1.LLab 2]]]"
(* TODO: for addition e.g., handle multiple results properly *)
| "llll_compile (L4Arith LAPlus ls) = ll1.LSeq ((map llll_compile (rev ls)) @ [ll1.L (Arith ADD)])"
| "llll_compile (L4Arith LAExp ls) = ll1.LSeq ((map llll_compile (rev ls)) @ [ll1.L (Arith EXP)])"
| "llll_compile (L4Arith LADiv ls) = ll1.LSeq ((map llll_compile (rev ls)) @ [ll1.L (Arith DIV)])"
| "llll_compile (L4Comp LCEq l1 l2) = ll1.LSeq [(llll_compile l2), llll_compile l1, ll1.L (Arith inst_EQ)]"

(* whitespace characters: bytes 9-13, 32 *)
definition isWs :: "char \<Rightarrow> bool"
  where
"isWs = 
  List.member
  (map String.char_of_nat
    [9, 10, 11, 12, 13, 32])"
value "String.char_of_nat 10"

definition isNewline :: "char \<Rightarrow> bool"
  where "isNewline c = (c = String.char_of_nat 10)"

fun stree_append :: "stree \<Rightarrow> stree \<Rightarrow> stree" where
"stree_append (STStr x) _ = STStr x"
| "stree_append (STStrs xs) s = STStrs (xs @ [s])"

definition newline :: "char" where
"newline = String.char_of_nat 10"

(* TODO: support comments
idea: add an extra flag (" we are in a comment") when we see a ;
clear it when we see a newline *)
(* With thanks to Alex Sanchez-Stern *)
fun llll_parse' :: "string \<Rightarrow> string \<Rightarrow> stree list \<Rightarrow> bool \<Rightarrow> stree option" where
"llll_parse' [] _ _ _ = None"
(* TODO: ensure partial token handling works w/r/t comments *)
| "llll_parse' (h#t) token parsed isComment =
   (if isComment then
       (if h = newline then
           (if token \<noteq> [] then 
                  (case parsed of
                     [] \<Rightarrow> None
                     | ph#pt \<Rightarrow> llll_parse' t [] (stree_append ph (STStr token) #pt) False)
                  else llll_parse' t [] parsed False)
           else llll_parse' t token parsed isComment
           )

   else 
      (if h = CHR '';''  then llll_parse' t token parsed True
      else (if h = CHR ''(''
          then llll_parse' t token ((STStrs [])#parsed) False
        else (if h = CHR '')''
              then (case parsed of
                    [] \<Rightarrow> None
                    | ph#[] \<Rightarrow> if token \<noteq> [] then Some (stree_append ph (STStr token))
                                             else Some ph
                    | ph1#ph2#pt \<Rightarrow> if token \<noteq> [] then llll_parse' t [] (stree_append ph2 (stree_append ph1 (STStr token)) # pt) False
                                                  else llll_parse' t [] (stree_append ph2 ph1#pt) False)
        else (if isWs h
              then (if token \<noteq> [] then 
                    (case parsed of
                       [] \<Rightarrow> None
                       | ph#pt \<Rightarrow> llll_parse' t [] (stree_append ph (STStr token) #pt) False)
                    else llll_parse' t [] parsed False) 
        else llll_parse' t (token@[h]) parsed False)))))"

fun llll_parse0 :: "string \<Rightarrow> stree option" where
"llll_parse0 s = llll_parse' s [] [] False"

value "llll_parse0 '';;a b c
(+ 11 1)''"

value "llll_parse0 '';a b c (+ 11 1)''"

value "llll_parse0 ''(+ 11 (+ 1 1) (- 2 1))''"


value "llll_parse0 ''(+ (+ 1 1) 2)''"

(* Q: best way to deal with the fact that
conditionals might not result in a value? *)
(*
| "llll_compile (L4Until c l) =
   ll1.LSeq [
   ll1.LSeq [ ll1.LLab 0,
              llll_compile c, ll1.LJmpI 1,
              llll_compile l,
              ll1.LJmp 0,
              ll1.LLab 1]]
*)

(* Q: will returning strings make termination proving harder? *)

(*definition charParse :: "char \<Rightarrow> string \<Rightarrow> (string * llll option)" where
"charParse _ [] = "[], *)

(* next: need to be able to parse fourL *)
(* do we want continuations here somehow? *)
(* Val's idea: continuations for:
- same level of precedence
- next level of precedence
- top 

the problem is that this seems to break termination. *)
(*
fun fourLParse :: "string \<Rightarrow> string * llll option" where
"fourParse
*)
value "LemExtraDefs.char_to_digit (CHR ''A'')"

(*
type_synonym ('a, 'b) parser =
  "string \<Rightarrow>
    ('a \<Rightarrow> string \<Rightarrow> 'b) \<Rightarrow> (* success continuation, consumes *)
    (string \<Rightarrow> 'b) \<Rightarrow> (* failure continuation, doesn't consume *)
    (string \<Rightarrow> 'b) \<Rightarrow> (* captures recursive call to entire grammar parser (e.g. for parens) *)
    'b"
*)
(* does this stratification work? *)
(* the idea is that parser' bake in their own recursor
   and that wherever possible we should use parser2 *)

type_synonym ('a, 'b) parser' =
  "string \<Rightarrow>
   ('a \<Rightarrow> string \<Rightarrow> 'b) \<Rightarrow>
   (string \<Rightarrow> 'b) \<Rightarrow>
   'b"

(* this seems weird, in particular how to avoid
using this e.g. for chainParse *)
definition fail' :: "('a, 'b option) parser'" where
"fail' _ _ _ = None"

type_synonym ('a, 'b) parser =
"string \<Rightarrow>
    ('a \<Rightarrow> string \<Rightarrow> 'b) \<Rightarrow> (* success continuation, consumes *)
    (string \<Rightarrow> 'b) \<Rightarrow> (* failure continuation, doesn't consume *)
    ('a, 'b) parser' \<Rightarrow> (* captures recursive call to entire grammar parser (e.g. for parens) *)
    'b"

value "CHR ''b''"

definition hex_parse_table :: "(char * nat) list" where
"hex_parse_table =
  [(CHR ''0'', 0)
  ,(CHR ''1'', 1)
  ,(CHR ''2'', 2)
  ,(CHR ''3'', 3)
  ,(CHR ''4'', 4)
  ,(CHR ''5'', 5)
  ,(CHR ''6'', 6)
  ,(CHR ''7'', 7)
  ,(CHR ''8'', 8)
  ,(CHR ''9'', 9)
  ,(CHR ''A'', 10), (CHR ''a'', 10)
  ,(CHR ''B'', 11), (CHR ''b'', 11)
  ,(CHR ''C'', 12), (CHR ''c'', 12)
  ,(CHR ''D'', 13), (CHR ''d'', 13)
  ,(CHR ''E'', 14), (CHR ''e'', 14)
  ,(CHR ''F'', 15), (CHR ''f'', 15)
  ]"

(* basic hex utils *)
fun parseHexNumeral :: "(nat, 'a) parser" where
"parseHexNumeral [] s f r = f []"
| "parseHexNumeral (h#t) s f r =
   (case Map.map_of hex_parse_table h of
    None \<Rightarrow> f (h#t)
    | Some n \<Rightarrow> s n t)"
(* does the r parameter need to change? *)

fun parseNumeral :: "(nat, 'a) parser" where
"parseNumeral [] s f r = f []" (* at this point we have no string to operate on *)
| "parseNumeral (h#t) s f r =
   (if LemExtraDefs.is_digit_char h
    then s (LemExtraDefs.char_to_digit h) t
    else f (h#t))"

(* idea: now we need to parse an arbitrary series of numerals
(as in TRX, we are including tokenization)
our failure case will not consume the next item yet
*)

function(sequential) parseNatSub :: "nat \<Rightarrow> (nat, 'a) parser" where
"parseNatSub i [] su fa r  = su i []"
| "parseNatSub i (h#t) su fa r  =
   parseNumeral (h#t) 
                (\<lambda> n l . parseNatSub (10*i + n) l su fa r)
                (\<lambda> l . su i l) r
   "
  by pat_completeness auto
termination sorry

function(sequential) parseHexSub :: "nat \<Rightarrow> (nat, 'a) parser" where
"parseHexSub i [] su fa r = su i []"
| "parseHexSub i (h#t) su fa r =
   parseHexNumeral (h#t)
                   (\<lambda> n l . parseHexSub (16 * i + n) l su fa r)
                   (\<lambda> l . su i l) r"
  by pat_completeness auto
termination sorry

(*
function(sequential) parseIntSub :: "int \<Rightarrow> (int, 'a) parser" where
"parseIntSub i [] su fa r  = su i []"
| "parseIntSub i (h#t) su fa r  =
   parseNumeral (h#t) 
                (\<lambda> n l . parseIntSub (10*i + Int.int n) l su fa r)
                (\<lambda> l . su i l) r
   "
  by pat_completeness auto
termination sorry
*)
fun parseNat :: "(nat, 'a) parser" where
"parseNat [] su fa r = fa []"
| "parseNat (h#t) su fa r =
   parseNumeral (h#t) 
    (\<lambda> n l . parseNatSub n l su fa r)
    fa r"


(* more helpers: matching a keyword (literal string) *)
(* matching an empty keyword is technically valid *)
fun parseKeyword :: "string \<Rightarrow> (unit, 'a) parser" where
"parseKeyword [] l su fa r = su () l"
| "parseKeyword (h#t) [] su fa r = fa []"
| "parseKeyword (h#t) (h'#t') su fa r =
   (if h = h' then
       parseKeyword t t' su fa r
    else fa (h'#t'))"


fun parseHex :: "(nat, 'a) parser" where
"parseHex ((h0)#(hx)#h#t) su fa r =
  (if (h0 = CHR ''0'' \<and> hx = CHR ''x'') then
    (parseHexNumeral (h#t)
   (\<lambda> n l . parseHexSub n l su fa r)
    fa r)
  else fa (h0#hx#h#t))"
| "parseHex l su fa r = fa l"

(* execute a parser on a string *)
function(sequential) run_parse :: "('a, 'b) parser \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> string \<Rightarrow> 'b" where
"run_parse p done dfl s =
  p s (\<lambda> x s . done x) (\<lambda> s . dfl)
    (\<lambda> s su fa . run_parse p done dfl s)"
  by pat_completeness auto
termination sorry

definition run_parse' :: "('a, 'a) parser \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a" where
"run_parse' p dfl s = run_parse p id dfl s"


type_synonym 'a l4p' = "('a, llll option) parser"
type_synonym l4p = "llll option l4p'"

(* generalize to arbitrary option types? *)
(*
definition run_parse :: "l4p \<Rightarrow> string \<Rightarrow> llll option" where
"run_parse p s = run_parse' p None s"
*)

definition run_parse_opt :: "('a , 'b option) parser \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> string \<Rightarrow> 'b option" where
"run_parse_opt p f s = run_parse p f None s"

definition run_parse_opt' :: "('a, 'a option) parser \<Rightarrow> string \<Rightarrow> 'a option" where
"run_parse_opt' p s = run_parse_opt p Some s"

(* (plusParse (parseKeyword ''hi'')) Some ''hihihi''*)

(*
(* TODO: be more consistent in calling the parser input parameter l*)
(* TODO: rethink how to do this in light of datatype rework *)
function run_parse :: "llll option parser \<Rightarrow> string \<Rightarrow> (llll option)" where
"run_parse p s =
  p s (\<lambda> x s . x) (\<lambda> s . None)
    (run_parse p)"
  by pat_completeness auto
termination sorry
*)

definition hello :: string where "hello = ''hello''"

(* NB: use of fail' in the following two example
parsers is not great *)
fun silly_parse :: "(llll, llll option) parser" where
"silly_parse l su fa r =
 parseKeyword hello l
  (\<lambda> x l . su (L4L_Nat 0) l)
 (\<lambda> l . parseKeyword ''kitty'' l
  (\<lambda> x l . su (L4L_Nat 1) l) fa fail') fail'"


value "run_parse_opt' silly_parse ''kitty''"
value "run_parse_opt' silly_parse ''hello''"
value "run_parse_opt' silly_parse ''other''"

definition fourLParse_int :: "(llll, llll option) parser" where
"fourLParse_int l su fa r =
 parseNat l (\<lambda> x s . su (L4L_Nat (x)) s) fa fail'"

value "run_parse_opt' fourLParse_int ''1000''"

value "run_parse_opt' parseNat ''20''"

fun mapAll :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
"mapAll _ [] = Some []"
| "mapAll f (h#t) =
  (case f h of
   None \<Rightarrow> None
   | Some b \<Rightarrow> (case mapAll f t of
                 None \<Rightarrow> None
                 | Some t' \<Rightarrow> Some (b#t')))"

(* only allow nat literals for now *)
(* TODO: proper EOS handling for tokens (right now our tokens might have
crap at the end that gets ignored *)
(*
TODO: redo parseNat without parser combinators (?)
TODO: add macro forms - constants only for now
when looking for parameters we will need to peek ahead
*)

type_synonym funs_tab = "(string * (llll list \<Rightarrow> llll option)) list"

(*
type_synonym vars_tab = "(string * llll) list"
*)
(* do we need this? *)
type_synonym vars_tab = "string list"

(* do we need another type for variable contexts?
*)

(* TODO: handle macros here, or in llll_compile?
here might be easier
llll_compile might make more sense if def
is in the llll syntax. options are
1. have llll_compile not cover all cases (e.g. def, macro)
2. simply not put macros in llll syntax.

there is actually another, better option:
handle macros after tokenization
 *)
(* for now, heads of sexprs must be literals *)
(* we want this parser phase to not actually dispatch macros *)
(*
function(sequential) llll_parse1 :: "funs_tab \<Rightarrow> vars_tab \<Rightarrow> stree \<Rightarrow> llll option" where
"llll_parse1 _ _ (STStr s) =
  (case run_parse_opt' parseNat s of
    None \<Rightarrow> None
   | Some n \<Rightarrow> Some (L4L_Nat n))" (* TODO: string literals are also a thing *)
| "llll_parse1 ft vt (STStrs (h#t)) = 
  (* TODO: first check if h is a definition *)
   (case mapAll (llll_parse1 ft vt) t of
    None \<Rightarrow> None
    | Some ls \<Rightarrow> 
    (case h of
     STStr hs \<Rightarrow> 
      (case map_of ft hs of
        None \<Rightarrow> None
        | Some f \<Rightarrow> f ls)
    | _ \<Rightarrow> None))"
| "llll_parse1 _ _ _ = None"
*)

(* need a chaining function *)
fun chainAll :: "('a \<Rightarrow> 'st \<Rightarrow> ('a * 'st) option) \<Rightarrow> 'a list \<Rightarrow> 'st \<Rightarrow> ('a list * 'st) option" where
"chainAll _ [] st = Some ([], st)"
| "chainAll f (h#t) st =
  (case f h st of
   None \<Rightarrow> None
   | Some (b, st') \<Rightarrow> (case chainAll f t st' of
                        None \<Rightarrow> None
                       | Some (t', st'') \<Rightarrow> Some (b#t', st'')))"


fun lookupS :: "(string \<times> 'b) list \<Rightarrow> string \<Rightarrow> 'b option" where
"lookupS [] _ = None"
| "lookupS ((ah, bh)#t) a = 
    (if a = ah then Some bh else lookupS t a)"

fun mkConsts :: "string list \<Rightarrow> llll list \<Rightarrow> funs_tab option"
  where
"mkConsts [] [] = Some []"
| "mkConsts (sh#st) (lh#lt) =
  (case mkConsts st lt of
    None \<Rightarrow> None
   | Some ft \<Rightarrow> Some ((sh,(\<lambda> _ . Some lh))#ft))"
| "mkConsts _ _ = None"

definition streq :: "string \<Rightarrow> string \<Rightarrow> bool" where
"streq x y = (x = y)"

value "lookupS [(''a'',1), (''a'',2)] ''a'' :: nat option"

(* TODO: support "lit", "lll" constructs *)


value "String.char_of_nat 39"

definition apos :: char where
"apos = String.char_of_nat 39"

(* TODO: have vars_tab argument to anything but parse1_def?  *)
(* TODO: have llll_parse1_seq for parsing a sequence of arguments *)
fun llll_parse1 :: "funs_tab  \<Rightarrow> stree \<Rightarrow> (llll * llll option * funs_tab) option " 
and llll_parse1_def :: "string \<Rightarrow> funs_tab \<Rightarrow> vars_tab \<Rightarrow> stree list \<Rightarrow> (llll * llll option * funs_tab )option"
and llll_parse1_args :: "funs_tab \<Rightarrow> stree list \<Rightarrow> (llll list * llll option * funs_tab )option" 
where

(*
in this case (STStr s), we will then look things up in our vars_tab.
Note that vars cannot be head symbols as we
do not support 'higher order' macros
*)

"llll_parse1_def s ft vt [] = None"
(* this case is wrong, we should instead just push a new macro def and return funs_tab
   funs_tab will have a new macro added to it, which will correspond to a function that takes
a bunch of already-parsed parameter values and converts them to an llll option
*)


(* this case is wrong. need to
- return an empty sequence L4Seq []
- return a function that substitutes in for all variables
what this means is that we return a function that constructs a series of funstab entries (?) *)
(* TODO: double check reversing is the right thing here *)
| "llll_parse1_def name ft vt (h#[]) = 
  (case name of
   [] \<Rightarrow> None
   | [hdchr] \<Rightarrow> None
   | hdchr#name' \<Rightarrow>
     (if hdchr \<noteq> apos then None
      else Some (L4Seq [], None, (name', (\<lambda> l . 
        (case mkConsts vt (rev l) of
           None \<Rightarrow> None
  (* TODO: are we leaving out something important by extracting the first parameter?? *)
  (* what do we do if a definition has a returnlll in it? For now, we ignore that payload. *)
           | Some ft' \<Rightarrow> (case (llll_parse1 (ft'@ft) h) of
                                None \<Rightarrow> None
                              | Some (l, _, _) \<Rightarrow> Some l ))
 ))#ft)))"

| "llll_parse1_def name ft vt (h#t) = 
   (case h of
     STStr v \<Rightarrow> llll_parse1_def name ft (v#vt) t 
    | _ \<Rightarrow> None)"

| "llll_parse1_args ft [] = None"
(* is payload handling correct here? *)
| "llll_parse1_args ft (h#[]) = 
    (case llll_parse1 ft h of
     None \<Rightarrow> None
    | Some (l, x, ft') \<Rightarrow> Some ([l], x, ft'))"
(* TODO - double check this one *)
| "llll_parse1_args ft (h#t) = 
    (case llll_parse1 ft h of
     None \<Rightarrow> None
    | Some (h', None, ft') \<Rightarrow> (case llll_parse1_args ft' t of
                        None \<Rightarrow> None
                        | Some (t', x, ft'') \<Rightarrow> Some (h'#t', x, ft''))
    | Some (h', Some pay, ft') \<Rightarrow> Some ([h'], Some pay, ft'))"
(* idea: we have already seen a head symbol, so we just need
to parse a list of strees as follows: parse the head, track the modifications
to the function context, thread those to the tail
*)

(* TODO: this does not deal with nullary macros correctly, I think. Need a case for those. 
actually it looks like this is right...?*)
(* need to attempt to parse hex first *)
| "llll_parse1 ft (STStr s) =
  (case run_parse_opt' parseHex s of
    None \<Rightarrow>
    (case run_parse_opt' parseNat s of
      None \<Rightarrow> (case lookupS ft s of
                      None \<Rightarrow> None
                      | Some f \<Rightarrow> (case f [] of 
                                     None \<Rightarrow> None
                                    | Some l \<Rightarrow> Some (l, None, ft)))
      | Some n \<Rightarrow> Some (L4L_Nat n, None, ft))
    | Some n \<Rightarrow> Some (L4L_Nat n, None, ft)) " (* TODO: string literals are also a thing *)

(* arguments of the definition are going to be in an extra layer of parens *)
| "llll_parse1 ft (STStrs (h#t)) = 
   (case h of
     STStr hs \<Rightarrow>
      (if hs = ''def''
          then (case t of
                 (* make sure the name starts with an apostrophe, then drop it off *)
                  STStr(h2) # STStrs (l) # [d] \<Rightarrow> (case llll_parse1_def h2 ft [] (l@[d]) of
                                  None \<Rightarrow> None
                                | Some p \<Rightarrow> Some p)
                | STStr(h2) # [d] \<Rightarrow> (case llll_parse1_def h2 ft [] [d] of
                                  None \<Rightarrow> None
                                | Some p \<Rightarrow> Some p)
                | _ \<Rightarrow> None)
          else
          (if hs = ''returnlll''
            then (case t of
                  [paysrc] \<Rightarrow> 
                    (case llll_parse1 ft paysrc of
                      Some (ls, None, ft') \<Rightarrow> Some (L4Seq [], Some ls, ft')
                      | _ \<Rightarrow> None)
                  | _ \<Rightarrow> None)
            else
            (case ((lookupS ft hs) :: (llll list \<Rightarrow> llll option) option) of
              None \<Rightarrow> None
             | Some f \<Rightarrow> (case llll_parse1_args ft t of
                          None \<Rightarrow> None
                         | Some (ls, x, ft') \<Rightarrow> (case f ls of
                                       None \<Rightarrow> None
                                       | Some l \<Rightarrow> Some(l, x, ft'))))))
    | _ \<Rightarrow> None)"
| "llll_parse1 ft  (STStrs []) = None"
(*

   (case  (llll_parse1 ft vt) t of
    None \<Rightarrow> None
    | Some ls \<Rightarrow> 
    (case h of
     STStr hs \<Rightarrow> 
      (case map_of ft hs of
        None \<Rightarrow> None
        | Some f \<Rightarrow> (f ls, ft))
    | _ \<Rightarrow> None))"
| "llll_parse1 _ _ _ = None"
*)
(* To emulate behavior of LLL, we need to have a state that is carried from
one statement (in parsing order) to the next. that is to say, we need to return a new
funs_tab and vars_tab (at most, maybe can get away with less - do we just need funs tab?) *)

(* to correctly parse defs, we will have to
no longer use mapAll - instead we will have to chain explicitly
- other notes: will we have to explicitly decrease the stacks when we are done?

should output type be (llll * funs_tab * vars tab)?
should it just be (llll * funs_tab)?
*)

(* idea: can we dispatch macros when compiling llll \<Rightarrow> ll1?
(* everything we don't recognize just becomes a macro invocation *)
*)

(* TODO functions for threading POPs in between elements of SEQ *)
(* *)

(* default *)
definition default_llll_funs :: funs_tab where
"default_llll_funs =
[
(* control constructs *)
(* TODO make this pop all but last result *)
 (''seq'', (\<lambda> l . Some (L4Seq l)))
,(''if'', (\<lambda> l . case l of
                 c # br1 # [br2] \<Rightarrow> Some (L4If c br1 br2)
                 | _ \<Rightarrow> None))
,(''when'', (\<lambda> l . case l of
                 c # [br] \<Rightarrow> Some (L4When c br)
                 | _ \<Rightarrow> None))
(* integer arithmetic *)
,(''+'', (\<lambda> l . Some (L4Arith LAPlus l)))
,(''-'', (\<lambda> l . Some (L4Arith LAMinus l)))
,(''*'', (\<lambda> l . Some (L4Arith LATimes l)))
,(''div'', (\<lambda> l . Some (L4Arith LADiv l)))
,(''exp'', (\<lambda> l . Some (L4Arith LAExp l)))
,(''/'', (\<lambda> l . Some (L4Arith LADiv l)))
,(''%'', (\<lambda> l . Some (L4Arith LAMod l)))
(* bitwise logic *)
,(''&'', (\<lambda> l . Some (L4Arith LAAnd l)))
,(''|'', (\<lambda> l . Some (L4Arith LAOr l)))
,(''^'', (\<lambda> l . Some (L4Arith LAXor l)))
,(''~'', (\<lambda> l . Some (L4Arith LANot l)))
(* boolean logic *)
,(''&&'', (\<lambda> l . Some (L4Logic LLAnd l)))
,(''||'', (\<lambda> l . Some (L4Logic LLOr l)))
,(''!'', (\<lambda> l . Some (L4Logic LLNot l)))
(* comparisons - for later*)
,(''='', (\<lambda> l . case l of
                lhs#[rhs] \<Rightarrow> Some (L4Comp LCEq lhs rhs)
                | _ \<Rightarrow> None))
(* other constructs, loads/stores - for later*)
,(''mstore'', (\<lambda> l . case l of
                loc#[sz] \<Rightarrow> Some (L4I2 (Memory MSTORE) loc sz)
                | _ \<Rightarrow> None))
,(''return'', (\<lambda> l . case l of
                loc#[sz] \<Rightarrow> Some (L4I2 (Misc RETURN) loc sz)
                | _ \<Rightarrow> None))
,(''calldataload'', (\<lambda> l . case l of
                [loc] \<Rightarrow> Some (L4I1 (Stack CALLDATALOAD) loc)
                | _ \<Rightarrow> None))
,(''sstore'', (\<lambda> l . case l of
                loc#[sz] \<Rightarrow> Some (L4I2 (Storage SSTORE) loc sz)
                | _ \<Rightarrow> None))
,(''sload'', (\<lambda> l . case l of
                [loc] \<Rightarrow> Some (L4I1 (Storage SLOAD) loc)))
(* data insertion - for later*)
]
"

definition llll_parse1_default :: "stree \<Rightarrow> (llll * llll option) option" where
"llll_parse1_default st = 
  (case llll_parse1 default_llll_funs st of
   None \<Rightarrow> None
   | Some (l, x, _) \<Rightarrow> Some (l, x))"

definition llll_parse_complete :: "string \<Rightarrow> (llll * llll option) option" where
"llll_parse_complete s =
  (case llll_parse0 s of
   None \<Rightarrow> None
  | Some st \<Rightarrow> llll_parse1_default st)"

(* used if there is a payload - creates the "interlude" that returns
the code to be deployed *)

(*
fun llll_combine_payload :: "llll \<Rightarrow> llll \<Rightarrow> nat \<Rightarrow> inst list" where
"llll_combine_payload l1 l2 =
*)

fun ilsz :: "inst list \<Rightarrow> nat" where
"ilsz [] = 0"
| "ilsz (h#t) =
   nat (Evm.inst_size h) + ilsz t"

(* 9 is the size of all the non-variable "interlude" instructions :
PUSH_N (sans payload)
DUP
PUSH_N (sans payload)
PUSH_N (0)
CODECOPY
PUSH_N (0)
RETURN
*)
definition base_interlude_size :: nat where
"base_interlude_size = 9"

fun llll_combine_payload_sub :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat * nat) option " where
"llll_combine_payload_sub fuel presz paysz startbytes endbytes =
 (if fuel = 0 then None
  else (if encode_size (paysz) = endbytes
        then (if encode_size (presz + startbytes + endbytes + base_interlude_size) = startbytes
              then Some (startbytes, endbytes)
              else llll_combine_payload_sub (fuel - 1) presz paysz (startbytes + 1) endbytes)
        else llll_combine_payload_sub (fuel - 1) presz paysz startbytes (endbytes + 1)))"

(* 32 bytes for each address pushed *)
definition combine_payload_fuel :: nat where
"combine_payload_fuel = 32 + 32"

(* assumes that sizes of startbytes and endbytes calculated correctly *)
definition makeInterlude :: "nat \<Rightarrow> nat \<Rightarrow> inst list \<Rightarrow> inst list \<Rightarrow> inst list" where
"makeInterlude startbytes endbytes prelude payload =
 prelude @ 
 [Evm.inst.Stack (PUSH_N (output_address (ilsz payload)))] @
 [Evm.inst.Dup 0] @
 [Evm.inst.Stack (PUSH_N (output_address (ilsz prelude + startbytes + endbytes + base_interlude_size)))] @
 [Evm.inst.Stack (PUSH_N (output_address 0))] @
 [Evm.inst.Memory CODECOPY] @
 [Evm.inst.Stack (PUSH_N (output_address 0))] @
 [Evm.inst.Misc RETURN] @
 payload"


(*
fun llll_combine_payload :: "inst list \<Rightarrow> inst list \<Rightarrow> nat \<Rightarrow> inst list" where
"llll_combine_payload l1 l2 n =
*)
value "llll_parse_complete ''(seq (+ 2 3) (- 1 2) (returnlll (- 1 2)))''"

value "llll_parse_complete ''(seq (+ 0x022 3) (+ 1 2))''"

value "llll_parse0 ''(seq (+ 2 3) (+ 1 a))''"

value "llll_parse_complete ''(seq (+ 2 3) (+ 1 a))''"

value "llll_parse_complete ''(seq (+ 2 3) (+ 1 a))''"


value "llll_parse_complete ''(seq (def 'a 1) (+ 2 3) (+ 1 a)))''"

value "llll_parse_complete ''(seq (def a 1) (def a 2) a)''"

(* echo *)

value "llll_parse_complete
  ''(seq
  (def 'scratch 0x00)
  (def 'identity 0xac37eebb)
  (def 'function (function-hash code-body) (+ 1 2)))''"

value "llll_parse_complete
''(seq
  (def 'scratch 0x00)
  (def 'identity 0xac37eebb)
  (def 'function (function-hash code-body)
    (when (= (div (calldataload 0x00) (exp 2 224)) function-hash)
      code-body))
  (def 'plus (avar bvar) (+ avar bvar))
  (returnlll
    (function identity
      (seq
        (mstore scratch (calldataload 0x04))
        (return scratch 32)))))''"

(* erc20 *)
(*     
    (function identity 1)))''"
*)
(*
      (seq
        (mstore scratch (calldataload 0x04))
        (return scratch 32)))))
''"
*)
(*
    (when (= (div (calldataload 0x00) (exp 2 224)) function-hash)
      code-body))
  ''"
*)
(* finally, we need to integrate our function for making the interlude *)
(* then, plug this into FourLExtract *)
definition il2wl :: "inst list \<Rightarrow> 8 word list" where
"il2wl il = List.concat (map Evm.inst_code il)"

(* translations to word-lists for string literals *)
definition chartow :: "char \<Rightarrow> 8 word" where
"chartow c = Evm.byteFromNat (String.char.nat_of_char c)"

definition strtowl :: "string \<Rightarrow> 8 word list" where
"strtowl s = List.map chartow s"

(* translations to word lists for int literals *)

definition fourL_compiler_string :: "string \<Rightarrow> string option" where
"fourL_compiler_string s =
  (case llll_parse_complete s of
   None \<Rightarrow> None
  | Some (l4pre, None) \<Rightarrow>
   ( case pipeline (llll_compile l4pre) (get_process_jumps_fuel (ll_pass1 (llll_compile l4pre))) of
      None \<Rightarrow> None
      | Some wl \<Rightarrow> Some (hexwrite wl)
   )
  | Some (l4pre, Some l4pay) \<Rightarrow>
    (case pipeline'' (llll_compile l4pre) (get_process_jumps_fuel (ll_pass1 (llll_compile l4pre))) of
     None \<Rightarrow> None
     | Some il_pre \<Rightarrow> (case pipeline'' (llll_compile l4pay) (get_process_jumps_fuel (ll_pass1 (llll_compile l4pay))) of
        None \<Rightarrow> None
        | Some il_pay \<Rightarrow>
          (case llll_combine_payload_sub combine_payload_fuel (ilsz il_pre) (ilsz il_pay) 0 0 of
            None \<Rightarrow> None
            | Some (startbytes, endbytes) \<Rightarrow> 
              Some (hexwrite (il2wl (makeInterlude startbytes endbytes il_pre il_pay)))
           )
 )))"

value "llll_parse_complete  ''(seq 1 2)''"

value "fourL_compiler_string  ''(seq 1 2)''"


value "case llll_parse_complete ''(seq 1 2)'' of
       None \<Rightarrow> None
       | Some (pre, None) \<Rightarrow> pipeline'' (llll_compile pre) (ll1_get_process_jumps_fuel (llll_compile pre))
      | _ \<Rightarrow> None"

end


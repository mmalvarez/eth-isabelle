theory FourL
  imports Main ElleSyntax ElleCompiler
begin

(* deal with literals:
- strings (truncate to 32 bytes, left align)
- integers
- expressions
*)

datatype llllarith =
   LAPlus
  | LAMinus

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
   | L4L_Def "string" "string list"
   | L4L_Mac "string" "llll list"
  | L4I "inst"
  | L4Seq "llll list"
  | L4Arith "llllarith" "llll list"
  | L4When "llll" "llll"
  | L4If "llll" "llll" "llll"
  | L4While "llll" "llll"

(* Read in a string as a word list (truncate to 32 bytes)*)
(* TODO: need to explicitly pad with zeros? *)
(* i think we might not need to, let's see *)
fun truncate_string_sub :: "string \<Rightarrow> nat \<Rightarrow> 8 word list"
  where
"truncate_string_sub _ 0 = []"
| "truncate_string_sub [] (Suc n) = byteFromNat 0 # truncate_string_sub [] n"
| "truncate_string_sub (h#t) (Suc n) =
   byteFromNat (String.char.nat_of_char h) #
   truncate_string_sub t n"

definition truncate_string :: "string \<Rightarrow> 8 word list"
  where "truncate_string s = truncate_string_sub s 32"

(* ints need to be right aligned (lowest sig bit) *)
(* output_address, from ElleCompiler, should work *)
(* note that this effectively means that
PUSHes are little-endian?
but no, numbers _are_ big endian in EVM
*)
definition intToBytes :: "int \<Rightarrow> 8 word list" where
"intToBytes i = bytes_of_nat (Int.nat i)"

value "intToBytes 2049"

(* TODO: do we need raw?
If so, how do we get it?
Raw means we need to basically save the first non-void result *)

(* TODO: is this the right ("jnz") semantics? *)
(* Idea: literals translate into pushes *)
fun llll_compile :: "llll \<Rightarrow> ll1" where
"llll_compile (L4L_Str s) = ll1.L (Evm.inst.Stack (PUSH_N (truncate_string s)))"
| "llll_compile (L4L_Nat i) = ll1.L (Evm.inst.Stack (PUSH_N (intToBytes (int i))))"
| "llll_compile (L4I i) = ll1.L i"
| "llll_compile (L4Seq l) = ll1.LSeq (map llll_compile l)"
| "llll_compile (L4When c l) =
   ll1.LSeq [llll_compile c, ll1.LJmpI 0, llll_compile l, ll1.LLab 0]"
| "llll_compile (L4If c l1 l2) = 
   ll1.LSeq [llll_compile c, ll1.LJmpI 0, llll_compile l2, ll1.LLab 0]"
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

(* TODO: support comments
idea: add an extra flag (" we are in a comment") when we see a ;
clear it when we see a newline *)
fun llll_parse' :: "string \<Rightarrow> string \<Rightarrow> stree list  \<Rightarrow> stree option" where
"llll_parse' [] _ _ = None"
| "llll_parse' (h#t) token parsed =
   (if h = CHR ''(''
       then llll_parse' t token ((STStrs [])#parsed)
    else (if h = CHR '')''
          then (case parsed of
                [] \<Rightarrow> None
                | ph#[] \<Rightarrow> if token \<noteq> [] then Some (stree_append ph (STStr token))
                                         else Some ph
                | ph1#ph2#pt \<Rightarrow> if token \<noteq> [] then llll_parse' t [] (stree_append ph2 (stree_append ph1 (STStr token)) # pt)
                                              else llll_parse' t [] (stree_append ph2 ph1#pt))
    else (if isWs h
          then (if token \<noteq> [] then 
                (case parsed of
                   [] \<Rightarrow> None
                   | ph#pt \<Rightarrow> llll_parse' t [] (stree_append ph (STStr token) #pt))
                else llll_parse' t [] parsed) 
    else llll_parse' t (token@[h]) parsed)))"

fun llll_parse0 :: "string \<Rightarrow> stree option" where
"llll_parse0 s = llll_parse' s [] []"

value "llll_parse0 ''(+ 11 1)''"

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
value "LemExtraDefs.char_to_digit (CHR ''B'')"

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
function(sequential) llll_parse1 :: "stree \<Rightarrow> llll option" where
"llll_parse1 (STStr s) =
  (case run_parse_opt' parseNat s of
    None \<Rightarrow> None
   | Some n \<Rightarrow> Some (L4L_Nat n))"
| "llll_parse1 (STStrs (h#t)) = 
   (case mapAll llll_parse1 t of
    None \<Rightarrow> None
    | Some ls \<Rightarrow> 
    (if h = STStr ''seq'' then Some (L4Seq ls)
     else if h = STStr ''+'' then Some (L4Arith LAPlus ls)
     else if h = STStr ''-'' then Some (L4Arith LAMinus ls)
     else None))"
| "llll_parse1 _ = None"
  by pat_completeness auto
termination sorry

definition llll_parse :: "string \<Rightarrow> llll option" where
"llll_parse s = 
  (case llll_parse0 s of
   None \<Rightarrow> None
   | Some st \<Rightarrow> llll_parse1 st)"

value "llll_parse ''(seq (+ 1 2) (+ 2 3 3))''"

value "llll_parse0 ''(seq (def a 2) (+ 2 3 3))''"

(* idea: no parentheses yet.
"+ 1 2" or "- 1 2" should parse correctly means
*)

(* one or more of something, separated by a delimiter string *)
(* idea: first we parse one of the thing
   then we attempt to parse a delimiter and repeat the process on the tail
   if that all succeeds, succeed
   otherwise, fail
*)
(* Q: make this more general? have arbitrary parsers for the delimiters? *)
(*
function(sequential) delimitParse_sub :: "string \<Rightarrow> ('a, 'b) parser \<Rightarrow> 'a list \<Rightarrow> ('a list, 'b) parser" where
"delimitParse_sub s parse acc l su fa r =
  parseKeyword s l
  (\<lambda> x l . parse l 
    (\<lambda> x1 l . delimitParse_sub s parse (acc@[x1]) l
             (\<lambda> x2 l . su x2 l)
             (\<lambda> l . su (acc@[x1]) l) r)
  fa r)
  fa r"
  by pat_completeness auto
termination sorry
*)
fun endInputParse :: "(unit, 'b) parser" where
"endInputParse [] su fa r =
  su () []"
| "endInputParse l su fa r =
  fa l"

(* useful primitives:
 - chaining successes
 - chaining failures
 - choices of alternatives
 - greedy recursive matching (?)
 - one or more *)

(*
more concretely:
- chaining successes (done)
- choose between 2 alternatives, i.e. chaining in the first one's failure case
- optionally run a parser (can be seen as choice between parser and empty, or its own thing)
*)

(* This is bind. We are monadic in the first parameter *)
(*
definition chainParse :: "('a1, 'b) parser \<Rightarrow> ('a1 \<Rightarrow> ('a2, 'b) parser) \<Rightarrow> ('a2, 'b) parser" where
"chainParse parse after l su fa r =
  parse l
   (\<lambda> x l . after x l su fa r)
   fa r
"
*)

(* TODO: is this improperly discarding results in recursor? *)
definition chainParse :: "('a1, 'b) parser \<Rightarrow> ('a1 \<Rightarrow> ('a2, 'b) parser) \<Rightarrow> ('a2, 'b) parser" where
"chainParse parse after l su fa r =
  parse l
   (\<lambda> x l . after x l su fa r)
   fa (\<lambda> l' su' fa' . r l' su fa)"


(* bind, without assignment *)
(* doesn't seem to work, idk why *)
definition seqParse :: "('a1, 'b) parser \<Rightarrow> ('a2, 'b) parser \<Rightarrow> ('a2, 'b) parser" where
"seqParse before parse l su fa r =
  chainParse before (\<lambda> _ . parse) l su fa r"


definition seqParse' :: "('a1, 'b) parser \<Rightarrow> ('a2, 'b) parser \<Rightarrow> ('a2, 'b) parser" where
"seqParse' before parse l su fa r =
  before l (\<lambda> _ l . parse l su fa r) fa (\<lambda> l' s' fa' . r l' su fa)"

(* seq parse, returning first result *)
definition seqParse1 :: "('a1, 'b) parser \<Rightarrow> ('a2, 'b) parser \<Rightarrow> ('a1, 'b) parser" where
"seqParse1 parse after l su fa r =
  parse l
  (\<lambda> x l . after l (\<lambda> _ . su x) fa (\<lambda> l' su' fa' . r l' su fa)) fa r"

(* return *)
definition retParse :: "'a \<Rightarrow> ('a, 'b) parser" where
"retParse x l su fa r =
  su x l"

(* TODO: can this now have a more general type? *)
definition choiceParse :: "('a, 'b) parser \<Rightarrow> ('a, 'b) parser \<Rightarrow> ('a, 'b) parser" where
"choiceParse parse1 parse2 l su fa r =
  parse1 l su
   (\<lambda> l . parse2 l su fa r) r"

(* Q: handling empty lists *)
fun choicesParse' :: "('a, 'b) parser \<Rightarrow> ('a, 'b) parser list \<Rightarrow> ('a, 'b) parser" where
"choicesParse' parse [] l su fa r = parse l su fa r"
| "choicesParse' parse (ph#pt) l su fa r =
 choiceParse parse (choicesParse' ph pt) l su
   fa r"
  

(* takes a default value, if parsing fails
nil, in the case of delimitParse *)
(* ordering of inputs to this guy? *)
definition optionalParse :: "('a, 'b) parser \<Rightarrow> 'a \<Rightarrow> ('a, 'b) parser" where
"optionalParse parse dfl l su fa r =
  parse l su (su dfl) r"

function(sequential) starParse_sub :: "('a, 'b) parser \<Rightarrow> 'a list \<Rightarrow> ('a list, 'b) parser" where
"starParse_sub parse acc l su fa r =
  parse l (\<lambda> x l . starParse_sub parse (acc@[x]) l su fa r)
    (su acc) (\<lambda> l' su' fa' . r l' su fa)"
  by pat_completeness auto
termination sorry

definition starParse :: "('a, 'b) parser \<Rightarrow> ('a list, 'b) parser" where
"starParse parse l su fa r = starParse_sub parse [] l su fa r"


value "run_parse' (starParse (parseKeyword ''hi'')) [] ''hi''"


definition plusParse :: "('a, 'b) parser \<Rightarrow> ('a list, 'b) parser" where
"plusParse parse l su fa r =
  parse l (\<lambda> x l . starParse_sub parse [x] l su fa r) 
  fa (\<lambda> l' su' fa' . r l' su fa)"

value "run_parse' (plusParse (parseKeyword ''hi'')) [] ''''"


value "run_parse_opt' (plusParse (parseKeyword ''hi'')) ''hihihi''"


value "run_parse' (plusParse (parseKeyword ''hi'')) [] ''''"

value "run_parse (plusParse (parseKeyword ''hi'')) Some None ''''"

value "run_parse (plusParse (parseKeyword ''hi'')) Some None ''hihihi''"

(*
value "run_parse (chainParse (plusParse (parseKeyword ''hi'')) examine_unit_result) ''hi''"

value "run_parse (chainParse (plusParse (parseKeyword ''hi'')) examine_unit_result) ''hihi''"
*)


fun parseWs :: "(unit, 'a) parser" where
"parseWs [] su fa r = fa []"
| "parseWs (h#t) su fa r =
   (if isWs h then (su () t)
    else fa (h#t))"
   
function(sequential) delimitParse'_sub :: "('x, 'b) parser \<Rightarrow> ('a, 'b) parser \<Rightarrow> 'a list \<Rightarrow> ('a list, 'b) parser" where
"delimitParse'_sub del parse acc l su fa r =
  del l
  (\<lambda> x0 l . parse l
    (\<lambda> x1 l . delimitParse'_sub del parse (acc@[x1]) l
        (\<lambda> x2 l . su x2 l)
        (\<lambda> l . su (acc @ [x1]) l) (\<lambda> l' su' fa' . r l' su fa))
    fa (\<lambda> l' su' fa' . r l' su fa))
  fa (\<lambda> l' su' fa' . r l' su fa)
"
  by pat_completeness auto
termination sorry

definition delimitParse :: "('x, 'b) parser \<Rightarrow> ('a, 'b) parser \<Rightarrow> ('a list, 'b) parser" where
"delimitParse del parse l su fa r = 
  parse l 
    (\<lambda> x1 l . delimitParse'_sub del parse [x1] l
             (\<lambda> x2 l . su x2 l)
             (\<lambda> l . su [x1] l) r)
  fa (\<lambda> l' su' fa' . r l' su fa)"


(* need a more general delimit parser that can use arbitrary
parsers for the delimiter *)

(* TODO: rework this type *)
fun nums_parse :: "(nat list, 'b) parser" where
"nums_parse l su fa = (delimitParse (parseWs) parseNat) l
  su fa"
  
value "run_parse nums_parse Some None ''10 11''"

(* idea:  *)

(* arith parser, with choice parsing, shows off + and - *)
(* needs to handle whitespace: parsing arith entails:
- parse  0 or more whitespace
- parse open paren
- 
*)

(*
idea:
- parse keyword ''(''
- then parse either
  - operator
    - then parse a list of arith
  - num
- then parse keyword '')'', returning last result
*)

(* dispatching on keywords:
- parse keyword, using choice
- return the appropriate arith op *)

(* another thing we need: guardParse (?) *)
(* Take a parser as argument. If parser succeeds we succeed
 *)

definition arith_parse0 :: "(llllarith, llllarith option) parser" where
"arith_parse0 l su fa r  =
  chainParse
  (parseKeyword ''('')
  (\<lambda> _ . (retParse LAPlus) :: (llllarith, llllarith option) parser) l su fa r"

definition arith_parse01 :: "(llllarith, llllarith option) parser" where
"arith_parse01 l su fa r  =
  seqParse'
  (parseKeyword ''('')
  ((retParse LAPlus) :: (llllarith, llllarith option) parser) l su fa r"

definition arith_parse1 :: "(llll, llll option) parser" where
"arith_parse1 l su fa r  =
  chainParse
  (parseKeyword ''('')
  (\<lambda> _ . chainParse (choicesParse'
              (chainParse (parseKeyword ''+'') 
                          (\<lambda> _ . retParse LAPlus))
             [(chainParse (parseKeyword ''-'') 
                         (\<lambda> _ . retParse LAMinus))])
              (\<lambda> x . retParse (L4Arith x []))) l su fa r
 "

definition wsSep :: "('a, 'b) parser \<Rightarrow> ('a list, 'b) parser" where
"wsSep p = delimitParse (plusParse parseWs) p"

value "run_parse_opt' (wsSep (parseKeyword ''hi'')) ''hi hi hi''"

value "run_parse_opt' arith_parse0  ''(-''"
value "run_parse_opt' arith_parse1  ''(-''"

(* need an arith_parse2_inner,
mutually recursive with this one?
or can we use "r" parameter? *)

(* 
idea: for "plus", do:
- parse +
- parse whitespace delimited list of ariths (using recursor arg. r)
- use retParse to return that list as part of the arguments
*)

(* this doesn't work? *)
definition wrapParser :: "(string \<Rightarrow> 'b) \<Rightarrow> (unit, 'b) parser" where
"wrapParser f l su fa r =
  f l "

(* TODO replace this with "run parse'" *)

definition arith_parse2_inner :: "(llll, llll option) parser" where
"arith_parse2_inner l su fa r =
chainParse (choicesParse'
              (chainParse (parseNat) 
                          (\<lambda> x . retParse (L4L_Nat x)))
             [(chainParse (parseKeyword ''+'') 
                          (\<lambda> _ . chainParse (wsSep (wrapParser r))
                          (\<lambda> l s . retParse (L4Arith LAPlus l))))])
su fa (\<lambda> l' su' fa' . r l' su fa)"

(* parse optional whitespaces throughout here *)
(* Q: when to use passed-in R vs the initial one *)
function(sequential) arith_parse2 :: "(llll, llll option) parser" where
"arith_parse2 l su fa r  =
  chainParse
  (parseKeyword ''('')
  (\<lambda> _ . 
    chainParse (choicesParse'
              (chainParse (parseInt) (\<lambda> x . retParse (L4L_Int x)))
             [(chainParse (parseKeyword ''+'') 
                          (\<lambda> _ . retParse (L4Arith LAPlus []))),
              (chainParse (parseKeyword ''-'') 
                         (\<lambda> _ . retParse (L4Arith LAMinus [])))])
     (\<lambda> x . chainParse (parseKeyword '')'') (\<lambda> _ . retParse x)))
              l su fa r
 "
  by pat_completeness auto
termination sorry

value "run_parse_opt' arith_parse2  ''(12)''"


(* next up we need to return a list of operands
as well as *)

(* require ''+'', then '' '' (for now) *)
(*
fun arith_parse1 :: "llll option parser" where
"arith_parse1 l su fa =
  (parseKeyword ''+'' l
   (\<lambda> x l . parseKeyword '' '' l
      (\<lambda> x l .  (delimitParse '' '' parseInt) l
        (\<lambda> x l . su (Some (L4Arith LAPlus (map L4L_Int x))) l)
        fa)
      fa)
   fa)"

value "run_parse arith_parse1 ''+ 1 0 2''"
*)

(*

need to start by parsing "("
end by parsing ")"

choice:
( - parse +
    - then parse one or more whitespaces
      - then 

fun arith_parse1 :: "llll option parser" where
"arith_parse1 l su fa =
  (parseChoice 
    (pa)
    ())
*)
(*

fun fourLParse_arith_test :: "llll option parser" where
"fourLParse_arith_test l su fa =
 parseKeyword ''+'' l
  

fun fourLParse_add :: "llll option parser" where
"fourLParse_sub l su fa =
 (* addition *)
 parseKeyword ''+'' l
  (\<lambda> x s . su (fourLParse_sub

*)
(*
fun fourLParse :: "string \<Rightarrow> (string \<Rightarrow> llll option) \<Rightarrow> (string \<Rightarrow> llll option) \<Rightarrow> llll option" where
"fourParse"
*)

end
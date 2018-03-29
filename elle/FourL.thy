theory FourL
  imports Main ElleSyntax
begin

datatype llll =
  L4I "inst"
  | L4Seq "llll" "llll"
  | L4When "llll" "llll"
  | L4If "llll" "llll" "llll"
  | L4While "llll" "llll"

(* TODO: is this the right ("jnz") semantics? *)
fun llll_compile :: "llll \<Rightarrow> ll1" where
"llll_compile (L4I i) = ll1.L i"
| "llll_compile (L4Seq l1 l2) = ll1.LSeq ([llll_compile l1, llll_compile l2])"
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
(*
| "llll_compile (L4Until c l) =
   ll1.LSeq [
   ll1.LSeq [ ll1.LLab 0,
              llll_compile c, ll1.LJmpI 1,
              llll_compile l,
              ll1.LJmp 0,
              ll1.LLab 1]]
*)

(* result semantics: "for" discards *)
end
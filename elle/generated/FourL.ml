module FourL : sig
  type char
  val compiler : string -> string option
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

type int = Zero_int | Pos of num | Neg of num;;

let rec equal_inta x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                     | Neg k, Pos l -> false
                     | Neg k, Zero_int -> false
                     | Pos k, Neg l -> false
                     | Pos k, Pos l -> equal_num k l
                     | Pos k, Zero_int -> false
                     | Zero_int, Neg l -> false
                     | Zero_int, Pos l -> false
                     | Zero_int, Zero_int -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

let one_inta : int = Pos One;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec plus_num
  x0 x1 = match x0, x1 with Bit1 m, Bit1 n -> Bit0 (plus_num (plus_num m n) One)
    | Bit1 m, Bit0 n -> Bit1 (plus_num m n)
    | Bit1 m, One -> Bit0 (plus_num m One)
    | Bit0 m, Bit1 n -> Bit1 (plus_num m n)
    | Bit0 m, Bit0 n -> Bit0 (plus_num m n)
    | Bit0 m, One -> Bit1 m
    | One, Bit1 n -> Bit0 (plus_num n One)
    | One, Bit0 n -> Bit1 n
    | One, One -> Bit0 One;;

let rec uminus_int = function Neg m -> Pos m
                     | Pos m -> Neg m
                     | Zero_int -> Zero_int;;

let rec bitM = function One -> One
               | Bit0 n -> Bit1 (bitM n)
               | Bit1 n -> Bit1 (Bit0 n);;

let rec dup = function Neg n -> Neg (Bit0 n)
              | Pos n -> Pos (Bit0 n)
              | Zero_int -> Zero_int;;

let rec plus_inta k l = match k, l with Neg m, Neg n -> Neg (plus_num m n)
                    | Neg m, Pos n -> sub n m
                    | Pos m, Neg n -> sub m n
                    | Pos m, Pos n -> Pos (plus_num m n)
                    | Zero_int, l -> l
                    | k, Zero_int -> k
and sub
  x0 x1 = match x0, x1 with Bit0 m, Bit1 n -> minus_int (dup (sub m n)) one_inta
    | Bit1 m, Bit0 n -> plus_inta (dup (sub m n)) one_inta
    | Bit1 m, Bit1 n -> dup (sub m n)
    | Bit0 m, Bit0 n -> dup (sub m n)
    | One, Bit1 n -> Neg (Bit0 n)
    | One, Bit0 n -> Neg (bitM n)
    | Bit1 m, One -> Pos (Bit0 m)
    | Bit0 m, One -> Pos (bitM m)
    | One, One -> Zero_int
and minus_int k l = match k, l with Neg m, Neg n -> sub n m
                | Neg m, Pos n -> Neg (plus_num m n)
                | Pos m, Neg n -> Pos (plus_num m n)
                | Pos m, Pos n -> sub m n
                | Zero_int, l -> uminus_int l
                | k, Zero_int -> k;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_int = ({plus = plus_inta} : int plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_int = ({zero = Zero_int} : int zero);;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};;

type 'a numeral =
  {one_numeral : 'a one; semigroup_add_numeral : 'a semigroup_add};;

let semigroup_add_int = ({plus_semigroup_add = plus_int} : int semigroup_add);;

let numeral_int =
  ({one_numeral = one_int; semigroup_add_numeral = semigroup_add_int} :
    int numeral);;

let rec times_num
  m n = match m, n with
    Bit1 m, Bit1 n -> Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
    | Bit1 m, Bit0 n -> Bit0 (times_num (Bit1 m) n)
    | Bit0 m, Bit1 n -> Bit0 (times_num m (Bit1 n))
    | Bit0 m, Bit0 n -> Bit0 (Bit0 (times_num m n))
    | One, n -> n
    | m, One -> m;;

let rec times_inta k l = match k, l with Neg m, Neg n -> Pos (times_num m n)
                     | Neg m, Pos n -> Neg (times_num m n)
                     | Pos m, Neg n -> Neg (times_num m n)
                     | Pos m, Pos n -> Pos (times_num m n)
                     | Zero_int, l -> Zero_int
                     | k, Zero_int -> Zero_int;;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_int = ({times = times_inta} : int times);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

let rec less_eq_num x0 n = match x0, n with Bit1 m, Bit0 n -> less_num m n
                      | Bit1 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit1 n -> less_eq_num m n
                      | Bit0 m, Bit0 n -> less_eq_num m n
                      | Bit1 m, One -> false
                      | Bit0 m, One -> false
                      | One, n -> true
and less_num m x1 = match m, x1 with Bit1 m, Bit0 n -> less_num m n
               | Bit1 m, Bit1 n -> less_num m n
               | Bit0 m, Bit1 n -> less_eq_num m n
               | Bit0 m, Bit0 n -> less_num m n
               | One, Bit1 n -> true
               | One, Bit0 n -> true
               | m, One -> false;;

let rec less_eq_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_eq_num l k
                      | Neg k, Pos l -> true
                      | Neg k, Zero_int -> true
                      | Pos k, Neg l -> false
                      | Pos k, Pos l -> less_eq_num k l
                      | Pos k, Zero_int -> false
                      | Zero_int, Neg l -> false
                      | Zero_int, Pos l -> true
                      | Zero_int, Zero_int -> true;;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec less_int x0 x1 = match x0, x1 with Neg k, Neg l -> less_num l k
                   | Neg k, Pos l -> true
                   | Neg k, Zero_int -> true
                   | Pos k, Neg l -> false
                   | Pos k, Pos l -> less_num k l
                   | Pos k, Zero_int -> false
                   | Zero_int, Neg l -> false
                   | Zero_int, Pos l -> true
                   | Zero_int, Zero_int -> false;;

let ord_int = ({less_eq = less_eq_int; less = less_int} : int ord);;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add;
    semigroup_mult_semiring : 'a semigroup_mult};;

let ab_semigroup_add_int =
  ({semigroup_add_ab_semigroup_add = semigroup_add_int} :
    int ab_semigroup_add);;

let semigroup_mult_int =
  ({times_semigroup_mult = times_int} : int semigroup_mult);;

let semiring_int =
  ({ab_semigroup_add_semiring = ab_semigroup_add_int;
     semigroup_mult_semiring = semigroup_mult_int}
    : int semiring);;

type 'a preorder = {ord_preorder : 'a ord};;

type 'a order = {preorder_order : 'a preorder};;

let preorder_int = ({ord_preorder = ord_int} : int preorder);;

let order_int = ({preorder_order = preorder_int} : int order);;

type 'a mult_zero = {times_mult_zero : 'a times; zero_mult_zero : 'a zero};;

let mult_zero_int =
  ({times_mult_zero = times_int; zero_mult_zero = zero_int} : int mult_zero);;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add; zero_monoid_add : 'a zero};;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add;
    monoid_add_comm_monoid_add : 'a monoid_add};;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add;
    mult_zero_semiring_0 : 'a mult_zero; semiring_semiring_0 : 'a semiring};;

let monoid_add_int =
  ({semigroup_add_monoid_add = semigroup_add_int; zero_monoid_add = zero_int} :
    int monoid_add);;

let comm_monoid_add_int =
  ({ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int;
     monoid_add_comm_monoid_add = monoid_add_int}
    : int comm_monoid_add);;

let semiring_0_int =
  ({comm_monoid_add_semiring_0 = comm_monoid_add_int;
     mult_zero_semiring_0 = mult_zero_int; semiring_semiring_0 = semiring_int}
    : int semiring_0);;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult;
    power_monoid_mult : 'a power};;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult;
    numeral_semiring_numeral : 'a numeral;
    semiring_semiring_numeral : 'a semiring};;

type 'a zero_neq_one =
  {one_zero_neq_one : 'a one; zero_zero_neq_one : 'a zero};;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral;
    semiring_0_semiring_1 : 'a semiring_0;
    zero_neq_one_semiring_1 : 'a zero_neq_one};;

let monoid_mult_int =
  ({semigroup_mult_monoid_mult = semigroup_mult_int;
     power_monoid_mult = power_int}
    : int monoid_mult);;

let semiring_numeral_int =
  ({monoid_mult_semiring_numeral = monoid_mult_int;
     numeral_semiring_numeral = numeral_int;
     semiring_semiring_numeral = semiring_int}
    : int semiring_numeral);;

let zero_neq_one_int =
  ({one_zero_neq_one = one_int; zero_zero_neq_one = zero_int} :
    int zero_neq_one);;

let semiring_1_int =
  ({semiring_numeral_semiring_1 = semiring_numeral_int;
     semiring_0_semiring_1 = semiring_0_int;
     zero_neq_one_semiring_1 = zero_neq_one_int}
    : int semiring_1);;

type 'a linorder = {order_linorder : 'a order};;

let linorder_int = ({order_linorder = order_int} : int linorder);;

type nat = Zero_nat | Suc of nat;;

let rec equal_nata x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                     | Suc x2, Zero_nat -> false
                     | Suc x2, Suc y2 -> equal_nata x2 y2
                     | Zero_nat, Zero_nat -> true;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                      | Zero_nat, n -> true
and less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
               | n, Zero_nat -> false;;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec equal_chara
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    equal_bool x1 y1 &&
      (equal_bool x2 y2 &&
        (equal_bool x3 y3 &&
          (equal_bool x4 y4 &&
            (equal_bool x5 y5 &&
              (equal_bool x6 y6 && (equal_bool x7 y7 && equal_bool x8 y8))))));;

let equal_char = ({equal = equal_chara} : char equal);;

type 'a itself = Type;;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

let rec plus_nat x0 n = match x0, n with Suc m, n -> plus_nat m (Suc n)
                   | Zero_nat, n -> n;;

let rec times_nat x0 n = match x0, n with Zero_nat, n -> Zero_nat
                    | Suc m, n -> plus_nat n (times_nat m n);;

let one_nat : nat = Suc Zero_nat;;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nat m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nat m m)
    | One -> one_nat;;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of int;;

let rec len_of_bit0 _A uu = times_nat (nat_of_num (Bit0 One)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

type 'a bit1 = Abs_bit1 of int;;

let rec len_of_bit1 _A
  uu = plus_nat (times_nat (nat_of_num (Bit0 One)) (len_of _A Type)) one_nat;;

let rec len0_bit1 _A = ({len_of = len_of_bit1 _A} : 'a bit1 len0);;

type num1 = One_num1;;

let rec len_of_num1 uu = one_nat;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

let one_integera : Big_int.big_int = (Big_int.big_int_of_int 1);;

let one_integer = ({one = one_integera} : Big_int.big_int one);;

let zero_integer = ({zero = Big_int.zero_big_int} : Big_int.big_int zero);;

let zero_neq_one_integer =
  ({one_zero_neq_one = one_integer; zero_zero_neq_one = zero_integer} :
    Big_int.big_int zero_neq_one);;

type storage_inst = SLOAD | SSTORE;;

type sarith_inst = SDIV | SMOD | SGT | SLT | SIGNEXTEND;;

type memory_inst = MLOAD | MSTORE | MSTORE8 | CALLDATACOPY | CODECOPY |
  EXTCODECOPY | MSIZE;;

type 'a word = Word of int;;

type stack_inst = POP | PUSH_N of num1 bit0 bit0 bit0 word list | CALLDATALOAD;;

type arith_inst = ADD | MUL | SUB | DIV | MOD | ADDMOD | MULMOD | EXP | Inst_GT
  | Inst_EQ | Inst_LT | ISZERO | SHA3;;

type misc_inst = STOP | CREATE | CALL | CALLCODE | DELEGATECALL | RETURN |
  SUICIDE;;

type info_inst = ADDRESS | BALANCE | ORIGIN | CALLER | CALLVALUE | CALLDATASIZE
  | CODESIZE | GASPRICE | EXTCODESIZE | BLOCKHASH | COINBASE | TIMESTAMP |
  NUMBER | DIFFICULTY | GASLIMIT | GAS;;

type bits_inst = Inst_AND | Inst_OR | Inst_XOR | Inst_NOT | BYTE;;

type log_inst = LOG0 | LOG1 | LOG2 | LOG3 | LOG4;;

type pc_inst = JUMP | JUMPI | PC | JUMPDEST;;

type inst = Unknown of num1 bit0 bit0 bit0 word | Bits of bits_inst |
  Sarith of sarith_inst | Arith of arith_inst | Info of info_inst |
  Dup of num1 bit0 bit0 word | Memory of memory_inst | Storage of storage_inst |
  Pc of pc_inst | Stack of stack_inst | Swap of num1 bit0 bit0 word |
  Log of log_inst | Misc of misc_inst;;

type llllcompare = LCEq | LCNeq | LCLt | LCLe | LCGt | LCGe;;

type lllllogic = LLAnd | LLOr | LLNot;;

type llllarith = LAPlus | LAMinus | LATimes | LADiv | LAMod | LAAnd | LAOr |
  LAXor | LANot | LAExp;;

type llll = L4L_Str of char list | L4L_Int of int | L4I0 of inst |
  L4I1 of inst * llll | L4I2 of inst * llll * llll |
  L4I3 of inst * llll * llll * llll | L4I4 of inst * llll * llll * llll * llll |
  L4In of inst * llll list | L4Seq of llll list |
  L4Arith of llllarith * llll list | L4Logic of lllllogic * llll list |
  L4Comp of llllcompare * llll * llll | L4When of llll * llll |
  L4Unless of llll * llll | L4If of llll * llll * llll |
  L4For of llll * llll * llll * llll | L4Revert;;

type ('a, 'b) tree = Leaf | Node of ('a, 'b) tree * 'a * 'b * ('a, 'b) tree;;

type cmp_val = LT | EQ | GT;;

type stree = STStr of char list | STStrs of stree list;;

type ll1 = L of inst | LLab of nat | LJmp of nat | LJmpI of nat |
  LSeq of ll1 list;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt = La of 'a * inst | LLaba of 'b * nat |
  LJmpa of 'c * nat * nat | LJmpIa of 'd * nat * nat |
  LSeqa of 'e * ((nat * nat) * ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt) list;;

type 'a program_ext = Program_ext of (int -> inst option) * int * 'a;;

type jump_resolve_result = JSuccess | JFail of nat list | JBump of nat list;;

type 'a constant_ctx_ext =
  Constant_ctx_ext of
    unit program_ext * num1 bit0 bit1 bit0 bit0 bit0 bit0 bit0 word *
      (num1 bit0 bit0 bit0 word list -> bool) * 'a;;

let rec id x = (fun xa -> xa) x;;

let rec cmp (_A1, _A2)
  x y = (if less _A2.order_linorder.preorder_order.ord_preorder x y then LT
          else (if eq _A1 x y then EQ else GT));;

let rec nat = function Pos k -> nat_of_num k
              | Zero_int -> Zero_nat
              | Neg k -> Zero_nat;;

let rec comp f g = (fun x -> f (g x));;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec maps f x1 = match f, x1 with f, [] -> []
               | f, x :: xs -> f x @ maps f xs;;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec uint _A (Word x) = x;;

let rec unat _A w = nat (uint _A w);;

let rec ht = function Leaf -> Zero_nat
             | Node (l, a, h, r) -> h;;

let rec bit_cut_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int
        then (Big_int.zero_big_int, false)
        else (let (r, s) =
                Big_int.quomod_big_int (Big_int.abs_big_int k)
                  (Big_int.abs_big_int (Big_int.big_int_of_int 2))
                in
               ((if Big_int.lt_big_int Big_int.zero_big_int k then r
                  else Big_int.sub_big_int (Big_int.minus_big_int r) s),
                 Big_int.eq_big_int s (Big_int.big_int_of_int 1))));;

let rec char_of_integer
  k = (let (q0, b0) = bit_cut_integer k in
       let (q1, b1) = bit_cut_integer q0 in
       let (q2, b2) = bit_cut_integer q1 in
       let (q3, b3) = bit_cut_integer q2 in
       let (q4, b4) = bit_cut_integer q3 in
       let (q5, b5) = bit_cut_integer q4 in
       let (q6, b6) = bit_cut_integer q5 in
       let a = bit_cut_integer q6 in
       let (_, aa) = a in
        Chara (b0, b1, b2, b3, b4, b5, b6, aa));;

let apos : char = char_of_integer (Big_int.big_int_of_int 39);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (Suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length Zero_nat x;;

let rec of_nat_aux _A inc x1 i = match inc, x1, i with inc, Zero_nat, i -> i
                        | inc, Suc n, i -> of_nat_aux _A inc n (inc i);;

let rec of_nat _A
  n = of_nat_aux _A
        (fun i ->
          plus _A.semiring_numeral_semiring_1.numeral_semiring_numeral.semigroup_add_numeral.plus_semigroup_add
            i (one _A.semiring_numeral_semiring_1.numeral_semiring_numeral.one_numeral))
        n (zero _A.semiring_0_semiring_1.mult_zero_semiring_0.zero_mult_zero);;

let rec divmod_step_int
  l (q, r) =
    (if less_eq_int (Pos l) r
      then (plus_inta (times_inta (Pos (Bit0 One)) q) one_inta,
             minus_int r (Pos l))
      else (times_inta (Pos (Bit0 One)) q, r));;

let rec divmod_int
  x0 x1 = match x0, x1 with
    Bit1 m, Bit1 n ->
      (if less_num m n then (Zero_int, Pos (Bit1 m))
        else divmod_step_int (Bit1 n) (divmod_int (Bit1 m) (Bit0 (Bit1 n))))
    | Bit0 m, Bit1 n ->
        (if less_eq_num m n then (Zero_int, Pos (Bit0 m))
          else divmod_step_int (Bit1 n) (divmod_int (Bit0 m) (Bit0 (Bit1 n))))
    | Bit1 m, Bit0 n ->
        (let (q, r) = divmod_int m n in
          (q, plus_inta (times_inta (Pos (Bit0 One)) r) one_inta))
    | Bit0 m, Bit0 n ->
        (let (q, r) = divmod_int m n in (q, times_inta (Pos (Bit0 One)) r))
    | One, Bit1 n -> (Zero_int, Pos One)
    | One, Bit0 n -> (Zero_int, Pos One)
    | Bit1 m, One -> (Pos (Bit1 m), Zero_int)
    | Bit0 m, One -> (Pos (Bit0 m), Zero_int)
    | One, One -> (Pos One, Zero_int);;

let rec snd (x1, x2) = x2;;

let rec adjust_mod
  l r = (if equal_inta r Zero_int then Zero_int else minus_int l r);;

let rec modulo_int
  k ka = match k, ka with Neg m, Neg n -> uminus_int (snd (divmod_int m n))
    | Pos m, Neg n -> uminus_int (adjust_mod (Pos n) (snd (divmod_int m n)))
    | Neg m, Pos n -> adjust_mod (Pos n) (snd (divmod_int m n))
    | Pos m, Pos n -> snd (divmod_int m n)
    | k, Neg One -> Zero_int
    | k, Pos One -> Zero_int
    | Zero_int, k -> Zero_int
    | k, Zero_int -> k;;

let rec power _A a x1 = match a, x1 with a, Zero_nat -> one _A.one_power
                   | a, Suc n -> times _A.times_power a (power _A a n);;

let rec word_of_int _A
  k = Word (modulo_int k (power power_int (Pos (Bit0 One)) (len_of _A Type)));;

let rec storage_inst_code
  = function
    SLOAD ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | SSTORE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))));;

let rec sarith_inst_code
  = function
    SDIV ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit1 (Bit0 One)))
    | SMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 One)))
    | SGT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 One)))))
    | SLT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 One)))))
    | SIGNEXTEND ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 One))));;

let rec memory_inst_code
  = function
    MLOAD ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | MSTORE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | MSTORE8 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | CALLDATACOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | CODECOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | EXTCODECOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))
    | MSIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));;

let rec plus_word _A a b = word_of_int _A (plus_inta (uint _A a) (uint _A b));;

let rec word8FromNat
  i = word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (of_nat semiring_1_int i);;

let rec byteFromNat x = word8FromNat x;;

let rec stack_inst_code
  = function
    POP ->
      [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
         (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))]
    | PUSH_N lst ->
        (if less_nat (size_list lst) one_nat
          then [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                  (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
                 word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                   Zero_int]
          else (if less_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                     (size_list lst)
                 then [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                         (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))));
                        word_of_int
                          (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                          Zero_int]
                 else [plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                         (byteFromNat (size_list lst))
                         (word_of_int
                           (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                           (Pos (Bit1 (Bit1
(Bit1 (Bit1 (Bit1 (Bit0 One))))))))] @
                        lst))
    | CALLDATALOAD ->
        [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
           (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))];;

let rec arith_inst_code
  = function
    ADD -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) one_inta
    | MUL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 One))
    | SUB ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 One))
    | DIV ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 One)))
    | MOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 One)))
    | ADDMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 One))))
    | MULMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 One))))
    | EXP ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 One))))
    | Inst_GT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit0 One)))))
    | Inst_LT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 One)))))
    | Inst_EQ ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit0 One)))))
    | ISZERO ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit1 (Bit0 One)))))
    | SHA3 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))));;

let rec swap_inst_code
  m = plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (uint (len0_bit0 (len0_bit0 len0_num1)) m))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))));;

let rec misc_inst_code
  = function
    STOP -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) Zero_int
    | CREATE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
    | CALL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
    | CALLCODE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
    | RETURN ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
    | DELEGATECALL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))))
    | SUICIDE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))));;

let rec info_inst_code
  = function
    ADDRESS ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | BALANCE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | ORIGIN ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | CALLVALUE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))
    | CALLDATASIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | CALLER ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | CODESIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | GASPRICE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | EXTCODESIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | BLOCKHASH ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | COINBASE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | TIMESTAMP ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | NUMBER ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | DIFFICULTY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | GASLIMIT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | GAS ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));;

let rec bits_inst_code
  = function
    Inst_AND ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit0 (Bit1 (Bit1 (Bit0 One)))))
    | Inst_OR ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit0 One)))))
    | Inst_XOR ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit1 One)))))
    | Inst_NOT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit1 One)))))
    | BYTE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit1 One)))));;

let rec log_inst_code
  = function
    LOG0 ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))
    | LOG1 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))
    | LOG2 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))
    | LOG3 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))))
    | LOG4 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))))));;

let rec dup_inst_code
  m = plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (uint (len0_bit0 (len0_bit0 len0_num1)) m))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))));;

let rec pc_inst_code
  = function
    JUMP ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Pos (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | JUMPI ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | PC -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
              (Pos (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | JUMPDEST ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))));;

let rec inst_code = function Unknown byte -> [byte]
                    | Bits b -> [bits_inst_code b]
                    | Sarith s -> [sarith_inst_code s]
                    | Arith a -> [arith_inst_code a]
                    | Info i -> [info_inst_code i]
                    | Dup d -> [dup_inst_code d]
                    | Memory m -> [memory_inst_code m]
                    | Storage s -> [storage_inst_code s]
                    | Pc p -> [pc_inst_code p]
                    | Stack s -> stack_inst_code s
                    | Swap s -> [swap_inst_code s]
                    | Log l -> [log_inst_code l]
                    | Misc m -> [misc_inst_code m];;

let rec inst_size i = of_nat semiring_1_int (size_list (inst_code i));;

let rec ilsz = function [] -> Zero_nat
               | h :: t -> plus_nat (nat (inst_size h)) (ilsz t);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> eq _A x y || member _A xs y;;

let rec isWs
  x = member equal_char
        (map char_of_integer
          [(Big_int.big_int_of_int 9); (Big_int.big_int_of_int 10);
            (Big_int.big_int_of_int 11); (Big_int.big_int_of_int 12);
            (Big_int.big_int_of_int 13); (Big_int.big_int_of_int 32)])
        x;;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec foldr f x1 = match f, x1 with f, [] -> id
                | f, x :: xs -> comp (f x) (foldr f xs);;

let rec map_option f x1 = match f, x1 with f, None -> None
                     | f, Some x2 -> Some (f x2);;

let rec those
  = function [] -> Some []
    | x :: xs ->
        (match x with None -> None
          | Some y -> map_option (fun a -> y :: a) (those xs));;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let quote : char = char_of_integer (Big_int.big_int_of_int 34);;

let rec concat xss = foldr (fun a b -> a @ b) xss [];;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec node
  l a r = Node (l, a, plus_nat (max ord_nat (ht l) (ht r)) one_nat, r);;

let rec balL
  l a r =
    (if equal_nata (ht l) (plus_nat (ht r) (nat_of_num (Bit0 One)))
      then (let Node (bl, b, _, br) = l in
             (if less_nat (ht bl) (ht br)
               then (let Node (cl, c, _, cr) = br in
                      node (node bl b cl) c (node cr a r))
               else node bl b (node br a r)))
      else node l a r);;

let rec balR
  l a r =
    (if equal_nata (ht r) (plus_nat (ht l) (nat_of_num (Bit0 One)))
      then (let Node (bl, b, _, br) = r in
             (if less_nat (ht br) (ht bl)
               then (let Node (cl, c, _, cr) = bl in
                      node (node l a cl) c (node cr b br))
               else node (node l a bl) b br))
      else node l a r);;

let rec lookupS
  x0 uu = match x0, uu with [], uu -> None
    | (ah, bh) :: t, a ->
        (if equal_lista equal_char a ah then Some bh else lookupS t a);;

let newline : char = char_of_integer (Big_int.big_int_of_int 10);;

let rec update (_A1, _A2)
  x y xa2 = match x, y, xa2 with
    x, y, Leaf -> Node (Leaf, (x, y), one_nat, Leaf)
    | x, y, Node (l, (a, b), h, r) ->
        (match cmp (_A1, _A2) x a
          with LT -> balL (update (_A1, _A2) x y l) (a, b) r
          | EQ -> Node (l, (x, y), h, r)
          | GT -> balR l (a, b) (update (_A1, _A2) x y r));;

let rec mkConsts
  x0 x1 = match x0, x1 with [], [] -> Some []
    | sh :: st, lh :: lt ->
        (match mkConsts st lt with None -> None
          | Some ft -> Some ((sh, (fun _ -> Some lh)) :: ft))
    | v :: va, [] -> None
    | [], v :: va -> None;;

let hex_parse_table : (char * int) list
  = [(Chara (false, false, false, false, true, true, false, false), Zero_int);
      (Chara (true, false, false, false, true, true, false, false), one_inta);
      (Chara (false, true, false, false, true, true, false, false),
        Pos (Bit0 One));
      (Chara (true, true, false, false, true, true, false, false),
        Pos (Bit1 One));
      (Chara (false, false, true, false, true, true, false, false),
        Pos (Bit0 (Bit0 One)));
      (Chara (true, false, true, false, true, true, false, false),
        Pos (Bit1 (Bit0 One)));
      (Chara (false, true, true, false, true, true, false, false),
        Pos (Bit0 (Bit1 One)));
      (Chara (true, true, true, false, true, true, false, false),
        Pos (Bit1 (Bit1 One)));
      (Chara (false, false, false, true, true, true, false, false),
        Pos (Bit0 (Bit0 (Bit0 One))));
      (Chara (true, false, false, true, true, true, false, false),
        Pos (Bit1 (Bit0 (Bit0 One))));
      (Chara (true, false, false, false, false, false, true, false),
        Pos (Bit0 (Bit1 (Bit0 One))));
      (Chara (true, false, false, false, false, true, true, false),
        Pos (Bit0 (Bit1 (Bit0 One))));
      (Chara (false, true, false, false, false, false, true, false),
        Pos (Bit1 (Bit1 (Bit0 One))));
      (Chara (false, true, false, false, false, true, true, false),
        Pos (Bit1 (Bit1 (Bit0 One))));
      (Chara (true, true, false, false, false, false, true, false),
        Pos (Bit0 (Bit0 (Bit1 One))));
      (Chara (true, true, false, false, false, true, true, false),
        Pos (Bit0 (Bit0 (Bit1 One))));
      (Chara (false, false, true, false, false, false, true, false),
        Pos (Bit1 (Bit0 (Bit1 One))));
      (Chara (false, false, true, false, false, true, true, false),
        Pos (Bit1 (Bit0 (Bit1 One))));
      (Chara (true, false, true, false, false, false, true, false),
        Pos (Bit0 (Bit1 (Bit1 One))));
      (Chara (true, false, true, false, false, true, true, false),
        Pos (Bit0 (Bit1 (Bit1 One))));
      (Chara (false, true, true, false, false, false, true, false),
        Pos (Bit1 (Bit1 (Bit1 One))));
      (Chara (false, true, true, false, false, true, true, false),
        Pos (Bit1 (Bit1 (Bit1 One))))];;

let rec parseHexNumeral
  x0 s f r = match x0, s, f, r with [], s, f, r -> f []
    | h :: t, s, f, r ->
        (match map_of equal_char hex_parse_table h with None -> f (h :: t)
          | Some n -> s n t);;

let rec parseHexSub
  i x1 su fa r = match i, x1, su, fa, r with i, [], su, fa, r -> su i []
    | i, h :: t, su, fa, r ->
        parseHexNumeral (h :: t)
          (fun n l ->
            parseHexSub
              (plus_inta (times_inta (Pos (Bit0 (Bit0 (Bit0 (Bit0 One))))) i) n)
              l su fa r)
          (su i) r;;

let rec parseHex
  x0 su fa r = match x0, su, fa, r with
    h0 :: hx :: h :: t, su, fa, r ->
      (if equal_chara h0
            (Chara (false, false, false, false, true, true, false, false)) &&
            equal_chara hx
              (Chara (false, false, false, true, true, true, true, false))
        then parseHexNumeral (h :: t) (fun n l -> parseHexSub n l su fa r) fa r
        else fa (h0 :: hx :: h :: t))
    | [], su, fa, r -> fa []
    | [v], su, fa, r -> fa [v]
    | [v; vb], su, fa, r -> fa [v; vb];;

let rec is_digit_char
  c = equal_chara c
        (Chara (false, false, false, false, true, true, false, false)) ||
        (equal_chara c
           (Chara (true, false, true, false, true, true, false, false)) ||
          (equal_chara c
             (Chara (true, false, false, false, true, true, false, false)) ||
            (equal_chara c
               (Chara (false, true, true, false, true, true, false, false)) ||
              (equal_chara c
                 (Chara
                   (false, true, false, false, true, true, false, false)) ||
                (equal_chara c
                   (Chara
                     (true, true, true, false, true, true, false, false)) ||
                  (equal_chara c
                     (Chara
                       (true, true, false, false, true, true, false, false)) ||
                    (equal_chara c
                       (Chara
                         (false, false, false, true, true, true, false,
                           false)) ||
                      (equal_chara c
                         (Chara
                           (false, false, true, false, true, true, false,
                             false)) ||
                        equal_chara c
                          (Chara
                            (true, false, false, true, true, true, false,
                              false))))))))));;

let rec char_to_digit
  c = (if equal_chara c
            (Chara (false, false, false, false, true, true, false, false))
        then Zero_nat
        else (if equal_chara c
                   (Chara (true, false, false, false, true, true, false, false))
               then one_nat
               else (if equal_chara c
                          (Chara
                            (false, true, false, false, true, true, false,
                              false))
                      then nat_of_num (Bit0 One)
                      else (if equal_chara c
                                 (Chara
                                   (true, true, false, false, true, true, false,
                                     false))
                             then nat_of_num (Bit1 One)
                             else (if equal_chara c
(Chara (false, false, true, false, true, true, false, false))
                                    then nat_of_num (Bit0 (Bit0 One))
                                    else (if equal_chara c
       (Chara (true, false, true, false, true, true, false, false))
   then nat_of_num (Bit1 (Bit0 One))
   else (if equal_chara c
              (Chara (false, true, true, false, true, true, false, false))
          then nat_of_num (Bit0 (Bit1 One))
          else (if equal_chara c
                     (Chara (true, true, true, false, true, true, false, false))
                 then nat_of_num (Bit1 (Bit1 One))
                 else (if equal_chara c
                            (Chara
                              (false, false, false, true, true, true, false,
                                false))
                        then nat_of_num (Bit0 (Bit0 (Bit0 One)))
                        else (if equal_chara c
                                   (Chara
                                     (true, false, false, true, true, true,
                                       false, false))
                               then nat_of_num (Bit1 (Bit0 (Bit0 One)))
                               else nat_of_num
                                      (Bit0 (Bit1 (Bit0 One)))))))))))));;

let rec parseNumeral
  x0 s f r = match x0, s, f, r with [], s, f, r -> f []
    | h :: t, s, f, r ->
        (if is_digit_char h then s (of_nat semiring_1_int (char_to_digit h)) t
          else f (h :: t));;

let rec parseIntSub
  i x1 su fa r = match i, x1, su, fa, r with i, [], su, fa, r -> su i []
    | i, h :: t, su, fa, r ->
        parseNumeral (h :: t)
          (fun n l ->
            parseIntSub
              (plus_inta (times_inta (Pos (Bit0 (Bit1 (Bit0 One)))) i) n) l su
              fa r)
          (su i) r;;

let rec parseInt
  x0 su fa r = match x0, su, fa, r with [], su, fa, r -> fa []
    | h :: t, su, fa, r ->
        parseNumeral (h :: t) (fun n l -> parseIntSub n l su fa r) fa r;;

let rec lookup (_A1, _A2)
  xa0 x = match xa0, x with Leaf, x -> None
    | Node (l, (a, b), uu, r), x ->
        (match cmp (_A1, _A2) x a with LT -> lookup (_A1, _A2) l x
          | EQ -> Some b | GT -> lookup (_A1, _A2) r x);;

let rec of_bool _A = function true -> one _A.one_zero_neq_one
                     | false -> zero _A.zero_zero_neq_one;;

let rec integer_of_char
  (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
    Big_int.add_big_int
      (Big_int.mult_big_int
        (Big_int.add_big_int
          (Big_int.mult_big_int
            (Big_int.add_big_int
              (Big_int.mult_big_int
                (Big_int.add_big_int
                  (Big_int.mult_big_int
                    (Big_int.add_big_int
                      (Big_int.mult_big_int
                        (Big_int.add_big_int
                          (Big_int.mult_big_int
                            (Big_int.add_big_int
                              (Big_int.mult_big_int
                                (of_bool zero_neq_one_integer b7)
                                (Big_int.big_int_of_int 2))
                              (of_bool zero_neq_one_integer b6))
                            (Big_int.big_int_of_int 2))
                          (of_bool zero_neq_one_integer b5))
                        (Big_int.big_int_of_int 2))
                      (of_bool zero_neq_one_integer b4))
                    (Big_int.big_int_of_int 2))
                  (of_bool zero_neq_one_integer b3))
                (Big_int.big_int_of_int 2))
              (of_bool zero_neq_one_integer b2))
            (Big_int.big_int_of_int 2))
          (of_bool zero_neq_one_integer b1))
        (Big_int.big_int_of_int 2))
      (of_bool zero_neq_one_integer b0);;

let rec implode
  cs = (let ks = (map integer_of_char
                   cs) in let res = Bytes.create (List.length ks) in let rec imp i = function | [] -> res | k :: ks ->
      let l = Big_int.int_of_big_int k in if 0 <= l && l < 128 then Bytes.set res i (Char.chr l) else failwith "Non-ASCII character in literal"; imp (i + 1) ks in imp 0 ks);;

let rec fst (x1, x2) = x1;;

let rec adjust_div
  (q, r) =
    plus_inta q (of_bool zero_neq_one_int (not (equal_inta r Zero_int)));;

let rec divide_int
  k ka = match k, ka with Neg m, Neg n -> fst (divmod_int m n)
    | Pos m, Neg n -> uminus_int (adjust_div (divmod_int m n))
    | Neg m, Pos n -> uminus_int (adjust_div (divmod_int m n))
    | Pos m, Pos n -> fst (divmod_int m n)
    | k, Neg One -> uminus_int k
    | k, Pos One -> k
    | Zero_int, k -> Zero_int
    | k, Zero_int -> Zero_int;;

let rec log256floor
  x = (if less_eq_int x
            (Pos (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))))
        then Zero_int
        else plus_inta one_inta
               (log256floor
                 (divide_int x
                   (Pos (Bit0 (Bit0 (Bit0 (Bit0
    (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))));;

let rec run_parse
  p donea dfl s =
    p s (fun x _ -> donea x) (fun _ -> dfl)
      (fun sa _ _ -> run_parse p donea dfl sa);;

let rec make
  program_content program_length =
    Program_ext (program_content, program_length, ());;

let rec int_to_bytes
  n = (let na =
         divide_int n
           (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
         in
       let mo =
         modulo_int n
           (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
         in
        (if equal_inta na Zero_int then [byteFromNat (nat mo)]
          else byteFromNat (nat mo) :: int_to_bytes na));;

let rec intToBytes i = rev (int_to_bytes i);;

let rec word160FromNatural
  i = word_of_int
        (len0_bit0
          (len0_bit0
            (len0_bit0
              (len0_bit0 (len0_bit0 (len0_bit1 (len0_bit0 len0_num1)))))))
        (of_nat semiring_1_int i);;

let w160_0 : num1 bit0 bit1 bit0 bit0 bit0 bit0 bit0 word
  = word160FromNatural Zero_nat;;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec sgn_integer
  k = (if Big_int.eq_big_int k Big_int.zero_big_int then Big_int.zero_big_int
        else (if Big_int.lt_big_int k Big_int.zero_big_int
               then (Big_int.minus_big_int (Big_int.big_int_of_int 1))
               else (Big_int.big_int_of_int 1)));;

let rec apsnd f (x, y) = (x, f y);;

let rec divmod_integer
  k l = (if Big_int.eq_big_int k Big_int.zero_big_int
          then (Big_int.zero_big_int, Big_int.zero_big_int)
          else (if Big_int.eq_big_int l Big_int.zero_big_int
                 then (Big_int.zero_big_int, k)
                 else comp (comp apsnd Big_int.mult_big_int) sgn_integer l
                        (if Big_int.eq_big_int (sgn_integer k) (sgn_integer l)
                          then Big_int.quomod_big_int (Big_int.abs_big_int k)
                                 (Big_int.abs_big_int l)
                          else (let (r, s) =
                                  Big_int.quomod_big_int (Big_int.abs_big_int k)
                                    (Big_int.abs_big_int l)
                                  in
                                 (if Big_int.eq_big_int s Big_int.zero_big_int
                                   then (Big_int.minus_big_int r,
  Big_int.zero_big_int)
                                   else (Big_int.sub_big_int
   (Big_int.minus_big_int r) (Big_int.big_int_of_int 1),
  Big_int.sub_big_int (Big_int.abs_big_int l) s))))));;

let rec nat_of_integer
  k = (if Big_int.le_big_int k Big_int.zero_big_int then Zero_nat
        else (let (l, j) = divmod_integer k (Big_int.big_int_of_int 2) in
              let la = nat_of_integer l in
              let lb = plus_nat la la in
               (if Big_int.eq_big_int j Big_int.zero_big_int then lb
                 else plus_nat lb one_nat)));;

let rec truncate_string_sub
  x0 n = match x0, n with
    [], n ->
      (if equal_nata n Zero_nat then []
        else byteFromNat Zero_nat ::
               truncate_string_sub [] (minus_nat n one_nat))
    | h :: t, n ->
        (if equal_nata n Zero_nat then []
          else byteFromNat (nat_of_integer (integer_of_char h)) ::
                 truncate_string_sub t (minus_nat n one_nat));;

let rec truncate_string
  s = truncate_string_sub s
        (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))));;

let rec l4constSize
  = function
    L4L_Str s ->
      Some (of_nat semiring_1_int
             (max ord_nat (size_list s) (size_list (truncate_string s))))
    | L4L_Int i -> Some (of_nat semiring_1_int (size_list (intToBytes i)))
    | L4I0 v -> None
    | L4I1 (v, va) -> None
    | L4I2 (v, va, vb) -> None
    | L4I3 (v, va, vb, vc) -> None
    | L4I4 (v, va, vb, vc, vd) -> None
    | L4In (v, va) -> None
    | L4Seq v -> None
    | L4Arith (v, va) -> None
    | L4Logic (v, va) -> None
    | L4Comp (v, va, vb) -> None
    | L4When (v, va) -> None
    | L4Unless (v, va) -> None
    | L4If (v, va, vb) -> None
    | L4For (v, va, vb, vc) -> None
    | L4Revert -> None;;

let rec stree_append x0 uu = match x0, uu with STStr x, uu -> STStr x
                       | STStrs xs, s -> STStrs (xs @ [s]);;

let rec llll_parse
  x0 uu uv uw ux = match x0, uu, uv, uw, ux with [], uu, uv, uw, ux -> None
    | h :: t, token, parsed, isComment, isQuote ->
        (if isComment
          then (if equal_chara h newline
                 then (if not (null token)
                        then (match parsed with [] -> None
                               | ph :: pt ->
                                 llll_parse t []
                                   (stree_append ph (STStr token) :: pt) false
                                   false)
                        else llll_parse t [] parsed false false)
                 else llll_parse t token parsed true false)
          else (if isQuote
                 then (if equal_chara h quote
                        then (if null token then None
                               else (match parsed with [] -> None
                                      | ph :: pt ->
llll_parse t [] (stree_append ph (STStr (token @ [h])) :: pt) false false))
                        else llll_parse t (token @ [h]) parsed false true)
                 else (if equal_chara h
                            (Chara
                              (true, true, false, true, true, true, false,
                                false))
                        then llll_parse t token parsed true false
                        else (if equal_chara h quote
                               then llll_parse t (token @ [h]) parsed false true
                               else (if equal_chara h
  (Chara (false, false, false, true, false, true, false, false))
                                      then llll_parse t token
     (STStrs [] :: parsed) false false
                                      else (if equal_chara h
         (Chara (true, false, false, true, false, true, false, false))
     then (match parsed with [] -> None
            | [ph] ->
              (if not (null token) then Some (stree_append ph (STStr token))
                else Some ph)
            | ph :: ph2 :: pt ->
              (if not (null token)
                then llll_parse t []
                       (stree_append ph2 (stree_append ph (STStr token)) :: pt)
                       false false
                else llll_parse t [] (stree_append ph2 ph :: pt) false false))
     else (if isWs h
            then (if not (null token)
                   then (match parsed with [] -> None
                          | ph :: pt ->
                            llll_parse t []
                              (stree_append ph (STStr token) :: pt) false false)
                   else llll_parse t [] parsed false false)
            else llll_parse t (token @ [h]) parsed false false)))))));;

let rec llll_parse0 s = llll_parse s [] [] false false;;

let rec run_parse_opt p f s = run_parse p f None s;;

let rec run_parse_opta p s = run_parse_opt p (fun a -> Some a) s;;

let rec parseStringChar
  x0 s f r = match x0, s, f, r with [], s, f, r -> f []
    | h :: t, s, f, r -> (if equal_chara h quote then f (h :: t) else s [h] t);;

let rec parseStringSub
  s x1 su fa r = match s, x1, su, fa, r with s, [], su, fa, r -> fa []
    | s, h :: t, su, fa, r ->
        (if equal_chara h quote then (if null s then fa (h :: t) else su s t)
          else parseStringChar (h :: t)
                 (fun nextc l -> parseStringSub (s @ nextc) l su fa r) fa r);;

let rec parseString
  x0 su fa r = match x0, su, fa, r with [], su, fa, r -> fa []
    | h :: t, su, fa, r ->
        (if equal_chara h quote
          then parseStringChar t (fun s l -> parseStringSub s l su fa r) fa r
          else fa (h :: t));;

let rec llll_parse1
  ft x1 = match ft, x1 with
    ft, STStr s ->
      (match run_parse_opta parseHex s
        with None ->
          (match run_parse_opta parseInt s
            with None ->
              (match run_parse_opta parseString s
                with None ->
                  (match lookupS ft s with None -> None
                    | Some f ->
                      (match f [] with None -> None
                        | Some l -> Some (l, (None, ft))))
                | Some sa -> Some (L4L_Str sa, (None, ft)))
            | Some n -> Some (L4L_Int n, (None, ft)))
        | Some n -> Some (L4L_Int n, (None, ft)))
    | ft, STStrs (h :: t) ->
        (match h
          with STStr hs ->
            (if equal_lista equal_char hs
                  [Chara (false, false, true, false, false, true, true, false);
                    Chara (true, false, true, false, false, true, true, false);
                    Chara (false, true, true, false, false, true, true, false)]
              then (match t with [] -> None | [STStr _] -> None
                     | [STStr h2; STStr listaa] ->
                       (match llll_parse1_def h2 ft [] [STStr listaa]
                         with None -> None | Some a -> Some a)
                     | STStr _ :: STStr _ :: _ :: _ -> None
                     | [STStr h2; STStrs l] ->
                       (match llll_parse1_def h2 ft [] [STStrs l]
                         with None -> None | Some a -> Some a)
                     | [STStr h2; STStrs l; d] ->
                       (match llll_parse1_def h2 ft [] (l @ [d])
                         with None -> None | Some a -> Some a)
                     | STStr _ :: STStrs _ :: _ :: _ :: _ -> None
                     | STStrs _ :: _ -> None)
              else (if equal_lista equal_char hs
                         [Chara (false, true, false, false, true, true, true,
                                  false);
                           Chara (true, false, true, false, false, true, true,
                                   false);
                           Chara (false, false, true, false, true, true, true,
                                   false);
                           Chara (true, false, true, false, true, true, true,
                                   false);
                           Chara (false, true, false, false, true, true, true,
                                   false);
                           Chara (false, true, true, true, false, true, true,
                                   false);
                           Chara (false, false, true, true, false, true, true,
                                   false);
                           Chara (false, false, true, true, false, true, true,
                                   false);
                           Chara (false, false, true, true, false, true, true,
                                   false)]
                     then (match t with [] -> None
                            | [paysrc] ->
                              (match llll_parse1 ft paysrc with None -> None
                                | Some (ls, (None, fta)) ->
                                  Some (L4Seq [], (Some ls, fta))
                                | Some (_, (Some _, _)) -> None)
                            | _ :: _ :: _ -> None)
                     else (match lookupS ft hs with None -> None
                            | Some f ->
                              (match llll_parse1_args ft t with None -> None
                                | Some (ls, (x, fta)) ->
                                  (match f ls with None -> None
                                    | Some l -> Some (l, (x, fta)))))))
          | STStrs _ -> None)
    | ft, STStrs [] -> None
and llll_parse1_def
  s ft vt x3 = match s, ft, vt, x3 with s, ft, vt, [] -> None
    | name, ft, vt, [h] ->
        (match name with [] -> None | [_] -> None
          | hdchr :: aa :: lista ->
            (if not (equal_chara hdchr apos) then None
              else Some (L4Seq [],
                          (None,
                            (aa :: lista,
                              (fun l ->
                                (match mkConsts vt (rev l) with None -> None
                                  | Some fta ->
                                    (match llll_parse1 (fta @ ft) h
                                      with None -> None
                                      | Some (la, (_, _)) -> Some la)))) ::
                              ft))))
    | name, ft, vt, h :: v :: va ->
        (match h with STStr vb -> llll_parse1_def name ft (vb :: vt) (v :: va)
          | STStrs _ -> None)
and llll_parse1_args
  ft x1 = match ft, x1 with ft, [] -> Some ([], (None, ft))
    | ft, [h] ->
        (match llll_parse1 ft h with None -> None
          | Some (l, (x, fta)) -> Some ([l], (x, fta)))
    | ft, h :: v :: va ->
        (match llll_parse1 ft h with None -> None
          | Some (ha, (None, fta)) ->
            (match llll_parse1_args fta (v :: va) with None -> None
              | Some (t, (x, ftb)) -> Some (ha :: t, (x, ftb)))
          | Some (ha, (Some pay, fta)) -> Some ([ha], (Some pay, fta)));;

let rec makeLogical i = [i; L (Arith ISZERO); L (Arith ISZERO)];;

let rec divmod_nat
  m n = (if equal_nata n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let a = divmod_nat (minus_nat m n) n in
                let (q, aa) = a in
                 (Suc q, aa)));;

let rec mynth x0 uu = match x0, uu with [], uu -> None
                | h :: t, Zero_nat -> h
                | h :: t, Suc v -> mynth t (minus_nat (Suc v) one_nat);;

let rec hexwrite1
  c = (if equal_nata c Zero_nat
        then Chara (false, false, false, false, true, true, false, false)
        else (if equal_nata c one_nat
               then Chara (true, false, false, false, true, true, false, false)
               else (if equal_nata c (nat_of_num (Bit0 One))
                      then Chara (false, true, false, false, true, true, false,
                                   false)
                      else (if equal_nata c (nat_of_num (Bit1 One))
                             then Chara (true, true, false, false, true, true,
  false, false)
                             else (if equal_nata c
(nat_of_num (Bit0 (Bit0 One)))
                                    then Chara
   (false, false, true, false, true, true, false, false)
                                    else (if equal_nata c
       (nat_of_num (Bit1 (Bit0 One)))
   then Chara (true, false, true, false, true, true, false, false)
   else (if equal_nata c (nat_of_num (Bit0 (Bit1 One)))
          then Chara (false, true, true, false, true, true, false, false)
          else (if equal_nata c (nat_of_num (Bit1 (Bit1 One)))
                 then Chara (true, true, true, false, true, true, false, false)
                 else (if equal_nata c (nat_of_num (Bit0 (Bit0 (Bit0 One))))
                        then Chara (false, false, false, true, true, true,
                                     false, false)
                        else (if equal_nata c
                                   (nat_of_num (Bit1 (Bit0 (Bit0 One))))
                               then Chara (true, false, false, true, true, true,
    false, false)
                               else (if equal_nata c
  (nat_of_num (Bit0 (Bit1 (Bit0 One))))
                                      then Chara
     (true, false, false, false, false, true, true, false)
                                      else (if equal_nata c
         (nat_of_num (Bit1 (Bit1 (Bit0 One))))
     then Chara (false, true, false, false, false, true, true, false)
     else (if equal_nata c (nat_of_num (Bit0 (Bit0 (Bit1 One))))
            then Chara (true, true, false, false, false, true, true, false)
            else (if equal_nata c (nat_of_num (Bit1 (Bit0 (Bit1 One))))
                   then Chara (false, false, true, false, false, true, true,
                                false)
                   else (if equal_nata c (nat_of_num (Bit0 (Bit1 (Bit1 One))))
                          then Chara (true, false, true, false, false, true,
                                       true, false)
                          else (if equal_nata c
                                     (nat_of_num (Bit1 (Bit1 (Bit1 One))))
                                 then Chara
(false, true, true, false, false, true, true, false)
                                 else failwith "undefined"))))))))))))))));;

let rec hexwrite2
  w = (let (d, m) =
         divmod_nat (unat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) w)
           (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))
         in
        (hexwrite1 d, hexwrite1 m));;

let rec hexwrite
  = function [] -> []
    | h :: t -> (let (c1, c2) = hexwrite2 h in c1 :: c2 :: hexwrite t);;

let rec program_of_lst
  lst program_content_formatter =
    Program_ext
      (program_content_formatter lst, of_nat semiring_1_int (size_list lst),
        ());;

let rec llll_compile
  = function L4L_Str s -> L (Stack (PUSH_N (truncate_string s)))
    | L4L_Int i -> L (Stack (PUSH_N (intToBytes i)))
    | L4I0 i -> L i
    | L4I1 (i, l) -> LSeq [llll_compile l; L i]
    | L4I2 (i, l1, l2) -> LSeq [llll_compile l2; llll_compile l1; L i]
    | L4I3 (i, l1, l2, l3) ->
        LSeq [llll_compile l3; llll_compile l2; llll_compile l1; L i]
    | L4I4 (i, l1, l2, l3, l4) ->
        LSeq [llll_compile l4; llll_compile l3; llll_compile l2;
               llll_compile l1; L i]
    | L4In (i, ls) -> LSeq (map llll_compile (rev ls) @ [L i])
    | L4Seq l -> LSeq (map llll_compile l)
    | L4When (c, l) ->
        LSeq [llll_compile c; L (Arith ISZERO); LJmpI Zero_nat; llll_compile l;
               LLab Zero_nat]
    | L4Unless (c, l) ->
        LSeq [llll_compile c; LJmpI Zero_nat; llll_compile l; LLab Zero_nat]
    | L4If (c, l1, l2) ->
        LSeq [LSeq [llll_compile c; LJmpI Zero_nat; llll_compile l2;
                     LJmp one_nat; LLab Zero_nat; llll_compile l1;
                     LLab one_nat]]
    | L4For (i, p, post, body) ->
        LSeq [LSeq [llll_compile i;
                     LSeq [LLab Zero_nat; llll_compile p; L (Arith ISZERO);
                            LJmpI one_nat; llll_compile body; llll_compile post;
                            LJmp Zero_nat];
                     LLab Zero_nat]]
    | L4Revert -> LSeq [LLab Zero_nat; LJmp Zero_nat]
    | L4Arith (LAPlus, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith ADD)])
    | L4Arith (LAExp, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith EXP)])
    | L4Arith (LADiv, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith DIV)])
    | L4Arith (LAMinus, ls) ->
        LSeq (map llll_compile (rev ls) @ [L (Arith SUB)])
    | L4Arith (LAOr, ls) ->
        LSeq (map llll_compile (rev ls) @ [L (Bits Inst_OR)])
    | L4Arith (LAAnd, ls) ->
        LSeq (map llll_compile (rev ls) @ [L (Bits Inst_AND)])
    | L4Arith (LANot, ls) ->
        LSeq (map llll_compile (rev ls) @ [L (Bits Inst_NOT)])
    | L4Logic (LLOr, ls) ->
        (let res = map llll_compile (rev ls) in
          LSeq (maps makeLogical res @ [L (Bits Inst_OR)]))
    | L4Logic (LLAnd, ls) ->
        (let res = map llll_compile (rev ls) in
          LSeq (maps makeLogical res @ [L (Bits Inst_AND)]))
    | L4Logic (LLNot, ls) ->
        LSeq (map llll_compile (rev ls) @ [L (Arith ISZERO)])
    | L4Comp (LCEq, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith Inst_EQ)]
    | L4Comp (LCNeq, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith Inst_EQ);
               L (Arith ISZERO)]
    | L4Comp (LCGt, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith Inst_GT)]
    | L4Comp (LCGe, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith ISZERO);
               L (Arith Inst_LT)]
    | L4Comp (LCLt, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith Inst_LT)]
    | L4Comp (LCLe, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith ISZERO);
               L (Arith Inst_GT)];;

let rec index x0 n = match x0, n with [], n -> None
                | x :: xs, Zero_nat -> Some x
                | x :: xs, Suc n -> index xs n;;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let rec mypeel
  = function [] -> Some []
    | None :: uu -> None
    | Some h :: t ->
        (match mypeel t with None -> None | Some ta -> Some (h :: ta));;

let rec zero_word _A = word_of_int _A Zero_int;;

let rec nat_to_bytes
  n = (match
        divmod_nat n
          (nat_of_num
            (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
        with (Zero_nat, mo) -> [byteFromNat mo]
        | (Suc na, mo) -> byteFromNat mo :: nat_to_bytes (Suc na));;

let rec output_address n = rev (nat_to_bytes n);;

let base_interlude_size : nat = nat_of_num (Bit1 (Bit0 (Bit0 One)));;

let rec makeInterlude
  startbytes endbytes prelude payload =
    prelude @
      [Stack (PUSH_N (output_address (ilsz payload)))] @
        [Dup (zero_word (len0_bit0 (len0_bit0 len0_num1)))] @
          [Stack (PUSH_N
                   (output_address
                     (plus_nat
                       (plus_nat (plus_nat (ilsz prelude) startbytes) endbytes)
                       base_interlude_size)))] @
            [Stack (PUSH_N (output_address Zero_nat))] @
              [Memory CODECOPY] @
                [Stack (PUSH_N (output_address Zero_nat))] @
                  [Misc RETURN] @ payload;;

let rec equal_word _A k l = equal_inta (uint _A k) (uint _A l);;

let rec inst_valid
  = function
    Unknown x ->
      equal_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) x
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Pos (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))))
    | Pc uu -> false
    | Misc RETURN -> true
    | Misc STOP -> true
    | Misc CREATE -> false
    | Misc CALL -> false
    | Misc CALLCODE -> false
    | Misc DELEGATECALL -> false
    | Misc SUICIDE -> false
    | Info CODESIZE -> false
    | Memory CODECOPY -> false
    | Bits v -> true
    | Sarith v -> true
    | Arith v -> true
    | Info ADDRESS -> true
    | Info BALANCE -> true
    | Info ORIGIN -> true
    | Info CALLER -> true
    | Info CALLVALUE -> true
    | Info CALLDATASIZE -> true
    | Info GASPRICE -> true
    | Info EXTCODESIZE -> true
    | Info BLOCKHASH -> true
    | Info COINBASE -> true
    | Info TIMESTAMP -> true
    | Info NUMBER -> true
    | Info DIFFICULTY -> true
    | Info GASLIMIT -> true
    | Info GAS -> true
    | Dup v -> true
    | Memory MLOAD -> true
    | Memory MSTORE -> true
    | Memory MSTORE8 -> true
    | Memory CALLDATACOPY -> true
    | Memory EXTCODECOPY -> true
    | Memory MSIZE -> true
    | Storage v -> true
    | Stack v -> true
    | Swap v -> true
    | Log v -> true;;

let rec ll1_valid = function L i -> inst_valid i
                    | LSeq is -> list_all ll1_valid is
                    | LLab v -> true
                    | LJmp v -> true
                    | LJmpI v -> true;;

let rec ll3_bump
  n x1 = match n, x1 with
    n, ((xa, x), LSeqa (e, lsdec)) :: ls ->
      ((plus_nat xa n, plus_nat x n), LSeqa (e, ll3_bump n lsdec)) ::
        ll3_bump n ls
    | n, ((xa, x), La (v, va)) :: ls ->
        ((plus_nat xa n, plus_nat x n), La (v, va)) :: ll3_bump n ls
    | n, ((xa, x), LLaba (v, va)) :: ls ->
        ((plus_nat xa n, plus_nat x n), LLaba (v, va)) :: ll3_bump n ls
    | n, ((xa, x), LJmpa (v, va, vb)) :: ls ->
        ((plus_nat xa n, plus_nat x n), LJmpa (v, va, vb)) :: ll3_bump n ls
    | n, ((xa, x), LJmpIa (v, va, vb)) :: ls ->
        ((plus_nat xa n, plus_nat x n), LJmpIa (v, va, vb)) :: ll3_bump n ls
    | n, [] -> [];;

let rec ll3_init = function (x, La (e, i)) -> (x, La (e, i))
                   | (x, LLaba (e, idx)) -> (x, LLaba (false, idx))
                   | (x, LJmpa (e, idx, s)) -> (x, LJmpa (e, idx, s))
                   | (x, LJmpIa (e, idx, s)) -> (x, LJmpIa (e, idx, s))
                   | (x, LSeqa (e, ls)) -> (x, LSeqa ([], map ll3_init ls));;

let rec ll4_init = function (x, La (e, i)) -> (x, La (e, i))
                   | (x, LLaba (e, idx)) -> (x, LLaba (e, idx))
                   | (x, LJmpa (e, idx, s)) -> (x, LJmpa (Zero_nat, idx, s))
                   | (x, LJmpIa (e, idx, s)) -> (x, LJmpIa (Zero_nat, idx, s))
                   | (x, LSeqa (e, ls)) -> (x, LSeqa (e, map ll4_init ls));;

let rec ll_phase1
  x0 i = match x0, i with
    L inst, i ->
      (((i, plus_nat i (nat (inst_size inst))), La ((), inst)),
        plus_nat i (nat (inst_size inst)))
    | LLab idx, i ->
        (((i, plus_nat i one_nat), LLaba ((), idx)), plus_nat one_nat i)
    | LJmp idx, i ->
        (((i, plus_nat (nat_of_num (Bit0 One)) i), LJmpa ((), idx, Zero_nat)),
          plus_nat (nat_of_num (Bit0 One)) i)
    | LJmpI idx, i ->
        (((i, plus_nat (nat_of_num (Bit0 One)) i), LJmpIa ((), idx, Zero_nat)),
          plus_nat (nat_of_num (Bit0 One)) i)
    | LSeq ls, i ->
        (let (lsa, ia) = ll_phase1_seq ls i in (((i, ia), LSeqa ((), lsa)), ia))
and ll_phase1_seq
  x0 i = match x0, i with [], i -> ([], i)
    | h :: t, i -> (let (ha, ia) = ll_phase1 h i in
                    let a = ll_phase1_seq t ia in
                    let (ta, aa) = a in
                     (ha :: ta, aa));;

let rec ll_pass1 l = fst (ll_phase1 l Zero_nat);;

let rec inst_code_clean
  = function
    Stack (PUSH_N lst) ->
      (match stack_inst_code (PUSH_N lst) with [] -> None | h :: _ -> Some [h])
    | Unknown v -> Some (inst_code (Unknown v))
    | Bits v -> Some (inst_code (Bits v))
    | Sarith v -> Some (inst_code (Sarith v))
    | Arith v -> Some (inst_code (Arith v))
    | Info v -> Some (inst_code (Info v))
    | Dup v -> Some (inst_code (Dup v))
    | Memory v -> Some (inst_code (Memory v))
    | Storage v -> Some (inst_code (Storage v))
    | Pc v -> Some (inst_code (Pc v))
    | Stack POP -> Some (inst_code (Stack POP))
    | Stack CALLDATALOAD -> Some (inst_code (Stack CALLDATALOAD))
    | Swap v -> Some (inst_code (Swap v))
    | Log v -> Some (inst_code (Log v))
    | Misc v -> Some (inst_code (Misc v));;

let rec codegen_clean
  = function [] -> Some []
    | h :: t ->
        (match inst_code_clean h with None -> None
          | Some wl ->
            (match codegen_clean t with None -> None
              | Some wls -> Some (wl @ wls)));;

let rec ellecompilev_il_wl il = codegen_clean il;;

let rec program_content
  (Program_ext (program_content, program_length, more)) = program_content;;

let rec get_instsa
  p start tot =
    (if less_eq_int tot Zero_int then Some []
      else (match program_content p start with None -> None
             | Some i ->
               (match
                 get_instsa p (plus_inta start one_inta)
                   (minus_int tot one_inta)
                 with None -> None | Some il -> Some (i :: il))));;

let rec cctx_program
  (Constant_ctx_ext (cctx_program, cctx_this, cctx_hash_filter, more)) =
    cctx_program;;

let rec program_length
  (Program_ext (program_content, program_length, more)) = program_length;;

let rec get_insts
  c = get_instsa (cctx_program c) Zero_int (program_length (cctx_program c));;

let rec ellecompilev_cc_il c = get_insts c;;

let rec program_list_of_lst_validate
  = function [] -> Some []
    | Stack (PUSH_N bytes) :: rest ->
        (if less_eq_nat (size_list bytes) Zero_nat then None
          else (if less_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
                     (size_list bytes)
                 then None
                 else (match program_list_of_lst_validate rest with None -> None
                        | Some resta ->
                          Some ([Stack (PUSH_N bytes)] @
                                 map (fun a -> Unknown a) bytes @ resta))))
    | Unknown v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Unknown v :: resta))
    | Bits v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Bits v :: resta))
    | Sarith v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Sarith v :: resta))
    | Arith v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Arith v :: resta))
    | Info v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Info v :: resta))
    | Dup v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Dup v :: resta))
    | Memory v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Memory v :: resta))
    | Storage v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Storage v :: resta))
    | Pc v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Pc v :: resta))
    | Stack POP :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Stack POP :: resta))
    | Stack CALLDATALOAD :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Stack CALLDATALOAD :: resta))
    | Swap v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Swap v :: resta))
    | Log v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Log v :: resta))
    | Misc v :: rest ->
        (match program_list_of_lst_validate rest with None -> None
          | Some resta -> Some (Misc v :: resta));;

let rec cctx_program_update
  cctx_programa
    (Constant_ctx_ext (cctx_program, cctx_this, cctx_hash_filter, more)) =
    Constant_ctx_ext
      (cctx_programa cctx_program, cctx_this, cctx_hash_filter, more);;

let rec codegen_check
  = function (uu, La (uv, i)) -> Some [i]
    | (uw, LLaba (ux, uy)) -> Some [Pc JUMPDEST]
    | (uz, LJmpa (a, va, s)) ->
        (if equal_nata (size_list (output_address a)) s
          then Some [Stack (PUSH_N (output_address a)); Pc JUMP] else None)
    | (vb, LJmpIa (a, vc, s)) ->
        (if equal_nata (size_list (output_address a)) s
          then Some [Stack (PUSH_N (output_address a)); Pc JUMPI] else None)
    | (vd, LSeqa (ve, ls)) ->
        (match those (map codegen_check ls) with None -> None
          | Some lsa -> Some (concat lsa));;

let rec ll4_load_lst_validate
  cc t =
    (match codegen_check t with None -> None
      | Some tc ->
        (match program_list_of_lst_validate tc with None -> None
          | Some l ->
            Some (cctx_program_update
                   (fun _ ->
                     make (fun i -> index l (nat i))
                       (of_nat semiring_1_int (size_list l)))
                   cc)));;

let rec store_byte_list_in_program
  uu x1 orig = match uu, x1, orig with uu, [], orig -> orig
    | pos, h :: t, orig ->
        store_byte_list_in_program (plus_inta pos one_inta) t
          (update (equal_int, linorder_int) pos (Unknown h) orig);;

let rec program_avl_of_lst
  uu x1 = match uu, x1 with uu, [] -> Leaf
    | pos, Stack (PUSH_N bytes) :: rest ->
        store_byte_list_in_program (plus_inta pos one_inta) bytes
          (update (equal_int, linorder_int) pos (Stack (PUSH_N bytes))
            (program_avl_of_lst
              (plus_inta (plus_inta pos one_inta)
                (of_nat semiring_1_int (size_list bytes)))
              rest))
    | pos, Unknown v :: rest ->
        update (equal_int, linorder_int) pos (Unknown v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Bits v :: rest ->
        update (equal_int, linorder_int) pos (Bits v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Sarith v :: rest ->
        update (equal_int, linorder_int) pos (Sarith v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Arith v :: rest ->
        update (equal_int, linorder_int) pos (Arith v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Info v :: rest ->
        update (equal_int, linorder_int) pos (Info v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Dup v :: rest ->
        update (equal_int, linorder_int) pos (Dup v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Memory v :: rest ->
        update (equal_int, linorder_int) pos (Memory v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Storage v :: rest ->
        update (equal_int, linorder_int) pos (Storage v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Pc v :: rest ->
        update (equal_int, linorder_int) pos (Pc v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Stack POP :: rest ->
        update (equal_int, linorder_int) pos (Stack POP)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Stack CALLDATALOAD :: rest ->
        update (equal_int, linorder_int) pos (Stack CALLDATALOAD)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Swap v :: rest ->
        update (equal_int, linorder_int) pos (Swap v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Log v :: rest ->
        update (equal_int, linorder_int) pos (Log v)
          (program_avl_of_lst (plus_inta pos one_inta) rest)
    | pos, Misc v :: rest ->
        update (equal_int, linorder_int) pos (Misc v)
          (program_avl_of_lst (plus_inta pos one_inta) rest);;

let rec prog_init_cctx
  p = Constant_ctx_ext
        (program_of_lst p
           (fun lst ->
             lookup (equal_int, linorder_int)
               (program_avl_of_lst Zero_int lst)),
          w160_0, (fun _ -> false), ());;

let rec ellecompilev_4_cc l = ll4_load_lst_validate (prog_init_cctx []) l;;

let rec ll_get_node
  t x1 = match t, x1 with t, [] -> Some t
    | (q, LSeqa (e, ls)), v :: va -> ll_get_node_list ls (v :: va)
    | (vb, La (vd, ve)), v :: va -> None
    | (vb, LLaba (vd, ve)), v :: va -> None
    | (vb, LJmpa (vd, ve, vf)), v :: va -> None
    | (vb, LJmpIa (vd, ve, vf)), v :: va -> None
and ll_get_node_list
  uw x1 = match uw, x1 with uw, [] -> None
    | [], v :: va -> None
    | h :: ls, Zero_nat :: p -> ll_get_node h p
    | uy :: ls, Suc v :: p ->
        ll_get_node_list ls (minus_nat (Suc v) one_nat :: p);;

let rec ll4_validate_jump_targets
  ns x1 = match ns, x1 with
    ns, ((xa, x), LJmpa (a, idx, sz)) ->
      (match mynth ns idx with None -> false | Some b -> equal_nata a b)
    | ns, ((xa, x), LJmpIa (a, idx, sz)) ->
        (match mynth ns idx with None -> false | Some b -> equal_nata a b)
    | ns, (q, LSeqa ([], lsdec)) ->
        list_all (ll4_validate_jump_targets (None :: ns)) lsdec
    | ns, (q, LSeqa (v :: va, lsdec)) ->
        (match ll_get_node (q, LSeqa (v :: va, lsdec)) (v :: va)
          with None -> false | Some ((_, _), La (_, _)) -> false
          | Some ((qa, _), LLaba (_, idx)) ->
            equal_nata (plus_nat idx one_nat) (size_list (v :: va)) &&
              list_all (ll4_validate_jump_targets (Some qa :: ns)) lsdec
          | Some ((_, _), LJmpa (_, _, _)) -> false
          | Some ((_, _), LJmpIa (_, _, _)) -> false
          | Some ((_, _), LSeqa (_, _)) -> false)
    | uu, (v, La (vb, vc)) -> true
    | uu, (v, LLaba (vb, vc)) -> true;;

let rec get_process_jumps_fuela
  = function
    (uu, LJmpa (uv, uw, s)) ->
      minus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) s
    | (ux, LJmpIa (uy, uz, s)) ->
        minus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))) s
    | (va, LSeqa (vb, ls)) ->
        foldl (fun a x -> plus_nat a (get_process_jumps_fuela x)) Zero_nat ls
    | (v, La (vb, vd)) -> Zero_nat
    | (v, LLaba (vb, vd)) -> Zero_nat;;

let rec get_process_jumps_fuel
  l = plus_nat one_nat (get_process_jumps_fuela l);;

let rec ll_get_label
  vd ve = match vd, ve with
    ((x, uu), LLaba (uv, uw)) :: ux, [Zero_nat] -> Some x
    | (uy, LSeqa (uz, lsdec)) :: ls, Zero_nat :: p -> ll_get_label lsdec p
    | (v, La (vd, ve)) :: ls, Zero_nat :: vb -> None
    | (v, LJmpa (vd, ve, vf)) :: ls, Zero_nat :: vb -> None
    | (v, LJmpIa (vd, ve, vf)) :: ls, Zero_nat :: vb -> None
    | (vb, LLaba (ve, vf)) :: ls, Zero_nat :: v :: vc -> None
    | (v, La (vb, vd)) :: ls, Suc va :: p ->
        ll_get_label ls (minus_nat (Suc va) one_nat :: p)
    | (v, LJmpa (vb, vd, ve)) :: ls, Suc va :: p ->
        ll_get_label ls (minus_nat (Suc va) one_nat :: p)
    | (v, LJmpIa (vb, vd, ve)) :: ls, Suc va :: p ->
        ll_get_label ls (minus_nat (Suc va) one_nat :: p)
    | (v, LSeqa (vb, vd)) :: ls, Suc va :: p ->
        ll_get_label ls (minus_nat (Suc va) one_nat :: p)
    | vc :: ls, Suc v :: p -> ll_get_label ls (minus_nat (Suc v) one_nat :: p)
    | [], ve -> None
    | (vb, La (vf, vg)) :: va, [] -> None
    | (vb, LJmpa (vf, vg, vh)) :: va, [] -> None
    | (vb, LJmpIa (vf, vg, vh)) :: va, [] -> None
    | (vb, LSeqa (vf, vg)) :: va, [] -> None
    | vd, [] -> None;;

let rec write_jump_targets
  ns x1 = match ns, x1 with
    ns, ((xa, x), LSeqa ([], lsdec)) ->
      (match mypeel (map (write_jump_targets (None :: ns)) lsdec)
        with None -> None | Some lsdeca -> Some ((xa, x), LSeqa ([], lsdeca)))
    | ns, ((xa, x), LSeqa (v :: va, lsdec)) ->
        (match ll_get_label lsdec (v :: va) with None -> None
          | Some addr ->
            (match mypeel (map (write_jump_targets (Some addr :: ns)) lsdec)
              with None -> None
              | Some lsdeca -> Some ((xa, x), LSeqa (v :: va, lsdeca))))
    | ns, ((xa, x), LJmpa (uu, idx, sz)) ->
        (match mynth ns idx with None -> None
          | Some a -> Some ((xa, x), LJmpa (a, idx, sz)))
    | ns, ((xa, x), LJmpIa (uv, idx, sz)) ->
        (match mynth ns idx with None -> None
          | Some a -> Some ((xa, x), LJmpIa (a, idx, sz)))
    | uw, (v, La (vb, vc)) -> Some (v, La (vb, vc))
    | uw, (v, LLaba (vb, vc)) -> Some (v, LLaba (vb, vc));;

let rec encode_size
  n = plus_nat (nat (log256floor (of_nat semiring_1_int n))) one_nat;;

let rec ll3_resolve_jump
  x0 oaddr n rel absol = match x0, oaddr, n, rel, absol with
    (uu, LJmpa (e, idx, s)) :: ls, None, n, rel, absol ->
      (if equal_nata idx (size_list rel) then JFail (n :: absol)
        else ll3_resolve_jump ls None (plus_nat n one_nat) rel absol)
    | (uv, LJmpa (e, idx, s)) :: ls, Some addr, n, rel, absol ->
        (if equal_nata idx (size_list rel)
          then (if less_nat s (encode_size addr) then JBump (n :: absol)
                 else (if equal_nata s (encode_size addr)
                        then ll3_resolve_jump ls (Some addr)
                               (plus_nat n one_nat) rel absol
                        else JFail (n :: absol)))
          else ll3_resolve_jump ls (Some addr) (plus_nat n one_nat) rel absol)
    | (uw, LJmpIa (e, idx, s)) :: ls, None, n, rel, absol ->
        (if equal_nata idx (size_list rel) then JFail (n :: absol)
          else ll3_resolve_jump ls None (plus_nat n one_nat) rel absol)
    | (ux, LJmpIa (e, idx, s)) :: ls, Some addr, n, rel, absol ->
        (if equal_nata idx (size_list rel)
          then (if less_nat s (encode_size addr) then JBump (n :: absol)
                 else (if equal_nata s (encode_size addr)
                        then ll3_resolve_jump ls (Some addr)
                               (plus_nat n one_nat) rel absol
                        else JFail (n :: absol)))
          else ll3_resolve_jump ls (Some addr) (plus_nat n one_nat) rel absol)
    | (uy, LSeqa ([], lsdec)) :: ls, oaddr, n, rel, absol ->
        (match ll3_resolve_jump lsdec oaddr Zero_nat (n :: rel) (n :: absol)
          with JSuccess ->
            (match ll3_resolve_jump lsdec None Zero_nat [] (n :: absol)
              with JSuccess ->
                ll3_resolve_jump ls oaddr (plus_nat n one_nat) rel absol
              | JFail a -> JFail a | JBump a -> JBump a)
          | JFail a -> JFail a | JBump a -> JBump a)
    | (uz, LSeqa (v :: va, lsdec)) :: ls, oaddr, n, rel, absol ->
        (match ll3_resolve_jump lsdec oaddr Zero_nat (n :: rel) (n :: absol)
          with JSuccess ->
            (match ll_get_label lsdec (v :: va) with None -> JFail absol
              | Some newaddr ->
                (match
                  ll3_resolve_jump lsdec (Some newaddr) Zero_nat [] (n :: absol)
                  with JSuccess ->
                    ll3_resolve_jump ls oaddr (plus_nat n one_nat) rel absol
                  | JFail a -> JFail a | JBump a -> JBump a))
          | JFail a -> JFail a | JBump a -> JBump a)
    | (v, La (vb, vc)) :: ls, oaddr, n, rel, absol ->
        ll3_resolve_jump ls oaddr (plus_nat n one_nat) rel absol
    | (v, LLaba (vb, vc)) :: ls, oaddr, n, rel, absol ->
        ll3_resolve_jump ls oaddr (plus_nat n one_nat) rel absol
    | [], va, vb, vc, vd -> JSuccess;;

let rec ll3_resolve_jump_wrap
  = function
    (x, LSeqa (e, lsdec)) ->
      (match e with [] -> ll3_resolve_jump lsdec None Zero_nat [] []
        | a :: lista ->
          (match ll_get_label lsdec (a :: lista) with None -> JFail []
            | Some aa -> ll3_resolve_jump lsdec (Some aa) Zero_nat [] []))
    | (v, La (vb, vc)) -> JFail []
    | (v, LLaba (vb, vc)) -> JFail []
    | (v, LJmpa (vb, vc, vd)) -> JFail []
    | (v, LJmpIa (vb, vc, vd)) -> JFail [];;

let rec ll3_inc_jump
  x0 n c = match x0, n, c with
    ((xa, x), LJmpa (e, idx, s)) :: ls, n, [c] ->
      (if equal_nata n c
        then (((xa, plus_nat x one_nat), LJmpa (e, idx, plus_nat s one_nat)) ::
                ll3_bump one_nat ls,
               true)
        else (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [c] in
               (((xa, x), LJmpa (e, idx, s)) :: lsa, a)))
    | ((xa, x), LJmpIa (e, idx, s)) :: ls, n, [c] ->
        (if equal_nata n c
          then (((xa, plus_nat x one_nat),
                  LJmpIa (e, idx, plus_nat s one_nat)) ::
                  ll3_bump one_nat ls,
                 true)
          else (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [c] in
                 (((xa, x), LJmpIa (e, idx, s)) :: lsa, a)))
    | ((xa, x), LSeqa (e, lsdec)) :: ls, n, c :: cs ->
        (if equal_nata n c
          then (match ll3_inc_jump lsdec Zero_nat cs
                 with (lsdeca, true) ->
                   (((xa, plus_nat x one_nat), LSeqa (e, lsdeca)) ::
                      ll3_bump one_nat ls,
                     true)
                 | (lsdeca, false) ->
                   (let (lsa, a) = ll3_inc_jump ls n (c :: cs) in
                     (((xa, x), LSeqa (e, lsdeca)) :: lsa, a)))
          else (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) (c :: cs) in
                 (((xa, x), LSeqa (e, lsdec)) :: lsa, a)))
    | (v, La (vb, vc)) :: ls, n, c ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) c in
          ((v, La (vb, vc)) :: lsa, a))
    | (v, LLaba (vb, vc)) :: ls, n, c ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) c in
          ((v, LLaba (vb, vc)) :: lsa, a))
    | (v, LJmpIa (vb, vc, vd)) :: ls, n, [] ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [] in
          ((v, LJmpIa (vb, vc, vd)) :: lsa, a))
    | (v, LJmpIa (vb, vc, vd)) :: ls, n, va :: vf :: vg ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) (va :: vf :: vg) in
          ((v, LJmpIa (vb, vc, vd)) :: lsa, a))
    | (v, LSeqa (vb, vc)) :: ls, n, [] ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [] in
          ((v, LSeqa (vb, vc)) :: lsa, a))
    | h :: ls, n, [] ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [] in
          (h :: lsa, a))
    | (va, LJmpa (ve, vf, vg)) :: ls, n, v :: vb :: vc ->
        (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) (v :: vb :: vc) in
          ((va, LJmpa (ve, vf, vg)) :: lsa, a))
    | [], uu, uv -> ([], false);;

let rec ll3_inc_jump_wrap
  x0 c = match x0, c with
    ((xa, x), LSeqa (e, lsdec)), c ->
      (match ll3_inc_jump lsdec Zero_nat c
        with (lsdeca, true) -> ((xa, plus_nat x one_nat), LSeqa (e, lsdeca))
        | (_, false) -> ((xa, x), LSeqa (e, lsdec)))
    | (v, La (vb, vc)), uu -> (v, La (vb, vc))
    | (v, LLaba (vb, vc)), uu -> (v, LLaba (vb, vc))
    | (v, LJmpa (vb, vc, vd)), uu -> (v, LJmpa (vb, vc, vd))
    | (v, LJmpIa (vb, vc, vd)), uu -> (v, LJmpIa (vb, vc, vd));;

let rec process_jumps_loop
  x0 uu = match x0, uu with Zero_nat, uu -> None
    | Suc v, ls ->
        (match ll3_resolve_jump_wrap ls with JSuccess -> Some ls
          | JFail _ -> None
          | JBump c ->
            process_jumps_loop (minus_nat (Suc v) one_nat)
              (ll3_inc_jump_wrap ls (rev c)));;

let rec ll3_consume_label
  p n x2 = match p, n, x2 with p, n, [] -> Some ([], [])
    | p, n, (x, LLaba (b, idx)) :: ls ->
        (if equal_nata idx (size_list p)
          then (if equal_bool b false
                 then Some ((x, LLaba (true, idx)) :: ls, n :: p) else None)
          else (match ll3_consume_label p (plus_nat n one_nat) ls
                 with None -> None
                 | Some (lsa, pa) -> Some ((x, LLaba (b, idx)) :: lsa, pa)))
    | p, n, (x, LSeqa (e, lsdec)) :: ls ->
        (match ll3_consume_label (n :: p) Zero_nat lsdec with None -> None
          | Some (lsdeca, []) ->
            (match ll3_consume_label p (plus_nat n one_nat) ls with None -> None
              | Some (lsa, pa) -> Some ((x, LSeqa (e, lsdeca)) :: lsa, pa))
          | Some (lsdeca, aa :: lista) ->
            Some ((x, LSeqa (e, lsdeca)) :: ls, aa :: lista))
    | p, n, (v, La (vb, vc)) :: ls ->
        (match ll3_consume_label p (plus_nat n one_nat) ls with None -> None
          | Some (lsa, pa) -> Some ((v, La (vb, vc)) :: lsa, pa))
    | p, n, (v, LJmpa (vb, vc, vd)) :: ls ->
        (match ll3_consume_label p (plus_nat n one_nat) ls with None -> None
          | Some (lsa, pa) -> Some ((v, LJmpa (vb, vc, vd)) :: lsa, pa))
    | p, n, (v, LJmpIa (vb, vc, vd)) :: ls ->
        (match ll3_consume_label p (plus_nat n one_nat) ls with None -> None
          | Some (lsa, pa) -> Some ((v, LJmpIa (vb, vc, vd)) :: lsa, pa));;

let rec ll3_assign_label
  = function
    (x, LSeqa (e, ls)) ->
      (match ll3_consume_label [] Zero_nat ls with None -> None
        | Some (lsa, p) ->
          (match ll3_assign_label_list lsa with None -> None
            | Some lsb -> Some (x, LSeqa (rev p, lsb))))
    | (x, LLaba (false, idx)) -> None
    | (v, La (vb, vc)) -> Some (v, La (vb, vc))
    | (v, LLaba (true, vc)) -> Some (v, LLaba (true, vc))
    | (v, LJmpa (vb, vc, vd)) -> Some (v, LJmpa (vb, vc, vd))
    | (v, LJmpIa (vb, vc, vd)) -> Some (v, LJmpIa (vb, vc, vd))
and ll3_assign_label_list
  = function [] -> Some []
    | h :: t ->
        (match ll3_assign_label h with None -> None
          | Some ha ->
            (match ll3_assign_label_list t with None -> None
              | Some ta -> Some (ha :: ta)));;

let rec ellecompile_untrusted
  l = (match ll3_assign_label (ll3_init (ll_pass1 l)) with None -> None
        | Some la ->
          (match process_jumps_loop (get_process_jumps_fuel la) la
            with None -> None
            | Some lb ->
              (match write_jump_targets [] (ll4_init lb) with None -> None
                | Some a -> Some a)));;

let rec gather_ll3_labels_list
  x0 vp vq vr = match x0, vp, vq, vr with [], vp, vq, vr -> []
    | h :: t, cp, ofs, d ->
        gather_ll3_labels h (cp @ [ofs]) d @
          gather_ll3_labels_list t cp (plus_nat ofs one_nat) d
and gather_ll3_labels
  x0 ux uy = match x0, ux, uy with (uu, La (uv, uw)), ux, uy -> []
    | (uz, LJmpa (va, vb, vc)), vd, ve -> []
    | (vf, LJmpIa (vg, vh, vi)), vj, vk -> []
    | (vl, LLaba (vm, n)), cp, d -> (if equal_nata n d then [cp] else [])
    | (vn, LSeqa (vo, ls)), cp, d ->
        gather_ll3_labels_list ls cp Zero_nat (plus_nat d one_nat);;

let rec check_ll3
  = function (uu, La (uv, uw)) -> true
    | (ux, LJmpa (uy, uz, va)) -> true
    | (vb, LJmpIa (vc, vd, ve)) -> true
    | (vf, LLaba (b, n)) -> equal_bool b true
    | (vg, LSeqa ([], ls)) ->
        list_all check_ll3 ls &&
          null (gather_ll3_labels_list ls [] Zero_nat Zero_nat)
    | (vh, LSeqa (v :: va, ls)) ->
        list_all check_ll3 ls &&
          equal_lista (equal_list equal_nat)
            (gather_ll3_labels_list ls [] Zero_nat Zero_nat) [v :: va];;

let rec ellecompilev_1_4
  l = (if ll1_valid l
        then (match ellecompile_untrusted l with None -> None
               | Some la ->
                 (if check_ll3 la
                   then (if ll4_validate_jump_targets [] la then Some la
                          else None)
                   else None))
        else None);;

let rec ellecompilev_full
  l = (match ellecompilev_1_4 l with None -> None
        | Some l4 ->
          (match ellecompilev_4_cc l4 with None -> None
            | Some cc ->
              (match ellecompilev_cc_il cc with None -> None
                | Some a -> ellecompilev_il_wl a)));;

let rec ellecompilev_1_il
  l = (match ellecompilev_1_4 l with None -> None
        | Some l4 ->
          (match ellecompilev_4_cc l4 with None -> None
            | Some a -> ellecompilev_cc_il a));;

let rec llll_combine_payload_sub
  fuel presz paysz startbytes endbytes =
    (if equal_nata fuel Zero_nat then None
      else (if equal_nata (encode_size paysz) endbytes
             then (if equal_nata
                        (encode_size
                          (plus_nat
                            (plus_nat (plus_nat presz startbytes) endbytes)
                            base_interlude_size))
                        startbytes
                    then Some (startbytes, endbytes)
                    else llll_combine_payload_sub (minus_nat fuel one_nat) presz
                           paysz (plus_nat startbytes one_nat) endbytes)
             else llll_combine_payload_sub (minus_nat fuel one_nat) presz paysz
                    startbytes (plus_nat endbytes one_nat)));;

let combine_payload_fuel : nat
  = plus_nat (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
      (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))));;

let default_llll_funs : (char list * (llll list -> llll option)) list
  = [([Chara (true, true, false, false, true, true, true, false);
        Chara (true, false, true, false, false, true, true, false);
        Chara (true, false, false, false, true, true, true, false)],
       (fun l -> Some (L4Seq l)));
      ([Chara (true, false, false, true, false, true, true, false);
         Chara (false, true, true, false, false, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None | [_; _] -> None
            | [c; br1; br2] -> Some (L4If (c, br1, br2))
            | _ :: _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, true, false, true, true, true, false);
         Chara (false, false, false, true, false, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (false, true, true, true, false, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [c; br] -> Some (L4When (c, br)) | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, false, true, false, true, true, true, false);
         Chara (false, true, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (true, true, false, false, true, true, true, false);
         Chara (true, true, false, false, true, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [c; br] -> Some (L4Unless (c, br)) | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, true, true, false, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None | [_; _] -> None
            | [_; _; _] -> None
            | [i; p; body; post] -> Some (L4For (i, p, body, post))
            | _ :: _ :: _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, false, true, false, true, false, false)],
        (fun l -> Some (L4Arith (LAPlus, l))));
      ([Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false)],
        (fun l -> Some (L4Arith (LAPlus, l))));
      ([Chara (true, false, true, true, false, true, false, false)],
        (fun l -> Some (L4Arith (LAMinus, l))));
      ([Chara (false, true, false, true, false, true, false, false)],
        (fun l -> Some (L4Arith (LATimes, l))));
      ([Chara (false, false, true, false, false, true, true, false);
         Chara (true, false, false, true, false, true, true, false);
         Chara (false, true, true, false, true, true, true, false)],
        (fun l -> Some (L4Arith (LADiv, l))));
      ([Chara (true, false, true, false, false, true, true, false);
         Chara (false, false, false, true, true, true, true, false);
         Chara (false, false, false, false, true, true, true, false)],
        (fun l -> Some (L4Arith (LAExp, l))));
      ([Chara (true, true, true, true, false, true, false, false)],
        (fun l -> Some (L4Arith (LADiv, l))));
      ([Chara (true, false, true, false, false, true, false, false)],
        (fun l -> Some (L4Arith (LAMod, l))));
      ([Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, false, true, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (true, true, false, false, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [start; width] -> Some (L4I2 (Arith SHA3, start, width))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, false, true, false, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (true, true, false, false, false, true, true, false);
         Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (true, true, false, true, false, true, true, false);
         Chara (false, true, false, false, true, true, false, false);
         Chara (true, false, true, false, true, true, false, false);
         Chara (false, true, true, false, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [start; width] -> Some (L4I2 (Arith SHA3, start, width))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, true, true, false, false, true, false, false)],
        (fun l -> Some (L4Arith (LAAnd, l))));
      ([Chara (false, false, true, true, true, true, true, false)],
        (fun l -> Some (L4Arith (LAOr, l))));
      ([Chara (false, true, true, true, true, false, true, false)],
        (fun l -> Some (L4Arith (LAXor, l))));
      ([Chara (false, true, true, true, true, true, true, false)],
        (fun l -> Some (L4Arith (LANot, l))));
      ([Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, false, true, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [vala; shift] ->
              Some (L4Arith
                     (LADiv,
                       [vala;
                         L4Arith (LAExp, [L4L_Int (Pos (Bit0 One)); shift])]))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, true, true, false, false, true, false, false);
         Chara (false, true, true, false, false, true, false, false)],
        (fun l -> Some (L4Logic (LLAnd, l))));
      ([Chara (false, false, true, true, true, true, true, false);
         Chara (false, false, true, true, true, true, true, false)],
        (fun l -> Some (L4Logic (LLOr, l))));
      ([Chara (true, false, false, false, false, true, false, false)],
        (fun l -> Some (L4Logic (LLNot, l))));
      ([Chara (true, false, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCEq, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, false, false, false, false, true, false, false);
         Chara (true, false, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCNeq, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, true, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCGt, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, false, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCLt, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, false, true, true, true, true, false, false);
         Chara (true, false, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCLe, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (false, true, true, true, true, true, false, false);
         Chara (true, false, true, true, true, true, false, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCGe, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, false, true, true, false, true, true, false);
         Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [loc; item] -> Some (L4I2 (Memory MSTORE, loc, item))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false)],
        (fun a ->
          (match a with [] -> None | [loc] -> Some (L4I1 (Memory MLOAD, loc))
            | _ :: _ :: _ -> None)));
      ([Chara (false, true, false, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, false, true, false, true, true, true, false);
         Chara (false, true, false, false, true, true, true, false);
         Chara (false, true, true, true, false, true, true, false)],
        (fun a ->
          (match a with [] -> None
            | [con] ->
              Some (L4Seq
                     [L4I2 (Memory MSTORE, L4L_Int Zero_int, con);
                       L4I2 (Misc RETURN, L4L_Int Zero_int,
                              L4L_Int
                                (Pos (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))])
            | [con; sz] -> Some (L4I2 (Misc RETURN, con, sz))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (false, false, false, false, true, true, true, false)],
        (fun _ -> Some (L4I0 (Misc STOP))));
      ([Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false)],
        (fun a ->
          (match a with [] -> None
            | [loc] -> Some (L4I1 (Stack CALLDATALOAD, loc))
            | _ :: _ :: _ -> None)));
      ([Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (true, true, false, false, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (false, false, false, false, true, true, true, false);
         Chara (true, false, false, true, true, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None | [_; _] -> None
            | [dst; src; len] ->
              Some (L4I3 (Memory CALLDATACOPY, dst, src, len))
            | _ :: _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (true, true, false, false, true, true, true, false);
         Chara (true, false, false, true, false, true, true, false);
         Chara (false, true, false, true, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false)],
        (fun _ -> Some (L4I0 (Info CALLDATASIZE))));
      ([Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, true, true, false, true, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, false, true, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false)],
        (fun _ -> Some (L4I0 (Info CALLVALUE))));
      ([Chara (true, true, false, false, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false)],
        (fun _ -> Some (L4I0 (Info CALLER))));
      ([Chara (true, true, false, false, true, true, true, false);
         Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, true, false, true, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [loc; sz] -> Some (L4I2 (Storage SSTORE, loc, sz))
            | _ :: _ :: _ :: _ -> None)));
      ([Chara (true, true, false, false, true, true, true, false);
         Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, false, false, false, false, true, true, false);
         Chara (false, false, true, false, false, true, true, false)],
        (fun [loc] -> Some (L4I1 (Storage SLOAD, loc))));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, true, true, false, false, true, true, false);
         Chara (false, false, false, false, true, true, false, false)],
        (fun l ->
          (if equal_nata (size_list l) (nat_of_num (Bit0 One))
            then Some (L4In (Log LOG0, l)) else None)));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, true, true, false, false, true, true, false);
         Chara (true, false, false, false, true, true, false, false)],
        (fun l ->
          (if equal_nata (size_list l) (nat_of_num (Bit1 One))
            then Some (L4In (Log LOG1, l)) else None)));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, true, true, false, false, true, true, false);
         Chara (false, true, false, false, true, true, false, false)],
        (fun l ->
          (if equal_nata (size_list l) (nat_of_num (Bit0 (Bit0 One)))
            then Some (L4In (Log LOG2, l)) else None)));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, true, true, false, false, true, true, false);
         Chara (true, true, false, false, true, true, false, false)],
        (fun l ->
          (if equal_nata (size_list l) (nat_of_num (Bit1 (Bit0 One)))
            then Some (L4In (Log LOG3, l)) else None)));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, true, true, true, false, true, true, false);
         Chara (true, true, true, false, false, true, true, false);
         Chara (false, false, true, false, true, true, false, false)],
        (fun l ->
          (if equal_nata (size_list l) (nat_of_num (Bit0 (Bit1 One)))
            then Some (L4In (Log LOG4, l)) else None)));
      ([Chara (false, true, false, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (false, true, true, false, true, true, true, false);
         Chara (true, false, true, false, false, true, true, false);
         Chara (false, true, false, false, true, true, true, false);
         Chara (false, false, true, false, true, true, true, false)],
        (fun _ -> Some L4Revert));
      ([Chara (false, false, true, true, false, true, true, false);
         Chara (true, false, false, true, false, true, true, false);
         Chara (false, false, true, false, true, true, true, false)],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [loc; lit] ->
              (match l4constSize lit with None -> None
                | Some i ->
                  Some (L4Seq [L4I2 (Memory MSTORE, lit, loc); L4L_Int i]))
            | _ :: _ :: _ :: _ -> None)))];;

let rec llll_parse1_default
  st = (match llll_parse1 default_llll_funs st with None -> None
         | Some (l, (x, _)) -> Some (l, x));;

let rec llll_parse_complete
  s = (match llll_parse0 s with None -> None
        | Some a -> llll_parse1_default a);;

let rec fourL_compiler_string
  s = (match llll_parse_complete s with None -> None
        | Some (l4pre, None) ->
          (match ellecompilev_full (llll_compile l4pre) with None -> None
            | Some wl -> Some (hexwrite wl))
        | Some (l4pre, Some l4pay) ->
          (match ellecompilev_1_il (llll_compile l4pre) with None -> None
            | Some il_pre ->
              (match ellecompilev_1_il (llll_compile l4pay) with None -> None
                | Some il_pay ->
                  (match
                    llll_combine_payload_sub combine_payload_fuel (ilsz il_pre)
                      (ilsz il_pay) Zero_nat Zero_nat
                    with None -> None
                    | Some (startbytes, endbytes) ->
                      (match
                        codegen_clean
                          (makeInterlude startbytes endbytes il_pre il_pay)
                        with None -> None | Some wl -> Some (hexwrite wl))))));;

let rec explode
  s = map char_of_integer
        (let s = s in let rec exp i l = if i < 0 then l else exp (i - 1) (let k = Char.code (Bytes.get s i) in
      if k < 128 then Big_int.big_int_of_int k :: l else failwith "Non-ASCII character in literal") in exp (Bytes.length s - 1) []);;

let rec compiler
  l = (match fourL_compiler_string (explode l) with None -> None
        | Some s -> Some (implode s));;

end;; (*struct FourL*)

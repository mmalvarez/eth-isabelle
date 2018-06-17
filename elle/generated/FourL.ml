module FourL : sig
  val compiler : string -> string option
end = struct

type int = Int_of_integer of Big_int.big_int;;

type num = One | Bit0 of num | Bit1 of num;;

let one_inta : int = Int_of_integer (Big_int.big_int_of_int 1);;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_int = ({one = one_inta} : int one);;

let rec integer_of_int (Int_of_integer k) = k;;

let rec times_inta
  k l = Int_of_integer
          (Big_int.mult_big_int (integer_of_int k) (integer_of_int l));;

type 'a times = {times : 'a -> 'a -> 'a};;
let times _A = _A.times;;

type 'a power = {one_power : 'a one; times_power : 'a times};;

let times_int = ({times = times_inta} : int times);;

let power_int = ({one_power = one_int; times_power = times_int} : int power);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_char = ({equal = (fun a b -> ((a : char) = b))} : char equal);;

type nat = Nat of Big_int.big_int;;

type 'a itself = Type;;

type 'a len0 = {len_of : 'a itself -> nat};;
let len_of _A = _A.len_of;;

let rec integer_of_nat (Nat x) = x;;

let rec times_nat
  m n = Nat (Big_int.mult_big_int (integer_of_nat m) (integer_of_nat n));;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let rec max _A a b = (if less_eq _A a b then b else a);;

let ord_integer =
  ({less_eq = Big_int.le_big_int; less = Big_int.lt_big_int} :
    Big_int.big_int ord);;

let rec nat_of_integer k = Nat (max ord_integer Big_int.zero_big_int k);;

type 'a finite = unit;;

type 'a bit0 = Abs_bit0 of int;;

let rec len_of_bit0 _A
  uu = times_nat (nat_of_integer (Big_int.big_int_of_int 2)) (len_of _A Type);;

let rec len0_bit0 _A = ({len_of = len_of_bit0 _A} : 'a bit0 len0);;

let one_nat : nat = Nat (Big_int.big_int_of_int 1);;

type num1 = One_num1;;

let rec len_of_num1 uu = one_nat;;

let len0_num1 = ({len_of = len_of_num1} : num1 len0);;

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

type llll = L4L_Str of char list | L4L_Nat of nat | L4I0 of inst |
  L4I1 of inst * llll | L4I2 of inst * llll * llll | L4Seq of llll list |
  L4Arith of llllarith * llll list | L4Logic of lllllogic * llll list |
  L4Comp of llllcompare * llll * llll | L4When of llll * llll |
  L4If of llll * llll * llll | L4While of llll * llll;;

type stree = STStr of char list | STStrs of stree list;;

type ll1 = L of inst | LLab of nat | LJmp of nat | LJmpI of nat |
  LSeq of ll1 list;;

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt = La of 'a * inst | LLaba of 'b * nat |
  LJmpa of 'c * nat * nat | LJmpIa of 'd * nat * nat |
  LSeqa of 'e * ((nat * nat) * ('a, 'b, 'c, 'd, 'e, 'f, 'g) llt) list;;

type jump_resolve_result = JSuccess | JFail of nat list | JBump of nat list;;

let rec eq _A a b = equal _A a b;;

let rec nat k = Nat (max ord_integer Big_int.zero_big_int (integer_of_int k));;

let rec plus_nat
  m n = Nat (Big_int.add_big_int (integer_of_nat m) (integer_of_nat n));;

let rec suc n = plus_nat n one_nat;;

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

let rec char_of_nat
  x = comp (fun a -> Char.chr (Big_int.int_of_big_int a)) integer_of_nat x;;

let apos : char = char_of_nat (nat_of_integer (Big_int.big_int_of_int 39));;

let zero_nat : nat = Nat Big_int.zero_big_int;;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length zero_nat x;;

let rec int_of_nat n = Int_of_integer (integer_of_nat n);;

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

let rec snd (x1, x2) = x2;;

let rec modulo_integer k l = snd (divmod_integer k l);;

let rec modulo_int
  k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));;

let rec minus_nat
  m n = Nat (max ord_integer Big_int.zero_big_int
              (Big_int.sub_big_int (integer_of_nat m) (integer_of_nat n)));;

let rec equal_nat
  m n = Big_int.eq_big_int (integer_of_nat m) (integer_of_nat n);;

let rec power _A
  a n = (if equal_nat n zero_nat then one _A.one_power
          else times _A.times_power a (power _A a (minus_nat n one_nat)));;

let rec word_of_int _A
  k = Word (modulo_int k
             (power power_int (Int_of_integer (Big_int.big_int_of_int 2))
               (len_of _A Type)));;

let rec storage_inst_code
  = function
    SLOAD ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 84))
    | SSTORE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 85));;

let rec sarith_inst_code
  = function
    SDIV ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 5))
    | SMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 7))
    | SGT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 19))
    | SLT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 18))
    | SIGNEXTEND ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 11));;

let rec memory_inst_code
  = function
    MLOAD ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 81))
    | MSTORE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 82))
    | MSTORE8 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 83))
    | CALLDATACOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 55))
    | CODECOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 57))
    | EXTCODECOPY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 60))
    | MSIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 89));;

let rec plus_int
  k l = Int_of_integer
          (Big_int.add_big_int (integer_of_int k) (integer_of_int l));;

let rec plus_word _A a b = word_of_int _A (plus_int (uint _A a) (uint _A b));;

let zero_int : int = Int_of_integer Big_int.zero_big_int;;

let rec less_nat
  m n = Big_int.lt_big_int (integer_of_nat m) (integer_of_nat n);;

let rec word8FromNat
  i = word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) (int_of_nat i);;

let rec byteFromNat x = word8FromNat x;;

let rec stack_inst_code
  = function
    POP ->
      [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
         (Int_of_integer (Big_int.big_int_of_int 80))]
    | PUSH_N lst ->
        (if less_nat (size_list lst) one_nat
          then [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                  (Int_of_integer (Big_int.big_int_of_int 96));
                 word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                   zero_int]
          else (if less_nat (nat_of_integer (Big_int.big_int_of_int 32))
                     (size_list lst)
                 then [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                         (Int_of_integer (Big_int.big_int_of_int 96));
                        word_of_int
                          (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                          zero_int]
                 else [plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                         (byteFromNat (size_list lst))
                         (word_of_int
                           (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
                           (Int_of_integer (Big_int.big_int_of_int 95)))] @
                        lst))
    | CALLDATALOAD ->
        [word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
           (Int_of_integer (Big_int.big_int_of_int 53))];;

let rec arith_inst_code
  = function
    ADD -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) one_inta
    | MUL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 2))
    | SUB ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 3))
    | DIV ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 4))
    | MOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 6))
    | ADDMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 8))
    | MULMOD ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 9))
    | EXP ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 10))
    | Inst_GT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 17))
    | Inst_LT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 16))
    | Inst_EQ ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 20))
    | ISZERO ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 21))
    | SHA3 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 32));;

let rec swap_inst_code
  m = plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (uint (len0_bit0 (len0_bit0 len0_num1)) m))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 144)));;

let rec misc_inst_code
  = function
    STOP -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) zero_int
    | CREATE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 240))
    | CALL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 241))
    | CALLCODE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 242))
    | RETURN ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 243))
    | DELEGATECALL ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 244))
    | SUICIDE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 255));;

let rec info_inst_code
  = function
    ADDRESS ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 48))
    | BALANCE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 49))
    | ORIGIN ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 50))
    | CALLVALUE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 52))
    | CALLDATASIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 54))
    | CALLER ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 51))
    | CODESIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 56))
    | GASPRICE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 58))
    | EXTCODESIZE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 59))
    | BLOCKHASH ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 64))
    | COINBASE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 65))
    | TIMESTAMP ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 66))
    | NUMBER ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 67))
    | DIFFICULTY ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 68))
    | GASLIMIT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 69))
    | GAS ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 90));;

let rec bits_inst_code
  = function
    Inst_AND ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 22))
    | Inst_OR ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 23))
    | Inst_XOR ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 24))
    | Inst_NOT ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 25))
    | BYTE ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 26));;

let rec log_inst_code
  = function
    LOG0 ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 160))
    | LOG1 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 161))
    | LOG2 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 162))
    | LOG3 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 163))
    | LOG4 ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 164));;

let rec dup_inst_code
  m = plus_word (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (uint (len0_bit0 (len0_bit0 len0_num1)) m))
        (word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 128)));;

let rec pc_inst_code
  = function
    JUMP ->
      word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
        (Int_of_integer (Big_int.big_int_of_int 86))
    | JUMPI ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 87))
    | PC -> word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
              (Int_of_integer (Big_int.big_int_of_int 88))
    | JUMPDEST ->
        word_of_int (len0_bit0 (len0_bit0 (len0_bit0 len0_num1)))
          (Int_of_integer (Big_int.big_int_of_int 91));;

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

let rec inst_size i = int_of_nat (size_list (inst_code i));;

let rec ilsz = function [] -> zero_nat
               | h :: t -> plus_nat (nat (inst_size h)) (ilsz t);;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec member _A x0 y = match x0, y with [], y -> false
                    | x :: xs, y -> eq _A x y || member _A xs y;;

let rec isWs
  x = member equal_char
        (map char_of_nat
          [nat_of_integer (Big_int.big_int_of_int 9);
            nat_of_integer (Big_int.big_int_of_int 10);
            nat_of_integer (Big_int.big_int_of_int 11);
            nat_of_integer (Big_int.big_int_of_int 12);
            nat_of_integer (Big_int.big_int_of_int 13);
            nat_of_integer (Big_int.big_int_of_int 32)])
        x;;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec map_of _A
  x0 k = match x0, k with
    (l, v) :: ps, k -> (if eq _A l k then Some v else map_of _A ps k)
    | [], k -> None;;

let rec il2wl il = maps inst_code il;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

let rec lookupS
  x0 uu = match x0, uu with [], uu -> None
    | (ah, bh) :: t, a ->
        (if equal_list equal_char a ah then Some bh else lookupS t a);;

let rec mkConsts
  x0 x1 = match x0, x1 with [], [] -> Some []
    | sh :: st, lh :: lt ->
        (match mkConsts st lt with None -> None
          | Some ft -> Some ((sh, (fun _ -> Some lh)) :: ft))
    | v :: va, [] -> None
    | [], v :: va -> None;;

let hex_parse_table : (char * nat) list
  = [('0', zero_nat); ('1', one_nat);
      ('2', nat_of_integer (Big_int.big_int_of_int 2));
      ('3', nat_of_integer (Big_int.big_int_of_int 3));
      ('4', nat_of_integer (Big_int.big_int_of_int 4));
      ('5', nat_of_integer (Big_int.big_int_of_int 5));
      ('6', nat_of_integer (Big_int.big_int_of_int 6));
      ('7', nat_of_integer (Big_int.big_int_of_int 7));
      ('8', nat_of_integer (Big_int.big_int_of_int 8));
      ('9', nat_of_integer (Big_int.big_int_of_int 9));
      ('A', nat_of_integer (Big_int.big_int_of_int 10));
      ('a', nat_of_integer (Big_int.big_int_of_int 10));
      ('B', nat_of_integer (Big_int.big_int_of_int 11));
      ('b', nat_of_integer (Big_int.big_int_of_int 11));
      ('C', nat_of_integer (Big_int.big_int_of_int 12));
      ('c', nat_of_integer (Big_int.big_int_of_int 12));
      ('D', nat_of_integer (Big_int.big_int_of_int 13));
      ('d', nat_of_integer (Big_int.big_int_of_int 13));
      ('E', nat_of_integer (Big_int.big_int_of_int 14));
      ('e', nat_of_integer (Big_int.big_int_of_int 14));
      ('F', nat_of_integer (Big_int.big_int_of_int 15));
      ('f', nat_of_integer (Big_int.big_int_of_int 15))];;

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
              (plus_nat
                (times_nat (nat_of_integer (Big_int.big_int_of_int 16)) i) n)
              l su fa r)
          (su i) r;;

let rec parseHex
  x0 su fa r = match x0, su, fa, r with
    h0 :: hx :: h :: t, su, fa, r ->
      (if ((h0 : char) = '0') && ((hx : char) = 'x')
        then parseHexNumeral (h :: t) (fun n l -> parseHexSub n l su fa r) fa r
        else fa (h0 :: hx :: h :: t))
    | [], su, fa, r -> fa []
    | [v], su, fa, r -> fa [v]
    | [v; vb], su, fa, r -> fa [v; vb];;

let rec is_digit_char
  c = ((c : char) = '0') ||
        (((c : char) = '5') ||
          (((c : char) = '1') ||
            (((c : char) = '6') ||
              (((c : char) = '2') ||
                (((c : char) = '7') ||
                  (((c : char) = '3') ||
                    (((c : char) = '8') ||
                      (((c : char) = '4') || ((c : char) = '9')))))))));;

let rec char_to_digit
  c = (if ((c : char) = '0') then zero_nat
        else (if ((c : char) = '1') then one_nat
               else (if ((c : char) = '2')
                      then nat_of_integer (Big_int.big_int_of_int 2)
                      else (if ((c : char) = '3')
                             then nat_of_integer (Big_int.big_int_of_int 3)
                             else (if ((c : char) = '4')
                                    then nat_of_integer
   (Big_int.big_int_of_int 4)
                                    else (if ((c : char) = '5')
   then nat_of_integer (Big_int.big_int_of_int 5)
   else (if ((c : char) = '6') then nat_of_integer (Big_int.big_int_of_int 6)
          else (if ((c : char) = '7')
                 then nat_of_integer (Big_int.big_int_of_int 7)
                 else (if ((c : char) = '8')
                        then nat_of_integer (Big_int.big_int_of_int 8)
                        else (if ((c : char) = '9')
                               then nat_of_integer (Big_int.big_int_of_int 9)
                               else nat_of_integer
                                      (Big_int.big_int_of_int 10)))))))))));;

let rec parseNumeral
  x0 s f r = match x0, s, f, r with [], s, f, r -> f []
    | h :: t, s, f, r ->
        (if is_digit_char h then s (char_to_digit h) t else f (h :: t));;

let rec parseNatSub
  i x1 su fa r = match i, x1, su, fa, r with i, [], su, fa, r -> su i []
    | i, h :: t, su, fa, r ->
        parseNumeral (h :: t)
          (fun n l ->
            parseNatSub
              (plus_nat
                (times_nat (nat_of_integer (Big_int.big_int_of_int 10)) i) n)
              l su fa r)
          (su i) r;;

let rec parseNat
  x0 su fa r = match x0, su, fa, r with [], su, fa, r -> fa []
    | h :: t, su, fa, r ->
        parseNumeral (h :: t) (fun n l -> parseNatSub n l su fa r) fa r;;

let rec fst (x1, x2) = x1;;

let rec divide_integer k l = fst (divmod_integer k l);;

let rec divide_int
  k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));;

let rec less_eq_int
  k l = Big_int.le_big_int (integer_of_int k) (integer_of_int l);;

let rec log256floor
  x = (if less_eq_int x (Int_of_integer (Big_int.big_int_of_int 255))
        then zero_int
        else plus_int one_inta
               (log256floor
                 (divide_int x
                   (Int_of_integer (Big_int.big_int_of_int 256)))));;

let rec run_parse
  p donea dfl s =
    p s (fun x _ -> donea x) (fun _ -> dfl)
      (fun sa _ _ -> run_parse p donea dfl sa);;

let rec modulo_nat
  m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));;

let rec divide_nat
  m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));;

let rec divmod_nat m n = (divide_nat m n, modulo_nat m n);;

let rec nat_to_bytes
  n = (let (a, mo) = divmod_nat n (nat_of_integer (Big_int.big_int_of_int 256))
         in
        (if equal_nat a zero_nat then [byteFromNat mo]
          else byteFromNat mo :: nat_to_bytes (suc (minus_nat a one_nat))));;

let rec output_address n = rev (nat_to_bytes n);;

let rec intToBytes i = output_address (nat i);;

let rec stree_append x0 uu = match x0, uu with STStr x, uu -> STStr x
                       | STStrs xs, s -> STStrs (xs @ [s]);;

let rec llll_parse
  x0 uu uv = match x0, uu, uv with [], uu, uv -> None
    | h :: t, token, parsed ->
        (if ((h : char) = '(') then llll_parse t token (STStrs [] :: parsed)
          else (if ((h : char) = ')')
                 then (match parsed with [] -> None
                        | [ph] ->
                          (if not (null token)
                            then Some (stree_append ph (STStr token))
                            else Some ph)
                        | ph :: ph2 :: pt ->
                          (if not (null token)
                            then llll_parse t []
                                   (stree_append ph2
                                      (stree_append ph (STStr token)) ::
                                     pt)
                            else llll_parse t [] (stree_append ph2 ph :: pt)))
                 else (if isWs h
                        then (if not (null token)
                               then (match parsed with [] -> None
                                      | ph :: pt ->
llll_parse t [] (stree_append ph (STStr token) :: pt))
                               else llll_parse t [] parsed)
                        else llll_parse t (token @ [h]) parsed)));;

let rec llll_parse0 s = llll_parse s [] [];;

let rec run_parse_opt p f s = run_parse p f None s;;

let rec run_parse_opta p s = run_parse_opt p (fun a -> Some a) s;;

let rec llll_parse1
  ft x1 = match ft, x1 with
    ft, STStr s ->
      (match run_parse_opta parseHex s
        with None ->
          (match run_parse_opta parseNat s
            with None ->
              (match lookupS ft s with None -> None
                | Some f ->
                  (match f [] with None -> None
                    | Some l -> Some (l, (None, ft))))
            | Some n -> Some (L4L_Nat n, (None, ft)))
        | Some n -> Some (L4L_Nat n, (None, ft)))
    | ft, STStrs (h :: t) ->
        (match h
          with STStr hs ->
            (if equal_list equal_char hs ['d'; 'e'; 'f']
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
              else (if equal_list equal_char hs
                         ['r'; 'e'; 't'; 'u'; 'r'; 'n'; 'l'; 'l'; 'l']
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
            (if not ((hdchr : char) = apos) then None
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
  ft x1 = match ft, x1 with ft, [] -> None
    | ft, [h] ->
        (match llll_parse1 ft h with None -> None
          | Some (l, (x, fta)) -> Some ([l], (x, fta)))
    | ft, h :: v :: va ->
        (match llll_parse1 ft h with None -> None
          | Some (ha, (None, fta)) ->
            (match llll_parse1_args fta (v :: va) with None -> None
              | Some (t, (x, ftb)) -> Some (ha :: t, (x, ftb)))
          | Some (ha, (Some pay, fta)) -> Some ([ha], (Some pay, fta)));;

let rec mynth
  x0 uu = match x0, uu with [], uu -> None
    | h :: t, v ->
        (if equal_nat v zero_nat then h
          else mynth t (minus_nat (suc (minus_nat v one_nat)) one_nat));;

let rec hexwrite1
  c = (if equal_nat c zero_nat then '0'
        else (if equal_nat c one_nat then '1'
               else (if equal_nat c (nat_of_integer (Big_int.big_int_of_int 2))
                      then '2'
                      else (if equal_nat c
                                 (nat_of_integer (Big_int.big_int_of_int 3))
                             then '3'
                             else (if equal_nat c
(nat_of_integer (Big_int.big_int_of_int 4))
                                    then '4'
                                    else (if equal_nat c
       (nat_of_integer (Big_int.big_int_of_int 5))
   then '5'
   else (if equal_nat c (nat_of_integer (Big_int.big_int_of_int 6)) then '6'
          else (if equal_nat c (nat_of_integer (Big_int.big_int_of_int 7))
                 then '7'
                 else (if equal_nat c
                            (nat_of_integer (Big_int.big_int_of_int 8))
                        then '8'
                        else (if equal_nat c
                                   (nat_of_integer (Big_int.big_int_of_int 9))
                               then '9'
                               else (if equal_nat c
  (nat_of_integer (Big_int.big_int_of_int 10))
                                      then 'a'
                                      else (if equal_nat c
         (nat_of_integer (Big_int.big_int_of_int 11))
     then 'b'
     else (if equal_nat c (nat_of_integer (Big_int.big_int_of_int 12)) then 'c'
            else (if equal_nat c (nat_of_integer (Big_int.big_int_of_int 13))
                   then 'd'
                   else (if equal_nat c
                              (nat_of_integer (Big_int.big_int_of_int 14))
                          then 'e'
                          else (if equal_nat c
                                     (nat_of_integer
                                       (Big_int.big_int_of_int 15))
                                 then 'f'
                                 else failwith "undefined"))))))))))))))));;

let rec hexwrite2
  w = (let (d, m) =
         divmod_nat (unat (len0_bit0 (len0_bit0 (len0_bit0 len0_num1))) w)
           (nat_of_integer (Big_int.big_int_of_int 16))
         in
        (hexwrite1 d, hexwrite1 m));;

let rec hexwrite
  = function [] -> []
    | h :: t -> (let (c1, c2) = hexwrite2 h in c1 :: c2 :: hexwrite t);;

let rec nat_of_char
  x = comp nat_of_integer (fun a -> Big_int.big_int_of_int (Char.code a)) x;;

let rec truncate_string_sub
  x0 n = match x0, n with
    [], n ->
      (if equal_nat n zero_nat then []
        else byteFromNat zero_nat ::
               truncate_string_sub [] (minus_nat n one_nat))
    | h :: t, n ->
        (if equal_nat n zero_nat then []
          else byteFromNat (nat_of_char h) ::
                 truncate_string_sub t (minus_nat n one_nat));;

let rec truncate_string
  s = truncate_string_sub s (nat_of_integer (Big_int.big_int_of_int 32));;

let rec llll_compile
  = function L4L_Str s -> L (Stack (PUSH_N (truncate_string s)))
    | L4L_Nat i -> L (Stack (PUSH_N (intToBytes (int_of_nat i))))
    | L4I0 i -> L i
    | L4I1 (i, l) -> LSeq [llll_compile l; L i]
    | L4I2 (i, l1, l2) -> LSeq [llll_compile l2; llll_compile l1; L i]
    | L4Seq l -> LSeq (map llll_compile l)
    | L4When (c, l) ->
        LSeq [llll_compile c; L (Arith ISZERO); LJmpI zero_nat; llll_compile l;
               LLab zero_nat]
    | L4If (c, l1, l2) ->
        LSeq [LSeq [llll_compile c; LJmpI zero_nat; llll_compile l2;
                     LJmp one_nat; LLab zero_nat; llll_compile l1;
                     LLab one_nat]]
    | L4While (c, l) ->
        LSeq [LSeq [LSeq [LLab zero_nat; llll_compile c; LJmpI one_nat;
                           LJmp (nat_of_integer (Big_int.big_int_of_int 2));
                           LLab one_nat; llll_compile l; LJmp zero_nat;
                           LLab (nat_of_integer (Big_int.big_int_of_int 2))]]]
    | L4Arith (LAPlus, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith ADD)])
    | L4Arith (LAExp, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith EXP)])
    | L4Arith (LADiv, ls) -> LSeq (map llll_compile (rev ls) @ [L (Arith DIV)])
    | L4Comp (LCEq, l1, l2) ->
        LSeq [llll_compile l2; llll_compile l1; L (Arith Inst_EQ)];;

let rec mypeel
  = function [] -> Some []
    | None :: uu -> None
    | Some h :: t ->
        (match mypeel t with None -> None | Some ta -> Some (h :: ta));;

let rec zero_word _A = word_of_int _A zero_int;;

let base_interlude_size : nat = nat_of_integer (Big_int.big_int_of_int 9);;

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
            [Stack (PUSH_N (output_address zero_nat))] @
              [Memory CODECOPY] @
                [Stack (PUSH_N (output_address zero_nat))] @
                  [Misc RETURN] @ payload;;

let rec codegena
  = function (uu, La (uv, i)) -> [i]
    | (uw, LLaba (ux, uy)) -> [Pc JUMPDEST]
    | (uz, LJmpa (a, va, s)) -> [Stack (PUSH_N (output_address a)); Pc JUMP]
    | (vb, LJmpIa (a, vc, vd)) -> [Stack (PUSH_N (output_address a)); Pc JUMPI]
    | (ve, LSeqa (vf, ls)) -> maps codegena ls;;

let rec codegen ls = maps inst_code (codegena ls);;

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
                   | (x, LJmpa (e, idx, s)) -> (x, LJmpa (zero_nat, idx, s))
                   | (x, LJmpIa (e, idx, s)) -> (x, LJmpIa (zero_nat, idx, s))
                   | (x, LSeqa (e, ls)) -> (x, LSeqa (e, map ll4_init ls));;

let rec ll_phase1
  x0 i = match x0, i with
    L inst, i ->
      (((i, plus_nat i (nat (inst_size inst))), La ((), inst)),
        plus_nat i (nat (inst_size inst)))
    | LLab idx, i ->
        (((i, plus_nat i one_nat), LLaba ((), idx)), plus_nat one_nat i)
    | LJmp idx, i ->
        (((i, plus_nat (nat_of_integer (Big_int.big_int_of_int 2)) i),
           LJmpa ((), idx, zero_nat)),
          plus_nat (nat_of_integer (Big_int.big_int_of_int 2)) i)
    | LJmpI idx, i ->
        (((i, plus_nat (nat_of_integer (Big_int.big_int_of_int 2)) i),
           LJmpIa ((), idx, zero_nat)),
          plus_nat (nat_of_integer (Big_int.big_int_of_int 2)) i)
    | LSeq ls, i ->
        (let (lsa, ia) = ll_phase1_seq ls i in (((i, ia), LSeqa ((), lsa)), ia))
and ll_phase1_seq
  x0 i = match x0, i with [], i -> ([], i)
    | h :: t, i -> (let (ha, ia) = ll_phase1 h i in
                    let a = ll_phase1_seq t ia in
                    let (ta, aa) = a in
                     (ha :: ta, aa));;

let rec ll_pass1 l = fst (ll_phase1 l zero_nat);;

let rec ll_get_label
  vd ve = match vd, ve with [], ve -> None
    | (vb, La (vf, vg)) :: va, [] -> None
    | (vb, LJmpa (vf, vg, vh)) :: va, [] -> None
    | (vb, LJmpIa (vf, vg, vh)) :: va, [] -> None
    | (vb, LSeqa (vf, vg)) :: va, [] -> None
    | vd, [] -> None
    | (v, La (vd, ve)) :: ls, va :: vb ->
        (if equal_nat va zero_nat then None
          else ll_get_label ls
                 (minus_nat (suc (minus_nat va one_nat)) one_nat :: vb))
    | (v, LJmpa (vd, ve, vf)) :: ls, va :: vb ->
        (if equal_nat va zero_nat then None
          else ll_get_label ls
                 (minus_nat (suc (minus_nat va one_nat)) one_nat :: vb))
    | (v, LJmpIa (vd, ve, vf)) :: ls, va :: vb ->
        (if equal_nat va zero_nat then None
          else ll_get_label ls
                 (minus_nat (suc (minus_nat va one_nat)) one_nat :: vb))
    | (uy, LSeqa (uz, lsdec)) :: ls, va :: p ->
        (if equal_nat va zero_nat then ll_get_label lsdec p
          else ll_get_label ls
                 (minus_nat (suc (minus_nat va one_nat)) one_nat :: p))
    | ((x, uu), LLaba (uv, uw)) :: ux, [v] ->
        (if equal_nat v zero_nat then Some x
          else ll_get_label ux [minus_nat (suc (minus_nat v one_nat)) one_nat])
    | (vb, LLaba (ve, vf)) :: ls, v :: va :: vc ->
        (if equal_nat v zero_nat then None
          else ll_get_label ls
                 (minus_nat (suc (minus_nat v one_nat)) one_nat :: va :: vc));;

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

let rec encode_size n = plus_nat (nat (log256floor (int_of_nat n))) one_nat;;

let rec ll3_resolve_jump
  x0 oaddr n rel absol = match x0, oaddr, n, rel, absol with
    (uu, LJmpa (e, idx, s)) :: ls, None, n, rel, absol ->
      (if equal_nat (plus_nat idx one_nat) (size_list rel)
        then JFail (n :: absol)
        else ll3_resolve_jump ls None (plus_nat n one_nat) rel absol)
    | (uv, LJmpa (e, idx, s)) :: ls, Some addr, n, rel, absol ->
        (if equal_nat idx (size_list rel)
          then (if less_nat s (encode_size addr) then JBump (n :: absol)
                 else (if equal_nat s (encode_size addr)
                        then ll3_resolve_jump ls (Some addr)
                               (plus_nat n one_nat) rel absol
                        else JFail (n :: absol)))
          else ll3_resolve_jump ls (Some addr) (plus_nat n one_nat) rel absol)
    | (uw, LJmpIa (e, idx, s)) :: ls, None, n, rel, absol ->
        (if equal_nat (plus_nat idx one_nat) (size_list rel)
          then JFail (n :: absol)
          else ll3_resolve_jump ls None (plus_nat n one_nat) rel absol)
    | (ux, LJmpIa (e, idx, s)) :: ls, Some addr, n, rel, absol ->
        (if equal_nat idx (size_list rel)
          then (if less_nat s (encode_size addr) then JBump (n :: absol)
                 else (if equal_nat s (encode_size addr)
                        then ll3_resolve_jump ls (Some addr)
                               (plus_nat n one_nat) rel absol
                        else JFail (n :: absol)))
          else ll3_resolve_jump ls (Some addr) (plus_nat n one_nat) rel absol)
    | (uy, LSeqa ([], lsdec)) :: ls, oaddr, n, rel, absol ->
        (match ll3_resolve_jump lsdec oaddr zero_nat (n :: rel) (n :: absol)
          with JSuccess ->
            (match ll3_resolve_jump lsdec None zero_nat [] (n :: absol)
              with JSuccess ->
                ll3_resolve_jump ls oaddr (plus_nat n one_nat) rel absol
              | JFail a -> JFail a | JBump a -> JBump a)
          | JFail a -> JFail a | JBump a -> JBump a)
    | (uz, LSeqa (v :: va, lsdec)) :: ls, oaddr, n, rel, absol ->
        (match ll3_resolve_jump lsdec oaddr zero_nat (n :: rel) (n :: absol)
          with JSuccess ->
            (match ll_get_label lsdec (v :: va) with None -> JFail absol
              | Some newaddr ->
                (match
                  ll3_resolve_jump lsdec (Some newaddr) zero_nat [] (n :: absol)
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
      (match e with [] -> ll3_resolve_jump lsdec None zero_nat [] []
        | a :: lista ->
          (match ll_get_label lsdec (a :: lista) with None -> JFail []
            | Some aa -> ll3_resolve_jump lsdec (Some aa) zero_nat [] []))
    | (v, La (vb, vc)) -> JFail []
    | (v, LLaba (vb, vc)) -> JFail []
    | (v, LJmpa (vb, vc, vd)) -> JFail []
    | (v, LJmpIa (vb, vc, vd)) -> JFail [];;

let rec ll3_inc_jump
  x0 n c = match x0, n, c with
    ((xa, x), LJmpa (e, idx, s)) :: ls, n, [c] ->
      (if equal_nat n c
        then (((xa, plus_nat x one_nat), LJmpa (e, idx, plus_nat s one_nat)) ::
                ll3_bump one_nat ls,
               true)
        else (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [c] in
               (((xa, x), LJmpa (e, idx, s)) :: lsa, a)))
    | ((xa, x), LJmpIa (e, idx, s)) :: ls, n, [c] ->
        (if equal_nat n c
          then (((xa, plus_nat x one_nat),
                  LJmpIa (e, idx, plus_nat s one_nat)) ::
                  ll3_bump one_nat ls,
                 true)
          else (let (lsa, a) = ll3_inc_jump ls (plus_nat n one_nat) [c] in
                 (((xa, x), LJmpIa (e, idx, s)) :: lsa, a)))
    | ((xa, x), LSeqa (e, lsdec)) :: ls, n, c :: cs ->
        (if equal_nat n c
          then (match ll3_inc_jump lsdec zero_nat cs
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
      (match ll3_inc_jump lsdec zero_nat c
        with (lsdeca, true) -> ((xa, plus_nat x one_nat), LSeqa (e, lsdeca))
        | (_, false) -> ((xa, x), LSeqa (e, lsdec)))
    | (v, La (vb, vc)), uu -> (v, La (vb, vc))
    | (v, LLaba (vb, vc)), uu -> (v, LLaba (vb, vc))
    | (v, LJmpa (vb, vc, vd)), uu -> (v, LJmpa (vb, vc, vd))
    | (v, LJmpIa (vb, vc, vd)), uu -> (v, LJmpIa (vb, vc, vd));;

let rec process_jumps_loop
  v uu =
    (if equal_nat v zero_nat then None
      else (match ll3_resolve_jump_wrap uu with JSuccess -> Some uu
             | JFail _ -> None
             | JBump c ->
               process_jumps_loop
                 (minus_nat (suc (minus_nat v one_nat)) one_nat)
                 (ll3_inc_jump_wrap uu (rev c))));;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

let rec ll3_consume_label
  p n x2 = match p, n, x2 with p, n, [] -> Some ([], [])
    | p, n, (x, LLaba (b, idx)) :: ls ->
        (if equal_nat idx (size_list p)
          then (if equal_bool b false
                 then Some ((x, LLaba (true, idx)) :: ls, n :: p) else None)
          else (match ll3_consume_label p (plus_nat n one_nat) ls
                 with None -> None
                 | Some (lsa, pa) -> Some ((x, LLaba (b, idx)) :: lsa, pa)))
    | p, n, (x, LSeqa (e, lsdec)) :: ls ->
        (match ll3_consume_label (n :: p) zero_nat lsdec with None -> None
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
      (match ll3_consume_label [] zero_nat ls with None -> None
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

let rec pipelinea
  l n = (match ll3_assign_label (ll3_init (ll_pass1 l)) with None -> None
          | Some la ->
            (match process_jumps_loop n la with None -> None
              | Some lb ->
                (match write_jump_targets [] (ll4_init lb) with None -> None
                  | Some a -> Some a)));;

let rec pipeline
  l n = (match pipelinea l n with None -> None | Some la -> Some (codegen la));;

let rec get_process_jumps_fuela
  = function
    (uu, LJmpa (uv, uw, s)) ->
      minus_nat (nat_of_integer (Big_int.big_int_of_int 32)) s
    | (ux, LJmpIa (uy, uz, s)) ->
        minus_nat (nat_of_integer (Big_int.big_int_of_int 32)) s
    | (va, LSeqa (vb, ls)) ->
        foldl (fun a x -> plus_nat a (get_process_jumps_fuela x)) zero_nat ls
    | (v, La (vb, vd)) -> zero_nat
    | (v, LLaba (vb, vd)) -> zero_nat;;

let rec get_process_jumps_fuel
  l = plus_nat one_nat (get_process_jumps_fuela l);;

let rec llll_combine_payload_sub
  fuel presz paysz startbytes endbytes =
    (if equal_nat fuel zero_nat then None
      else (if equal_nat (encode_size paysz) endbytes
             then (if equal_nat
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
  = plus_nat (nat_of_integer (Big_int.big_int_of_int 32))
      (nat_of_integer (Big_int.big_int_of_int 32));;

let default_llll_funs : (char list * (llll list -> llll option)) list
  = [(['s'; 'e'; 'q'], (fun l -> Some (L4Seq l)));
      (['i'; 'f'],
        (fun a ->
          (match a with [] -> None | [_] -> None | [_; _] -> None
            | [c; br1; br2] -> Some (L4If (c, br1, br2))
            | _ :: _ :: _ :: _ :: _ -> None)));
      (['w'; 'h'; 'e'; 'n'],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [c; br] -> Some (L4When (c, br)) | _ :: _ :: _ :: _ -> None)));
      (['+'], (fun l -> Some (L4Arith (LAPlus, l))));
      (['-'], (fun l -> Some (L4Arith (LAMinus, l))));
      (['*'], (fun l -> Some (L4Arith (LATimes, l))));
      (['d'; 'i'; 'v'], (fun l -> Some (L4Arith (LADiv, l))));
      (['e'; 'x'; 'p'], (fun l -> Some (L4Arith (LAExp, l))));
      (['/'], (fun l -> Some (L4Arith (LADiv, l))));
      (['%'], (fun l -> Some (L4Arith (LAMod, l))));
      (['&'], (fun l -> Some (L4Arith (LAAnd, l))));
      (['|'], (fun l -> Some (L4Arith (LAOr, l))));
      (['^'], (fun l -> Some (L4Arith (LAXor, l))));
      (['~'], (fun l -> Some (L4Arith (LANot, l))));
      (['&'; '&'], (fun l -> Some (L4Logic (LLAnd, l))));
      (['|'; '|'], (fun l -> Some (L4Logic (LLOr, l))));
      (['!'], (fun l -> Some (L4Logic (LLNot, l))));
      (['='],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [lhs; rhs] -> Some (L4Comp (LCEq, lhs, rhs))
            | _ :: _ :: _ :: _ -> None)));
      (['m'; 's'; 't'; 'o'; 'r'; 'e'],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [loc; sz] -> Some (L4I2 (Memory MSTORE, loc, sz))
            | _ :: _ :: _ :: _ -> None)));
      (['r'; 'e'; 't'; 'u'; 'r'; 'n'],
        (fun a ->
          (match a with [] -> None | [_] -> None
            | [loc; sz] -> Some (L4I2 (Misc RETURN, loc, sz))
            | _ :: _ :: _ :: _ -> None)));
      (['c'; 'a'; 'l'; 'l'; 'd'; 'a'; 't'; 'a'; 'l'; 'o'; 'a'; 'd'],
        (fun a ->
          (match a with [] -> None
            | [loc] -> Some (L4I1 (Stack CALLDATALOAD, loc))
            | _ :: _ :: _ -> None)))];;

let rec llll_parse1_default
  st = (match llll_parse1 default_llll_funs st with None -> None
         | Some (l, (x, _)) -> Some (l, x));;

let rec llll_parse_complete
  s = (match llll_parse0 s with None -> None
        | Some a -> llll_parse1_default a);;

let rec pipelineb
  l n = (match pipelinea l n with None -> None
          | Some la -> Some (codegena la));;

let rec fourL_compiler_string
  s = (match llll_parse_complete s with None -> None
        | Some (l4pre, None) ->
          (match
            pipeline (llll_compile l4pre)
              (get_process_jumps_fuel (ll_pass1 (llll_compile l4pre)))
            with None -> None | Some wl -> Some (hexwrite wl))
        | Some (l4pre, Some l4pay) ->
          (match
            pipelineb (llll_compile l4pre)
              (get_process_jumps_fuel (ll_pass1 (llll_compile l4pre)))
            with None -> None
            | Some il_pre ->
              (match
                pipelineb (llll_compile l4pay)
                  (get_process_jumps_fuel (ll_pass1 (llll_compile l4pay)))
                with None -> None
                | Some il_pay ->
                  (match
                    llll_combine_payload_sub combine_payload_fuel (ilsz il_pre)
                      (ilsz il_pay) zero_nat zero_nat
                    with None -> None
                    | Some (startbytes, endbytes) ->
                      Some (hexwrite
                             (il2wl
                               (makeInterlude startbytes endbytes il_pre
                                 il_pay)))))));;

let rec compiler
  l = (match
        fourL_compiler_string
          (let s = l in let rec exp i l = if i < 0 then l else exp (i - 1) (String.get s i :: l) in exp (String.length s - 1) [])
        with None -> None
        | Some s ->
          Some (let l = s in let res = String.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> String.set res i c; imp (i + 1) l in imp 0 l));;

end;; (*struct FourL*)

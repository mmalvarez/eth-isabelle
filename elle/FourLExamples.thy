theory FourLExamples
imports Main FourL
begin

value "llll_parse_complete
''(if 1 2 3)''"

value "llll_parse_complete
''(seq)''"

value "fourL_compiler_elle
''(if 1 2 3)''"

value "fourL_compiler_string
''(if 1 2 3)
''"

value "fourL_compiler_string
''(seq)
''"


value "fourL_compiler_string
''(for (mstore 0 20)
       (> (mload 0) 0)
       3
       (mstore 0 (- (mload 0) 1)))''"

       value "fourL_compiler_elle
''(for (mstore 0 20)
       (> (mload 0) 0)
       3
       (mstore 0 (- (mload 0) 1)))''"
       
value "fourL_compiler_elle
''
(if 1
 (seq
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
)
3)
''"

value "fourL_compiler_string
''
(if 1
 (seq
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
  2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2
)
3)
''"

value "fourL_compiler_string
''(lit 0x00 0x10)
''"

value "fourL_compiler_string
(''(lit 0x00 '' @ [quote] @ ''abc def g'' @ [quote] @ '')'')"

value "fourL_compiler_string
(''(lit 0x00 '' @ [quote] @ ''())('' @ [quote] @ '')'')"

value "fourL_compiler_string
''(seq
    (def 'a 1)
    (def 'b () (+ a 1))
    b)
''"

(* echo *)

value "fourL_compiler_string

''(seq
  (def 'scratch 0x00)
  (def 'identity 0xac37eebb) ; function hash, for ABI compliance
  (def 'function (function-hash code-body)
    (when (= (div (calldataload 0x00)
                  (exp 2 224)) function-hash)
      code-body))
  (returnlll
    (function identity
      (seq
        (mstore scratch (calldataload 0x04))
        (return scratch 32)))))
 ''"

 value "fourL_parse_elle

''(seq
  (def 'scratch 0x00)
  (def 'identity 0xac37eebb) ; function hash, for ABI compliance
  (def 'function (function-hash code-body)
    (when (= (div (calldataload 0x00)
                  (exp 2 224)) function-hash)
      code-body))
  (returnlll
    (function identity
      (seq
        (mstore scratch (calldataload 0x04))
        (return scratch 32)))))
 ''"


(* ENS *)


end
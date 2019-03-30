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


(* ENS *)


end
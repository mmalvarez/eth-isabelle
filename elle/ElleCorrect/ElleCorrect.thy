theory ElleCorrect
  imports "../ElleSemantics" "Valid4"
begin

(* Correctness means:
- if we get a successful result out of ll sem (of final form emitted from compiler)
  - in a certain initial state (certain gas)
  - with a certain amount of fuel
- then we get the same successful result out of program_sem
  - with the same fuel parameter
    - (in practice program_sem takes less fuel)

Lemmas needed:
Relationship between
- ll_get_by_loc
- ll_get_node
- "!" x in list of bytecodes output by codegen
- program_content applied to x
*)
end
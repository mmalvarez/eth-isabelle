theory ElleCompilerVerified
  imports Main "ElleCorrect.ElleAltSemantics"
  begin

  fun get_insts' ::
    "program \<Rightarrow> int \<Rightarrow> int \<Rightarrow> inst list option" where
  "get_insts' p start tot =
    (if tot <= 0 then Some []
         else (case (program_content p start) of
                  None \<Rightarrow> None
                  | Some i \<Rightarrow> (case get_insts' p (start + 1) (tot - 1) of
                      None \<Rightarrow> None
                      | Some il \<Rightarrow> Some (i#il))))"
  
  definition get_insts ::
    "constant_ctx \<Rightarrow> inst list option" where
    "get_insts c =
      get_insts' (cctx_program c) 0 (program_length (cctx_program c))"

  fun inst_code_clean :: "inst \<Rightarrow> 8 word list option" where
    "inst_code_clean (Stack (PUSH_N lst) ) =
     (case (stack_inst_code (PUSH_N lst)) of
        [] \<Rightarrow> None
        | h#t \<Rightarrow> Some [h])"
    | "inst_code_clean i = Some (inst_code i)"
      
    fun codegen_clean ::
        "inst list \<Rightarrow> 8 word list option" where
      "codegen_clean [] = Some []"
      | "codegen_clean (h#t) = 
        (case inst_code_clean h of
          None \<Rightarrow> None
          | Some wl \<Rightarrow> (case codegen_clean t of
            None \<Rightarrow> None
            | Some wls \<Rightarrow> Some (wl @ wls)))"

  (* idea: do ellecompile, except that we need to
use ll4_load_lst_validate *)
(* then, use the primitives here to dump the code to output *)
definition ellecompilev_1_4 :: "ll1 \<Rightarrow> ll4 option" where
"ellecompilev_1_4 l =
  (if ll1_valid l then
    (case ellecompile_untrusted l of
      Some l' \<Rightarrow>
      (if check_ll3 l' then
        (if ll4_validate_jump_targets [] l' then
          Some l'
          else None)
       else None)
     | _ \<Rightarrow> None)
   else None)"

definition ellecompilev_4_cc :: "ll4 \<Rightarrow> constant_ctx option" where          
"ellecompilev_4_cc l =
  ll4_load_lst_validate (prog_init_cctx []) l
"

definition ellecompilev_cc_il :: "constant_ctx \<Rightarrow> inst list option" where
"ellecompilev_cc_il c = get_insts c"

definition ellecompilev_il_wl :: "inst list \<Rightarrow> 8 word list option" where
"ellecompilev_il_wl il = codegen_clean il"

definition ellecompilev_1_il :: "ll1 \<Rightarrow> inst list option" where
    "ellecompilev_1_il l =
      (case ellecompilev_1_4 l of
        None \<Rightarrow> None
        | Some l4 \<Rightarrow> (case ellecompilev_4_cc l4 of
                        None \<Rightarrow> None
                        | Some cc \<Rightarrow> ellecompilev_cc_il cc))"
    
definition ellecompilev_full :: "ll1 \<Rightarrow> 8 word list option" where
"ellecompilev_full l =
  (case ellecompilev_1_4 l of
   None \<Rightarrow> None
   | Some l4 \<Rightarrow> (case ellecompilev_4_cc l4 of
               None \<Rightarrow> None
               | Some cc \<Rightarrow> (case ellecompilev_cc_il cc of
                              None \<Rightarrow> None
                              | Some il \<Rightarrow> ellecompilev_il_wl il)))"
            
  (* pipeline *)
  (* elle_compiler into ll4
     valid3' check
     validate_jump_targets
     ll4_load_lst_validate *)
  (* postprocessing:
     extract list out from ll4
     output bytes, using inst_code
     - only output head byte of PUSH instruction (override)
  *)

  (* elle_compiler_ *)
  
end
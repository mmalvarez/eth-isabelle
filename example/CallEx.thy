theory CallEx

imports
  Dispatcher
  "HOL-Eisbach.Eisbach"
  "../BlockFacts"
begin

\<comment>\<open>
squires $ cat call.sol 
pragma solidity ^0.4.24;

contract B {
	function f() pure public returns (uint256)
	{
		return 42;
	}
}

contract A {
    B b;
    uint256 v;

    constructor(address _b) public {
	b = B(_b);
	v = 0;
    }


    function callB() public returns (uint256)
    {
	    v = b.f();
    }

}
squires $ ./solc  call.sol --overwrite --bin-runtime -o res
squires $ for f in res/*.bin-runtime ; do cat $f ; echo ; done
608060405260043610610041576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806344fd4fa014610046575b600080fd5b34801561005257600080fd5b5061005b610071565b6040518082815260200191505060405180910390f35b60008060009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166326121ff06040518163ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401602060405180830381600087803b1580156100f857600080fd5b505af115801561010c573d6000803e3d6000fd5b505050506040513d602081101561012257600080fd5b8101908080519060200190929190505050600181905550905600a165627a7a72305820b098d684bc2516a3af5106f6efd38d926edb67ea42c065bd94a63e7e988f19980029
608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806326121ff0146044575b600080fd5b348015604f57600080fd5b506056606c565b6040518082815260200191505060405180910390f35b6000602a9050905600a165627a7a7230582056366c316c8eb1c2cb71b875b90a5eaf72d3069879bea637993dcf928cfb1cde0029
s

\<close>

definition A_addr :: "address" where
 "A_addr \<equiv> 0x42"
definition A_bytestr :: "byte list" where
 "A_bytestr \<equiv> bytes_of_hex_content ''608060405260043610610041576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806344fd4fa014610046575b600080fd5b34801561005257600080fd5b5061005b610071565b6040518082815260200191505060405180910390f35b60008060009054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff166326121ff06040518163ffffffff167c0100000000000000000000000000000000000000000000000000000000028152600401602060405180830381600087803b1580156100f857600080fd5b505af115801561010c573d6000803e3d6000fd5b505050506040513d602081101561012257600080fd5b8101908080519060200190929190505050600181905550905600a165627a7a72305820b098d684bc2516a3af5106f6efd38d926edb67ea42c065bd94a63e7e988f19980029''"

definition B_addr :: "address" where
 "B_addr \<equiv> 0x43"
definition B_bytestr :: "byte list" where
 "B_bytestr \<equiv> bytes_of_hex_content ''608060405260043610603f576000357c0100000000000000000000000000000000000000000000000000000000900463ffffffff16806326121ff0146044575b600080fd5b348015604f57600080fd5b506056606c565b6040518082815260200191505060405180910390f35b6000602a9050905600a165627a7a7230582056366c316c8eb1c2cb71b875b90a5eaf72d3069879bea637993dcf928cfb1cde0029
s''"


value "parse_bytes A_bytestr"

definition
 "A_insts \<equiv> [Stack (PUSH_N [0x80]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [4]), Info CALLDATASIZE, Arith inst_LT,
  Stack (PUSH_N [0, 0x41]), Pc JUMPI, Stack (PUSH_N [0]), Stack CALLDATALOAD,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), Swap 0, Arith DIV,
  Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Bits inst_AND, Dup 0, Stack (PUSH_N [0x44, 0xFD, 0x4F, 0xA0]), Arith inst_EQ,
  Stack (PUSH_N [0, 0x46]), Pc JUMPI, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Info CALLVALUE, Dup 0,
  Arith ISZERO, Stack (PUSH_N [0, 0x52]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack POP,
  Stack (PUSH_N [0, 0x5B]), Stack (PUSH_N [0, 0x71]), Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Dup 2, Dup 1,
  Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD, Swap 1, Stack POP, Stack POP, Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1,
  Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Stack (PUSH_N [0]), Swap 0, Storage SLOAD, Swap 0,
  Stack (PUSH_N [1, 0]), Arith EXP, Swap 0, Arith DIV,
  Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND,
  Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]),
  Bits inst_AND, Stack (PUSH_N [0x26, 0x12, 0x1F, 0xF0]), Stack (PUSH_N [0x40]), Memory MLOAD, Dup 1,
  Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Bits inst_AND,
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), Arith MUL, Dup 1, Memory MSTORE,
  Stack (PUSH_N [4]), Arith ADD, Stack (PUSH_N [0x20]), Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Dup 3, Arith SUB, Dup 1,
  Stack (PUSH_N [0]), Dup 7, Dup 0, Info EXTCODESIZE, Arith ISZERO, Dup 0, Arith ISZERO, Stack (PUSH_N [0, 0xF8]), Pc JUMPI,
  Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack POP, Info GAS, Misc CALL, Arith ISZERO, Dup 0, Arith ISZERO,
  Stack (PUSH_N [1, 0xC]), Pc JUMPI, Unknown 0x3D, Stack (PUSH_N [0]), Dup 0, Unknown 0x3E, Unknown 0x3D, Stack (PUSH_N [0]), Unknown 0xFD,
  Pc JUMPDEST, Stack POP, Stack POP, Stack POP, Stack POP, Stack (PUSH_N [0x40]), Memory MLOAD, Unknown 0x3D, Stack (PUSH_N [0x20]), Dup 1,
  Arith inst_LT, Arith ISZERO, Stack (PUSH_N [1, 0x22]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST, Dup 1, Arith ADD,
  Swap 0, Dup 0, Dup 0, Memory MLOAD, Swap 0, Stack (PUSH_N [0x20]), Arith ADD, Swap 0, Swap 2, Swap 1, Swap 0, Stack POP, Stack POP,
  Stack POP, Stack (PUSH_N [1]), Dup 1, Swap 0, Storage SSTORE, Stack POP, Swap 0, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Unknown 0xB0, Swap 8, Unknown 0xD6, Dup 4, Unknown 0xBC, Unknown 0x25,
  Bits inst_AND, Log LOG3, Unknown 0xAF, Memory MLOAD, Arith MOD, Unknown 0xF6, Unknown 0xEF, Unknown 0xD3, Dup 0xD, Swap 2,
  Stack (PUSH_N [0xDB, 0x67, 0xEA, 0x42, 0xC0, 0x65, 0xBD, 0x94, 0xA6, 0x3E, 0x7E, 0x98, 0x8F, 0x19, 0x98]), Misc STOP, Unknown 0x29]"


definition
  bytestr_to_program :: "byte list \<Rightarrow> program" where
 "bytestr_to_program bstr \<equiv> program_of_lst (parse_bytes bstr)
                                              (\<lambda>xs i. if i < length xs then Some (xs ! nat i) else None)"

definition
  user :: address where
 "user = 0x88"

definition transaction_nonce :: w256 where
 "transaction_nonce \<equiv> 0x13"

definition
 "acc_bal = 0x1000000000000"

definition accounts :: "address \<Rightarrow> block_account"  where
 "accounts \<equiv> undefined(
    A_addr := \<lparr>   block_account_address = A_addr, 
                  block_account_storage = (\<lambda>_. 0),
                  block_account_code = bytestr_to_program A_bytestr,
                  block_account_balance = 0,
                  block_account_nonce = undefined,
                  block_account_exists = True,
                  block_account_hascode = True \<rparr> ,
    B_addr := \<lparr>   block_account_address = B_addr, 
                  block_account_storage = (\<lambda>_. 0),
                  block_account_code = bytestr_to_program B_bytestr,
                  block_account_balance = 0,
                  block_account_nonce = undefined,
                  block_account_exists = True,
                  block_account_hascode = True \<rparr>,
   user := \<lparr>   block_account_address = user, 
                  block_account_storage = (\<lambda>_. 0),
                  block_account_code = undefined,
                  block_account_balance = acc_bal,
                  block_account_nonce = transaction_nonce,
                  block_account_exists = True,
                  block_account_hascode = False \<rparr>)"

term start_transaction
term global_sem

definition
 "tr_gas_limit' \<equiv> 0x1000000"

definition tr :: transaction where
 "tr \<equiv> \<lparr> tr_from = user, tr_to = Some A_addr, tr_gas_limit = tr_gas_limit', tr_gas_price= 100, tr_value = 0, tr_nonce = transaction_nonce, tr_data = [] \<rparr>"

definition coinbase :: address where
 "coinbase \<equiv> 0x88888888888888"

definition "block_gaslimit' \<equiv> 0x1000000000000000"

definition bi :: block_info where
 "bi \<equiv> \<lparr> block_blockhash = undefined, block_coinbase = coinbase, block_timestamp = 0x6660000000, block_number= 100000000, block_difficulty = 0, block_gaslimit = block_gaslimit' \<rparr>"

lemmas addrs = A_addr_def B_addr_def user_def

schematic_goal start_trans:
 "start_transaction tr accounts bi = Continue ?s"
  apply (simp add: start_transaction_def Let_def)
  apply (simp add: tr_def)
  apply (rule conjI)
  
  apply (simp add: tr_def accounts_def addrs) 
   apply (clarsimp simp: calc_igas_def unat_arith_simps tr_gas_limit'_def)
  apply clarsimp
  apply (rule conjI)
  apply (simp add: tr_def accounts_def addrs) 
   apply (clarsimp simp: calc_igas_def unat_arith_simps homestead_block_def )
   apply (clarsimp simp: bi_def)
   apply (clarsimp simp: block_gaslimit'_def tr_gas_limit'_def)
  apply clarsimp
  apply (rule conjI)
  apply (simp add: tr_def accounts_def addrs) 
   apply (clarsimp simp:  unat_arith_simps homestead_block_def )
   apply (clarsimp simp: bi_def)
   apply (clarsimp simp: acc_bal_def tr_gas_limit'_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: accounts_def)
  apply (clarsimp simp: Let_def)
  apply (rule refl)
  done

lemma addrs_uniq:
 "A_addr \<noteq> user"
 "B_addr \<noteq> user"
 "A_addr \<noteq> B_addr"
  by (simp add: addrs)+

lemma update_world_simp:
  "x \<noteq> y
  \<Longrightarrow> (update_world accs x (accs x \<lparr>block_account_nonce := n, block_account_balance := m\<rparr>) y) = accs y"
  by (simp add: update_world_def)


lemma build_cctx_update_world:
  "(build_cctx0 (update_world accounts user
               (accounts user
                \<lparr>block_account_nonce := transaction_nonce + 1,
                   block_account_balance := block_account_balance (accounts user) - 0x64 * tr_gas_limit'\<rparr>)
               A_addr)) = \<lparr>cctx_program = bytestr_to_program A_bytestr, cctx_this = A_addr, cctx_hash_filter = \<lambda>x. True\<rparr>"
  apply (subst update_world_simp, simp add: addrs_uniq[symmetric])
  apply (simp add: accounts_def addrs_uniq)
  apply (simp add: build_cctx0_def)
  done

lemma
" program_sem_t
        \<lparr>cctx_program = bytestr_to_program A_bytestr, cctx_this = A_addr, cctx_hash_filter = \<lambda>x. True\<rparr> net
        (InstructionContinue
          \<lparr>vctx_stack = [], vctx_memory = empty_memory, vctx_memory_usage = 0,
             vctx_storage = block_account_storage (accounts A_addr), vctx_pc = 0,
             vctx_balance =
               \<lambda>addr.
                  block_account_balance
                   (update_world
                     (update_world accounts user
                       (accounts user
                        \<lparr>block_account_nonce := transaction_nonce + 1,
                           block_account_balance := block_account_balance (accounts user) - 0x64000000\<rparr>))
                     A_addr (accounts A_addr) addr),
             vctx_caller = user, vctx_value_sent = 0, vctx_data_sent = [],
             vctx_storage_at_call = block_account_storage (accounts A_addr),
             vctx_balance_at_call =
               \<lambda>addr.
                  block_account_balance
                   (update_world
                     (update_world accounts user
                       (accounts user
                        \<lparr>block_account_nonce := transaction_nonce + 1,
                           block_account_balance := block_account_balance (accounts user) - 0x64000000\<rparr>))
                     A_addr (accounts A_addr) addr),
             vctx_origin = user,
             vctx_ext_program =
               \<lambda>addr.
                  block_account_code
                   (update_world
                     (update_world accounts user
                       (accounts user
                        \<lparr>block_account_nonce := transaction_nonce + 1,
                           block_account_balance := block_account_balance (accounts user) - 0x64000000\<rparr>))
                     A_addr (accounts A_addr) addr),
             vctx_block =
               \<lparr>block_blockhash = undefined, block_coinbase = coinbase, block_timestamp = 0x6660000000,
                  block_number = 0x5F5E100, block_difficulty = 0, block_gaslimit = block_gaslimit'\<rparr>,
             vctx_gas = 16756216,
             vctx_account_existence =
               \<lambda>addr.
                  block_account_exists
                   (update_world
                     (update_world accounts user
                       (accounts user
                        \<lparr>block_account_nonce := transaction_nonce + 1,
                           block_account_balance := block_account_balance (accounts user) - 0x64000000\<rparr>))
                     A_addr (accounts A_addr) addr),
             vctx_touched_storage_index = [], vctx_logs = [], vctx_refund = 0, vctx_gasprice = 0x64\<rparr>) =
       InstructionToEnvironment x21 x22 x23"
  oops

lemma A_bytestr_sz:
 "fst (last (add_address A_insts)) < 2 ^ 256"
  by eval

theorem triple_soundness:
"bytecode \<noteq> [] \<Longrightarrow>
fst (last (add_address bytecode)) < 2 ^ 256 \<Longrightarrow>
bbtriple net pre (build_blocks bytecode) post \<Longrightarrow>
triple_sem_t net pre (set (add_address bytecode)) post"
  sorry

lemma parse_bytes_not_Nil:
 "xs \<noteq> [] \<Longrightarrow> parse_bytes xs \<noteq> []"
  by (case_tac xs; clarsimp split: parse_byte_result.splits)

lemma bytes_of_hex_content_not_Nil:
"length xs > 1 \<Longrightarrow>
 bytes_of_hex_content xs \<noteq> []"
  apply (case_tac xs; clarsimp)
  apply (rename_tac ys, case_tac ys; clarsimp)
  done


definition "blocks_A_insts \<equiv> build_blocks A_insts"
value "blocks_A_insts"
lemma blocks_A_insts_simp:
 "blocks_A_insts = [(0, [(0, Stack (PUSH_N [0x80])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE), (5, Stack (PUSH_N [4])), (7, Info CALLDATASIZE),
       (8, Arith inst_LT), (9, Stack (PUSH_N [0, 0x41]))],
   Jumpi),
  (13,
   [(13, Stack (PUSH_N [0])), (15, Stack CALLDATALOAD),
    (16, Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])), (46, Swap 0),
    (47, Arith DIV), (48, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (53, Bits inst_AND), (54, Dup 0),
    (55, Stack (PUSH_N [0x44, 0xFD, 0x4F, 0xA0])), (60, Arith inst_EQ), (61, Stack (PUSH_N [0, 0x46]))],
   Jumpi),
  (65, [(65, Pc JUMPDEST), (66, Stack (PUSH_N [0])), (68, Dup 0), (69, Unknown 0xFD)], Terminal),
  (70, [(70, Pc JUMPDEST), (71, Info CALLVALUE), (72, Dup 0), (73, Arith ISZERO), (74, Stack (PUSH_N [0, 0x52]))], Jumpi),
  (78, [(78, Stack (PUSH_N [0])), (80, Dup 0), (81, Unknown 0xFD)], Terminal),
  (82, [(82, Pc JUMPDEST), (83, Stack POP), (84, Stack (PUSH_N [0, 0x5B])), (87, Stack (PUSH_N [0, 0x71]))], Jump),
  (91,
   [(91, Pc JUMPDEST), (92, Stack (PUSH_N [0x40])), (94, Memory MLOAD), (95, Dup 0), (96, Dup 2), (97, Dup 1), (98, Memory MSTORE),
    (99, Stack (PUSH_N [0x20])), (101, Arith ADD), (102, Swap 1), (103, Stack POP), (104, Stack POP), (105, Stack (PUSH_N [0x40])),
    (107, Memory MLOAD), (108, Dup 0), (109, Swap 1), (110, Arith SUB), (111, Swap 0), (112, Misc RETURN)],
   Terminal),
  (113,
   [(113, Pc JUMPDEST), (114, Stack (PUSH_N [0])), (116, Dup 0), (117, Stack (PUSH_N [0])), (119, Swap 0), (120, Storage SLOAD),
    (121, Swap 0), (122, Stack (PUSH_N [1, 0])), (125, Arith EXP), (126, Swap 0), (127, Arith DIV),
    (128,
     Stack
      (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (149, Bits inst_AND),
    (150,
     Stack
      (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF])),
    (171, Bits inst_AND), (172, Stack (PUSH_N [0x26, 0x12, 0x1F, 0xF0])), (177, Stack (PUSH_N [0x40])), (179, Memory MLOAD), (180, Dup 1),
    (181, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (186, Bits inst_AND),
    (187, Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])), (217, Arith MUL),
    (218, Dup 1), (219, Memory MSTORE), (220, Stack (PUSH_N [4])), (222, Arith ADD), (223, Stack (PUSH_N [0x20])),
    (225, Stack (PUSH_N [0x40])), (227, Memory MLOAD), (228, Dup 0), (229, Dup 3), (230, Arith SUB), (231, Dup 1),
    (232, Stack (PUSH_N [0])), (234, Dup 7), (235, Dup 0), (236, Info EXTCODESIZE), (237, Arith ISZERO), (238, Dup 0), (239, Arith ISZERO),
    (240, Stack (PUSH_N [0, 0xF8]))],
   Jumpi),
  (244, [(244, Stack (PUSH_N [0])), (246, Dup 0), (247, Unknown 0xFD)], Terminal),
  (248, [(248, Pc JUMPDEST), (249, Stack POP), (250, Info GAS), (251, Misc CALL)], Terminal),
  (252, [(252, Arith ISZERO), (253, Dup 0), (254, Arith ISZERO), (255, Stack (PUSH_N [1, 0xC]))], Jumpi),
  (259, [(259, Unknown 0x3D)], Terminal), (260, [(260, Stack (PUSH_N [0])), (262, Dup 0), (263, Unknown 0x3E)], Terminal),
  (264, [(264, Unknown 0x3D)], Terminal), (265, [(265, Stack (PUSH_N [0])), (267, Unknown 0xFD)], Terminal),
  (268,
   [(268, Pc JUMPDEST), (269, Stack POP), (270, Stack POP), (271, Stack POP), (272, Stack POP), (273, Stack (PUSH_N [0x40])),
    (275, Memory MLOAD), (276, Unknown 0x3D)],
   Terminal),
  (277, [(277, Stack (PUSH_N [0x20])), (279, Dup 1), (280, Arith inst_LT), (281, Arith ISZERO), (282, Stack (PUSH_N [1, 0x22]))], Jumpi),
  (286, [(286, Stack (PUSH_N [0])), (288, Dup 0), (289, Unknown 0xFD)], Terminal),
  (290,
   [(290, Pc JUMPDEST), (291, Dup 1), (292, Arith ADD), (293, Swap 0), (294, Dup 0), (295, Dup 0), (296, Memory MLOAD), (297, Swap 0),
    (298, Stack (PUSH_N [0x20])), (300, Arith ADD), (301, Swap 0), (302, Swap 2), (303, Swap 1), (304, Swap 0), (305, Stack POP),
    (306, Stack POP), (307, Stack POP), (308, Stack (PUSH_N [1])), (310, Dup 1), (311, Swap 0), (312, Storage SSTORE), (313, Stack POP),
    (314, Swap 0)],
   Jump),
  (316, [(316, Misc STOP)], Terminal),
  (317, [(317, Log LOG1), (318, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (325, Arith SHA3), (326, Unknown 0xB0)], Terminal),
  (327, [(327, Swap 8), (328, Unknown 0xD6)], Terminal), (329, [(329, Dup 4), (330, Unknown 0xBC)], Terminal),
  (331, [(331, Unknown 0x25)], Terminal), (332, [(332, Bits inst_AND), (333, Log LOG3), (334, Unknown 0xAF)], Terminal),
  (335, [(335, Memory MLOAD), (336, Arith MOD), (337, Unknown 0xF6)], Terminal), (338, [(338, Unknown 0xEF)], Terminal),
  (339, [(339, Unknown 0xD3)], Terminal),
  (340,
   [(340, Dup 0xD), (341, Swap 2),
    (342, Stack (PUSH_N [0xDB, 0x67, 0xEA, 0x42, 0xC0, 0x65, 0xBD, 0x94, 0xA6, 0x3E, 0x7E, 0x98, 0x8F, 0x19, 0x98])), (358, Misc STOP)],
   Terminal),
  (359, [(359, Unknown 0x29)], Terminal)]"
  by eval

definition A_hash :: "32 word" where
 "A_hash \<equiv> 0x44fd4fa0"

lemma
  bit_mask_rev[simp]
  address_mask_ucast[simp] address_mask_ucast[simplified word_bool_alg.conj.commute, simp]
  ucast_and_w256_drop[simp]
  transfer_hash_def[simp]
  word_bool_alg.conj.commute[simp]
  length_word_rsplit_4[simp]
  ucast_160_upto_256_eq[simp]
  hash_diff[simp]
  eval_bit_mask[simp]
len_bytestr_simps[simp]
shows

 "\<exists>Q. bbtriple net
 ( program_counter 0 ** stack_height 0 **
   sent_data (bytestr A_hash) **
   sent_value 0 ** caller sender ** blk_num bn **
   memory_usage 0 ** continuing ** gas_pred 100000 **
   storage 0 B_ptr **
   storage 1 v **
   account_existence sender sender_ex  **
   account_existence to to_ex **
   memory (0::w256) m0x0 **
   memory (0x20::w256) m0x20 **
   memory (0x40::w256) (bytestr_to_w256 [x]) **
   memory (0x60::w256) (bytestr_to_w256 [y]) **
   log_number log_num **
   this_account this)
 (blocks_A_insts) (action (ContractCall args) ** Q)"
  including dispatcher_bundle
  apply (rule exI)
  apply (simp add: blocks_A_insts_simp)
  apply (simp add: bbtriple_def )
  apply (block_vcg; (solves \<open>clarsimp\<close>)?)
   apply (block_vcg)
  apply (simp add: bytestr_def length_word_rsplit_32)
   apply (simp add: A_hash_def)
  apply (block_vcg)

   apply (block_vcg)

    apply split_conds
  apply (simp add: A_hash_def bytestr_def)
    apply (block_vcg)


  apply (blocks_rule_vcg; (rule refl)?)
      apply triple_seq_vcg
             apply clarsimp
             apply order_sep_conj
  apply (sep_cancel)
             apply (sep_cancel)

             apply clarsimp
             apply (sep_cancel)
             apply (simp add: Gverylow_def pure_def)
             apply order_sep_conj
  apply (sep_cancel)
             apply (sep_cancel)
             apply (simp add: Gverylow_def pure_def)
  apply (sep_imp_solve simp: Gverylow_def)
             apply order_sep_conj
  apply (sep_cancel)
             apply order_sep_conj
  apply (sep_cancel)
             apply order_sep_conj
  apply (sep_cancel)
             apply order_sep_conj
  apply (sep_cancel)
             apply order_sep_conj
           apply (sep_cancel)
  apply (simp add: word_rcat_simps)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (order_sep_conj, sep_cancel)
  find_theorems length word_rsplit 32
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def)
  apply assumption
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
  apply sep_cancel
  apply sep_cancel
          apply sep_cancel
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
          apply sep_cancel
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
             apply (order_sep_conj, sep_cancel)
           apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps inst_size_def)
      apply (order_sep_conj, sep_cancel)
  apply simp
    apply (clarsimp simp: Gverylow_def length_word_rsplit_32 Cmem_def gas_simps Gmemory_def M_def word_rcat_simps inst_size_def)
  apply (rule conjI, rule refl, rule refl)
(*   apply triple_blocks_vcg
  apply (block_vcg)
 *)  apply split_conds
  apply (blocks_rule_vcg; (rule refl)?)
      apply triple_seq_vcg
             apply clarsimp
             apply order_sep_conj
  apply (sep_cancel)
             apply (sep_cancel)


          apply (sep_imp_solve2)
  apply (sep_imp_solve2)

  oops

lemma A_calls_B_spec:
  " triple_sem_t net P (set (add_address (A_insts))) Q"
  apply (rule triple_soundness)
   apply (simp add: A_insts_def)
  apply (simp only: A_bytestr_sz)
  sorry

lemma
  "sint (block_number bi) \<ge> homestead_block \<Longrightarrow> 
  global_sem net (case start_transaction tr accounts bi of Continue x \<Rightarrow> x) = Some v"
  apply clarsimp

  apply (rule context_conjI)
   apply (clarsimp simp: start_trans)
   apply (clarsimp simp: get_vctx_gas_def create_env_def)
   apply (clarsimp simp: calc_igas_def tr_gas_limit'_def)
  apply simp  
  apply (clarsimp simp add: Let_def split: instruction_result.splits)
  apply (rule conjI)
  apply (clarsimp split: global_state.split)
   apply (simp (no_asm) add: start_trans create_env_def)
  apply clarsimp
   apply (clarsimp simp: build_cctx_update_world)
   apply (subst update_world_simp, fastforce simp: addrs_uniq[symmetric])+
  apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp: global_step_def)
  apply (clarsimp simp: envstep_def Let_def)
    apply (clarsimp simp: tr_gas_limit'_def calc_igas_def bi_def homestead_block_def)
  apply (clarsimp simp add: program_sem_t_no_gas_not_continuing split: instruction_result.splits)
  apply (clarsimp simp: program_sem_t.simps vctx_next_instruction_def)
  using A_calls_B_spec[simplified triple_sem_t_def]
  
    apply (case_tac "global_step net _ ")
  oops

end

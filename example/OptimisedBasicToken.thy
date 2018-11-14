theory OptimisedBasicToken

imports
  Dispatcher
  "~~/src/HOL/Eisbach/Eisbach"

begin
(*
pragma solidity ^0.4.18;

import "./ERC20Basic.sol";
import "/home/samani/dev/ethereum/seed/zeppelin-solidity/contracts/math/SafeMath.sol";


/**
 * @title Basic token
 * @dev Basic version of StandardToken, with no allowances.
 */
contract BasicToken is ERC20Basic {
  using SafeMath for uint256;

  mapping(address => uint256) balances;

  uint256 totalSupply_;

  /**
  * @dev total number of tokens in existence
  */
  function totalSupply() public view returns (uint256) {
    return totalSupply_;
  }

  /**
  * @dev transfer token for a specified address
  * @param _to The address to transfer to.
  * @param _value The amount to be transferred.
  */
  function transfer(address _to, uint256 _value) public returns (bool) {
    require(_to != address(0));
    /* The following require is redundant with safe math
        assertion in SafeMath.sub.
    */
    // require(_value <= balances[msg.sender]);

    // SafeMath.sub will throw if there is not enough balance.
    balances[msg.sender] = balances[msg.sender].sub(_value);
    balances[_to] = balances[_to].add(_value);
    Transfer(msg.sender, _to, _value);
    return true;
  }

  /**
  * @dev Gets the balance of the specified address.
  * @param _owner The address to query the the balance of.
  * @return An uint256 representing the amount owned by the passed address.
  */
  function balanceOf(address _owner) public view returns (uint256 balance) {
    return balances[_owner];
  }

}

Compiled with:
 /usr/bin/solc --optimize --overwrite -o optimised-basic --bin-runtime --asm --hashes
  --allow-paths /home/samani/dev/ethereum/seed/zeppelin-solidity/contracts/math/ OptimisedBasicToken.sol

70a08231: balanceOf(address)
18160ddd: totalSupply()
a9059cbb: transfer(address,uint256)

*)
value"(parse_bytecode ''6060604052600436106100565763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166318160ddd811461005b57806370a0823114610080578063a9059cbb1461009f575b600080fd5b341561006657600080fd5b61006e6100d5565b60405190815260200160405180910390f35b341561008b57600080fd5b61006e600160a060020a03600435166100db565b34156100aa57600080fd5b6100c1600160a060020a03600435166024356100f6565b604051901515815260200160405180910390f35b60015490565b600160a060020a031660009081526020819052604090205490565b6000600160a060020a038316151561010d57600080fd5b600160a060020a033316600090815260208190526040902054610136908363ffffffff6101e316565b600160a060020a03338116600090815260208190526040808220939093559085168152205461016b908363ffffffff6101f516565b60008085600160a060020a0316600160a060020a031681526020019081526020016000208190555082600160a060020a031633600160a060020a03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef8460405190815260200160405180910390a350600192915050565b6000828211156101ef57fe5b50900390565b60008282018381101561020457fe5b93925050505600a165627a7a7230582052802772002d60968839f12e0b905a2b3142271f958da1c18fe8ffb91dd6c7350029'')"

definition insts_ex where
"insts_ex == [Stack (PUSH_N [0x60]), Stack (PUSH_N [0x40]), Memory MSTORE, Stack (PUSH_N [4]), Info CALLDATASIZE,
  Arith inst_LT, Stack (PUSH_N [0, 0x56]), Pc JUMPI, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]),
  Stack (PUSH_N [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
  Stack (PUSH_N [0]), Stack CALLDATALOAD, Arith DIV, Bits inst_AND, Stack (PUSH_N [0x18, 0x16, 0xD, 0xDD]),
  Dup 1, Arith inst_EQ, Stack (PUSH_N [0, 0x5B]), Pc JUMPI, Dup 0, Stack (PUSH_N [0x70, 0xA0, 0x82, 0x31]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x80]), Pc JUMPI, Dup 0, Stack (PUSH_N [0xA9, 5, 0x9C, 0xBB]),
  Arith inst_EQ, Stack (PUSH_N [0, 0x9F]), Pc JUMPI, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x66]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0,
  Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [0, 0xD5]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0x40]), Memory MLOAD, Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD,
  Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Misc RETURN, Pc JUMPDEST,
  Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0x8B]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Stack (PUSH_N [0, 0x6E]), Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]),
  Arith EXP, Arith SUB, Stack (PUSH_N [4]), Stack CALLDATALOAD, Bits inst_AND, Stack (PUSH_N [0, 0xDB]),
  Pc JUMP, Pc JUMPDEST, Info CALLVALUE, Arith ISZERO, Stack (PUSH_N [0, 0xAA]), Pc JUMPI, Stack (PUSH_N [0]),
  Dup 0, Unknown 0xFD, Pc JUMPDEST, Stack (PUSH_N [0, 0xC1]), Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]),
  Stack (PUSH_N [2]), Arith EXP, Arith SUB, Stack (PUSH_N [4]), Stack CALLDATALOAD, Bits inst_AND,
  Stack (PUSH_N [0x24]), Stack CALLDATALOAD, Stack (PUSH_N [0, 0xF6]), Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [0x40]), Memory MLOAD, Swap 0, Arith ISZERO, Arith ISZERO, Dup 1, Memory MSTORE,
  Stack (PUSH_N [0x20]), Arith ADD, Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0,
  Misc RETURN, Pc JUMPDEST, Stack (PUSH_N [1]), Storage SLOAD, Swap 0, Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND,
  Stack (PUSH_N [0]), Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Dup 1, Swap 0, Memory MSTORE,
  Stack (PUSH_N [0x40]), Swap 0, Arith SHA3, Storage SLOAD, Swap 0, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]),
  Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Dup 3, Bits inst_AND,
  Arith ISZERO, Arith ISZERO, Stack (PUSH_N [1, 0xD]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD,
  Pc JUMPDEST, Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB,
  Info CALLER, Bits inst_AND, Stack (PUSH_N [0]), Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Dup 1,
  Swap 0, Memory MSTORE, Stack (PUSH_N [0x40]), Swap 0, Arith SHA3, Storage SLOAD, Stack (PUSH_N [1, 0x36]),
  Swap 0, Dup 3, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Stack (PUSH_N [1, 0xE3]), Bits inst_AND, Pc JUMP,
  Pc JUMPDEST, Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB,
  Info CALLER, Dup 1, Bits inst_AND, Stack (PUSH_N [0]), Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]),
  Dup 1, Swap 0, Memory MSTORE, Stack (PUSH_N [0x40]), Dup 0, Dup 2, Arith SHA3, Swap 3, Swap 0, Swap 3,
  Storage SSTORE, Swap 0, Dup 5, Bits inst_AND, Dup 1, Memory MSTORE, Arith SHA3, Storage SLOAD,
  Stack (PUSH_N [1, 0x6B]), Swap 0, Dup 3, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Stack (PUSH_N [1, 0xF5]),
  Bits inst_AND, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Dup 5, Stack (PUSH_N [1]),
  Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Stack (PUSH_N [1]),
  Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Dup 1, Memory MSTORE,
  Stack (PUSH_N [0x20]), Arith ADD, Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD,
  Stack (PUSH_N [0]), Arith SHA3, Dup 1, Swap 0, Storage SSTORE, Stack POP, Dup 2, Stack (PUSH_N [1]),
  Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Info CALLER,
  Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND,
  Stack (PUSH_N
          [0xDD, 0xF2, 0x52, 0xAD, 0x1B, 0xE2, 0xC8, 0x9B, 0x69, 0xC2, 0xB0, 0x68, 0xFC, 0x37, 0x8D, 0xAA,
           0x95, 0x2B, 0xA7, 0xF1, 0x63, 0xC4, 0xA1, 0x16, 0x28, 0xF5, 0x5A, 0x4D, 0xF5, 0x23, 0xB3, 0xEF]),
  Dup 4, Stack (PUSH_N [0x40]), Memory MLOAD, Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD,
  Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Log LOG3, Stack POP,
  Stack (PUSH_N [1]), Swap 2, Swap 1, Stack POP, Stack POP, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 2,
  Dup 2, Arith inst_GT, Arith ISZERO, Stack (PUSH_N [1, 0xEF]), Pc JUMPI, Unknown 0xFE, Pc JUMPDEST,
  Stack POP, Swap 0, Arith SUB, Swap 0, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 2, Dup 2, Arith ADD,
  Dup 3, Dup 1, Arith inst_LT, Arith ISZERO, Stack (PUSH_N [2, 4]), Pc JUMPI, Unknown 0xFE, Pc JUMPDEST,
  Swap 3, Swap 2, Stack POP, Stack POP, Stack POP, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Memory MSTORE, Dup 0, Unknown 0x27,
  Stack (PUSH_N
          [0, 0x2D, 0x60, 0x96, 0x88, 0x39, 0xF1, 0x2E, 0xB, 0x90, 0x5A, 0x2B, 0x31, 0x42, 0x27, 0x1F, 0x95,
           0x8D, 0xA1]),
  Unknown 0xC1, Dup 0xF, Unknown 0xE8, Misc SUICIDE, Unknown 0xB9, Unknown 0x1D, Unknown 0xD6, Unknown 0xC7,
  Stack CALLDATALOAD, Misc STOP, Unknown 0x29]"
value "length insts_ex"
(* 348 instructions *)

lemma
 "parse_bytecode ''6060604052600436106100565763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166318160ddd811461005b57806370a0823114610080578063a9059cbb1461009f575b600080fd5b341561006657600080fd5b61006e6100d5565b60405190815260200160405180910390f35b341561008b57600080fd5b61006e600160a060020a03600435166100db565b34156100aa57600080fd5b6100c1600160a060020a03600435166024356100f6565b604051901515815260200160405180910390f35b60015490565b600160a060020a031660009081526020819052604090205490565b6000600160a060020a038316151561010d57600080fd5b600160a060020a033316600090815260208190526040902054610136908363ffffffff6101e316565b600160a060020a03338116600090815260208190526040808220939093559085168152205461016b908363ffffffff6101f516565b60008085600160a060020a0316600160a060020a031681526020019081526020016000208190555082600160a060020a031633600160a060020a03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef8460405190815260200160405180910390a350600192915050565b6000828211156101ef57fe5b50900390565b60008282018381101561020457fe5b93925050505600a165627a7a7230582052802772002d60968839f12e0b905a2b3142271f958da1c18fe8ffb91dd6c7350029'' = insts_ex"
  unfolding insts_ex_def
  by eval

definition "blocks_basictoken == build_blocks insts_ex"
value "blocks_basictoken"
lemma blocks_basictoken_simp:
 "blocks_basictoken = [(0, [(0, Stack (PUSH_N [0x60])), (2, Stack (PUSH_N [0x40])), (4, Memory MSTORE), (5, Stack (PUSH_N [4])),
       (7, Info CALLDATASIZE), (8, Arith inst_LT), (9, Stack (PUSH_N [0, 0x56]))],
   Jumpi),
  (13, [(13, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])),
        (18, Stack (PUSH_N
                     [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                      0])),
        (48, Stack (PUSH_N [0])), (50, Stack CALLDATALOAD), (51, Arith DIV), (52, Bits inst_AND),
        (53, Stack (PUSH_N [0x18, 0x16, 0xD, 0xDD])), (58, Dup 1), (59, Arith inst_EQ),
        (60, Stack (PUSH_N [0, 0x5B]))],
   Jumpi),
  (64, [(64, Dup 0), (65, Stack (PUSH_N [0x70, 0xA0, 0x82, 0x31])), (70, Arith inst_EQ),
        (71, Stack (PUSH_N [0, 0x80]))],
   Jumpi),
  (75, [(75, Dup 0), (76, Stack (PUSH_N [0xA9, 5, 0x9C, 0xBB])), (81, Arith inst_EQ),
        (82, Stack (PUSH_N [0, 0x9F]))],
   Jumpi),
  (86, [(86, Pc JUMPDEST), (87, Stack (PUSH_N [0])), (89, Dup 0), (90, Unknown 0xFD)], Terminal),
  (91, [(91, Pc JUMPDEST), (92, Info CALLVALUE), (93, Arith ISZERO), (94, Stack (PUSH_N [0, 0x66]))], Jumpi),
  (98, [(98, Stack (PUSH_N [0])), (100, Dup 0), (101, Unknown 0xFD)], Terminal),
  (102, [(102, Pc JUMPDEST), (103, Stack (PUSH_N [0, 0x6E])), (106, Stack (PUSH_N [0, 0xD5]))], Jump),
  (110, [(110, Pc JUMPDEST), (111, Stack (PUSH_N [0x40])), (113, Memory MLOAD), (114, Swap 0), (115, Dup 1),
         (116, Memory MSTORE), (117, Stack (PUSH_N [0x20])), (119, Arith ADD), (120, Stack (PUSH_N [0x40])),
         (122, Memory MLOAD), (123, Dup 0), (124, Swap 1), (125, Arith SUB), (126, Swap 0),
         (127, Misc RETURN)],
   Terminal),
  (128, [(128, Pc JUMPDEST), (129, Info CALLVALUE), (130, Arith ISZERO), (131, Stack (PUSH_N [0, 0x8B]))],
   Jumpi),
  (135, [(135, Stack (PUSH_N [0])), (137, Dup 0), (138, Unknown 0xFD)], Terminal),
  (139, [(139, Pc JUMPDEST), (140, Stack (PUSH_N [0, 0x6E])), (143, Stack (PUSH_N [1])),
         (145, Stack (PUSH_N [0xA0])), (147, Stack (PUSH_N [2])), (149, Arith EXP), (150, Arith SUB),
         (151, Stack (PUSH_N [4])), (153, Stack CALLDATALOAD), (154, Bits inst_AND),
         (155, Stack (PUSH_N [0, 0xDB]))],
   Jump),
  (159, [(159, Pc JUMPDEST), (160, Info CALLVALUE), (161, Arith ISZERO), (162, Stack (PUSH_N [0, 0xAA]))],
   Jumpi),
  (166, [(166, Stack (PUSH_N [0])), (168, Dup 0), (169, Unknown 0xFD)], Terminal),
  (170, [(170, Pc JUMPDEST), (171, Stack (PUSH_N [0, 0xC1])), (174, Stack (PUSH_N [1])),
         (176, Stack (PUSH_N [0xA0])), (178, Stack (PUSH_N [2])), (180, Arith EXP), (181, Arith SUB),
         (182, Stack (PUSH_N [4])), (184, Stack CALLDATALOAD), (185, Bits inst_AND),
         (186, Stack (PUSH_N [0x24])), (188, Stack CALLDATALOAD), (189, Stack (PUSH_N [0, 0xF6]))],
   Jump),
  (193, [(193, Pc JUMPDEST), (194, Stack (PUSH_N [0x40])), (196, Memory MLOAD), (197, Swap 0),
         (198, Arith ISZERO), (199, Arith ISZERO), (200, Dup 1), (201, Memory MSTORE),
         (202, Stack (PUSH_N [0x20])), (204, Arith ADD), (205, Stack (PUSH_N [0x40])), (207, Memory MLOAD),
         (208, Dup 0), (209, Swap 1), (210, Arith SUB), (211, Swap 0), (212, Misc RETURN)],
   Terminal),
  (213, [(213, Pc JUMPDEST), (214, Stack (PUSH_N [1])), (216, Storage SLOAD), (217, Swap 0)], Jump),
  (219, [(219, Pc JUMPDEST), (220, Stack (PUSH_N [1])), (222, Stack (PUSH_N [0xA0])),
         (224, Stack (PUSH_N [2])), (226, Arith EXP), (227, Arith SUB), (228, Bits inst_AND),
         (229, Stack (PUSH_N [0])), (231, Swap 0), (232, Dup 1), (233, Memory MSTORE),
         (234, Stack (PUSH_N [0x20])), (236, Dup 1), (237, Swap 0), (238, Memory MSTORE),
         (239, Stack (PUSH_N [0x40])), (241, Swap 0), (242, Arith SHA3), (243, Storage SLOAD),
         (244, Swap 0)],
   Jump),
  (246, [(246, Pc JUMPDEST), (247, Stack (PUSH_N [0])), (249, Stack (PUSH_N [1])),
         (251, Stack (PUSH_N [0xA0])), (253, Stack (PUSH_N [2])), (255, Arith EXP), (256, Arith SUB),
         (257, Dup 3), (258, Bits inst_AND), (259, Arith ISZERO), (260, Arith ISZERO),
         (261, Stack (PUSH_N [1, 0xD]))],
   Jumpi),
  (265, [(265, Stack (PUSH_N [0])), (267, Dup 0), (268, Unknown 0xFD)], Terminal),
  (269, [(269, Pc JUMPDEST), (270, Stack (PUSH_N [1])), (272, Stack (PUSH_N [0xA0])),
         (274, Stack (PUSH_N [2])), (276, Arith EXP), (277, Arith SUB), (278, Info CALLER),
         (279, Bits inst_AND), (280, Stack (PUSH_N [0])), (282, Swap 0), (283, Dup 1), (284, Memory MSTORE),
         (285, Stack (PUSH_N [0x20])), (287, Dup 1), (288, Swap 0), (289, Memory MSTORE),
         (290, Stack (PUSH_N [0x40])), (292, Swap 0), (293, Arith SHA3), (294, Storage SLOAD),
         (295, Stack (PUSH_N [1, 0x36])), (298, Swap 0), (299, Dup 3),
         (300, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (305, Stack (PUSH_N [1, 0xE3])),
         (308, Bits inst_AND)],
   Jump),
  (310, [(310, Pc JUMPDEST), (311, Stack (PUSH_N [1])), (313, Stack (PUSH_N [0xA0])),
         (315, Stack (PUSH_N [2])), (317, Arith EXP), (318, Arith SUB), (319, Info CALLER), (320, Dup 1),
         (321, Bits inst_AND), (322, Stack (PUSH_N [0])), (324, Swap 0), (325, Dup 1), (326, Memory MSTORE),
         (327, Stack (PUSH_N [0x20])), (329, Dup 1), (330, Swap 0), (331, Memory MSTORE),
         (332, Stack (PUSH_N [0x40])), (334, Dup 0), (335, Dup 2), (336, Arith SHA3), (337, Swap 3),
         (338, Swap 0), (339, Swap 3), (340, Storage SSTORE), (341, Swap 0), (342, Dup 5),
         (343, Bits inst_AND), (344, Dup 1), (345, Memory MSTORE), (346, Arith SHA3), (347, Storage SLOAD),
         (348, Stack (PUSH_N [1, 0x6B])), (351, Swap 0), (352, Dup 3),
         (353, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (358, Stack (PUSH_N [1, 0xF5])),
         (361, Bits inst_AND)],
   Jump),
  (363, [(363, Pc JUMPDEST), (364, Stack (PUSH_N [0])), (366, Dup 0), (367, Dup 5),
         (368, Stack (PUSH_N [1])), (370, Stack (PUSH_N [0xA0])), (372, Stack (PUSH_N [2])),
         (374, Arith EXP), (375, Arith SUB), (376, Bits inst_AND), (377, Stack (PUSH_N [1])),
         (379, Stack (PUSH_N [0xA0])), (381, Stack (PUSH_N [2])), (383, Arith EXP), (384, Arith SUB),
         (385, Bits inst_AND), (386, Dup 1), (387, Memory MSTORE), (388, Stack (PUSH_N [0x20])),
         (390, Arith ADD), (391, Swap 0), (392, Dup 1), (393, Memory MSTORE), (394, Stack (PUSH_N [0x20])),
         (396, Arith ADD), (397, Stack (PUSH_N [0])), (399, Arith SHA3), (400, Dup 1), (401, Swap 0),
         (402, Storage SSTORE), (403, Stack POP), (404, Dup 2), (405, Stack (PUSH_N [1])),
         (407, Stack (PUSH_N [0xA0])), (409, Stack (PUSH_N [2])), (411, Arith EXP), (412, Arith SUB),
         (413, Bits inst_AND), (414, Info CALLER), (415, Stack (PUSH_N [1])), (417, Stack (PUSH_N [0xA0])),
         (419, Stack (PUSH_N [2])), (421, Arith EXP), (422, Arith SUB), (423, Bits inst_AND),
         (424, Stack (PUSH_N
                       [0xDD, 0xF2, 0x52, 0xAD, 0x1B, 0xE2, 0xC8, 0x9B, 0x69, 0xC2, 0xB0, 0x68, 0xFC, 0x37,
                        0x8D, 0xAA, 0x95, 0x2B, 0xA7, 0xF1, 0x63, 0xC4, 0xA1, 0x16, 0x28, 0xF5, 0x5A, 0x4D,
                        0xF5, 0x23, 0xB3, 0xEF])),
         (457, Dup 4), (458, Stack (PUSH_N [0x40])), (460, Memory MLOAD), (461, Swap 0), (462, Dup 1),
         (463, Memory MSTORE), (464, Stack (PUSH_N [0x20])), (466, Arith ADD), (467, Stack (PUSH_N [0x40])),
         (469, Memory MLOAD), (470, Dup 0), (471, Swap 1), (472, Arith SUB), (473, Swap 0), (474, Log LOG3),
         (475, Stack POP), (476, Stack (PUSH_N [1])), (478, Swap 2), (479, Swap 1), (480, Stack POP),
         (481, Stack POP)],
   Jump),
  (483, [(483, Pc JUMPDEST), (484, Stack (PUSH_N [0])), (486, Dup 2), (487, Dup 2), (488, Arith inst_GT),
         (489, Arith ISZERO), (490, Stack (PUSH_N [1, 0xEF]))],
   Jumpi),
  (494, [(494, Unknown 0xFE)], Terminal),
  (495, [(495, Pc JUMPDEST), (496, Stack POP), (497, Swap 0), (498, Arith SUB), (499, Swap 0)], Jump),
  (501, [(501, Pc JUMPDEST), (502, Stack (PUSH_N [0])), (504, Dup 2), (505, Dup 2), (506, Arith ADD),
         (507, Dup 3), (508, Dup 1), (509, Arith inst_LT), (510, Arith ISZERO),
         (511, Stack (PUSH_N [2, 4]))],
   Jumpi),
  (515, [(515, Unknown 0xFE)], Terminal),
  (516, [(516, Pc JUMPDEST), (517, Swap 3), (518, Swap 2), (519, Stack POP), (520, Stack POP),
         (521, Stack POP)],
   Jump),
  (523, [(523, Misc STOP)], Terminal),
  (524, [(524, Log LOG1), (525, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (532, Arith SHA3),
         (533, Memory MSTORE), (534, Dup 0), (535, Unknown 0x27)],
   Terminal),
  (536, [(536, Stack (PUSH_N
                       [0, 0x2D, 0x60, 0x96, 0x88, 0x39, 0xF1, 0x2E, 0xB, 0x90, 0x5A, 0x2B, 0x31, 0x42, 0x27,
                        0x1F, 0x95, 0x8D, 0xA1])),
         (556, Unknown 0xC1)],
   Terminal),
  (557, [(557, Dup 0xF), (558, Unknown 0xE8)], Terminal), (559, [(559, Misc SUICIDE)], Terminal),
  (560, [(560, Unknown 0xB9)], Terminal), (561, [(561, Unknown 0x1D)], Terminal),
  (562, [(562, Unknown 0xD6)], Terminal), (563, [(563, Unknown 0xC7)], Terminal),
  (564, [(564, Stack CALLDATALOAD), (565, Misc STOP)], Terminal), (566, [(566, Unknown 0x29)], Terminal)]"
  by eval

definition balanceOf_hash :: "32 word"  where
 "balanceOf_hash = 0x70a08231"

definition totalSupply_hash :: "32 word"  where
 "totalSupply_hash = 0x18160ddd"

definition transfer_hash :: "32 word"  where
 "transfer_hash = 0xa9059cbb"

context
notes
  words_simps[simp add]
  calldataload_simps[simp add]
  M_def[simp add]
  Cmem_def[simp add]
  memory_range.simps[simp del]
 if_split[ split del ] sep_fun_simps[simp del]
gas_value_simps[simp add] gas_simps[simp] pure_emp_simps[simp add]
evm_fun_simps[simp add] sep_lc[simp del] sep_conj_first[simp add]
pure_false_simps[simp add] iszero_stack_def[simp add]
word256FromNat_def[simp add]
begin
abbreviation "blk_num \<equiv> block_number_pred"

lemma address_mask:
 "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = mask 160"
  by (simp add: mask_def)

lemma address_mask_ucast:
 "ucast (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF && (ucast (w::address))::w256) = w"
  apply (simp add: ucast_ucast_mask address_mask ucast_mask_drop word_bool_alg.conj.commute)
  apply (simp add: mask_def)
  done

lemma ucast_and_w256_drop:
 "((ucast (w::address))::w256) && 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = ucast w"
  by word_bitwise

definition
  bytestr_to_w256 :: "byte list \<Rightarrow> w256"  where
 "bytestr_to_w256 \<equiv> word_rcat"

lemma hash_diff:
  "ucast (hash::32 word) = (0xa9059cbb::w256) \<Longrightarrow> hash = 0xa9059cbb "
  "ucast (hash::32 word) = (0x70a08231::w256) \<Longrightarrow> hash = 0x70a08231 "
  "ucast (hash::32 word) = (0x18160ddd::w256) \<Longrightarrow> hash = 0x18160ddd "
  by word_bitwise+

lemma ucast_160_upto_256_eq:
  " ((ucast (x::160 word))::w256) = ucast y \<Longrightarrow> x = y"
  by (drule ucast_up_inj; simp)

method sep_imp_solve2 uses simp =
   solves \<open>rule conjI; rule refl\<close>
 | solves \<open>match conclusion in "block_lookup _ _ = Some _"  \<Rightarrow> \<open>simp add:word_rcat_simps\<close>
             , (rule conjI, (rule refl)+)\<close>
 | solves \<open>simp\<close>
 | solves \<open>(clarsimp?, order_sep_conj, ((((sep_cancel, clarsimp?)+)|simp add:simp|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp?, order_sep_conj, ((((sep_cancel, clarsimp?)+)|(clarsimp split:if_split simp: simp)|rule conjI)+)[1])\<close>
 | solves \<open>(clarsimp split:if_splits simp:word_rcat_simps) ; sep_imp_solve2 \<close>

method split_conds =
 (split if_split_asm; clarsimp simp add: word_rcat_simps)?

method block_vcg2 uses simp=
  split_conds,
  ((blocks_rule_vcg; (rule refl)?), triple_seq_vcg),
  (sep_imp_solve2 simp:simp)+,
  (solves \<open>split_conds\<close>)?

definition w256 :: "'a::len0 word \<Rightarrow> w256"  where
 "w256 v \<equiv> ucast v"

definition bytestr :: "'a::len0 word \<Rightarrow> byte list"  where
 "bytestr \<equiv> word_rsplit"

definition
 balances_mapping :: "address \<Rightarrow> w256"
 where
 "balances_mapping addr \<equiv>  keccak (bytestr (w256 addr) @ bytestr (0::w256))"

definition requires_cond
  where
 "requires_cond to val balance_frm balance_to \<equiv>
  to \<noteq> 0 \<and>  val \<le> balance_frm"

lemma len_bytestr_simps: 
 "\<And>x. length (bytestr (x::32 word)) = 4"
 "\<And>x. length (bytestr (x::64 word)) = 8"
 "\<And>x. length (bytestr (x::256 word)) = 32"
  by(simp add: bytestr_def length_word_rsplit_exp_size' word_size)+

lemma two_power_of_224:
 "(0x100000000000000000000000000000000000000000000000000000000::nat) = 2^224"
  by simp


(* *** word_rcat shifts more generally *** *)
lemma concat_map_take :
"\<forall>x \<in> set xs. length (f x) = n \<Longrightarrow>
List.concat (map f (take k xs)) = take (k*n) (List.concat (map f xs))"
  apply(induct xs arbitrary: k, simp)
  apply(case_tac k, simp)
  apply clarsimp
  done


lemma word_rcat_shiftr_take : 
"length ys = 32 \<Longrightarrow> k \<le> 32 \<Longrightarrow>
 word_rcat (ys::byte list) >> 8 * k = (word_rcat (take (length ys - k) ys) ::w256)"
  apply (simp add: word_rcat_bl shiftr_bl)
  apply (simp add: word_rep_drop size_rcat_lem)
  apply(subst concat_map_take[where n=8])
   apply clarsimp
  apply(subst diff_mult_distrib)
  apply simp
  apply(subst Groups.ab_semigroup_mult_class.mult.commute)
  by(rule refl)

lemma word_rcat_append_shiftr :
  "length ys + length xs = 32 \<Longrightarrow>
   word_rcat ((ys::byte list) @ xs) >> (8 * length xs) = (word_rcat ys :: w256)"
  by(subst word_rcat_shiftr_take, simp_all)
(* ************************************************ *)  

lemma take_32_of_w256:
  fixes w1::byte and w2 :: byte and w3 :: byte and w4 :: byte and xs :: "bool list"
  shows
 "length xs = 224 \<Longrightarrow> 
  take 32 (to_bl (of_bl (to_bl w1 @ to_bl w2 @ to_bl w3 @ to_bl w4 @ xs) :: 256 word)) =
   take 32 (to_bl w1 @ to_bl w2 @ to_bl w3 @ to_bl w4)"
  by (simp add: word_rep_drop)

lemma word_rcat_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat ([a::byte, b, d, e] @ xs)::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat [a, b, d, e]"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply(subgoal_tac "unat (word_rcat (a # b # d # e # xs) >> 224) = 
                     unat (word_rcat ([a, b, d, e] @ xs) >> 8 * length xs)")
   apply(erule ssubst, subst word_rcat_append_shiftr)
    apply simp
   apply(rule refl)
  by simp

lemma word_rcat_word_rsplit_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat (word_rsplit (w::32 word) @ (xs::byte list))::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat (word_rsplit w :: byte list)"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply(subgoal_tac "unat (word_rcat (word_rsplit w @ xs) >> 224) = 
                     unat (word_rcat (word_rsplit w @ xs) >> 8 * length xs)")
   apply(erule ssubst, subst word_rcat_append_shiftr)
    apply(simp add: length_word_rsplit_4)
   apply(rule refl)
  by simp

(* ? ? ? ?
lemma take_to_bl_of_bl_word_list:
  fixes w::"'b::len0 word"
    and w'::"'a::len0 word"
    and xs :: "bool list"
  shows
 "length xs = LENGTH('b) - LENGTH('a) \<Longrightarrow>
  w = of_bl (to_bl w' @ xs) \<Longrightarrow>
  LENGTH('b) > LENGTH('a) \<Longrightarrow>
  take LENGTH('a) (to_bl w) =
   take LENGTH('a) (to_bl w')"
  by (simp add: word_rep_drop)

lemma take_32_concat_to_bl_word_rsplit:
  fixes w :: "32 word"
  and xs :: "byte list"
  shows
  "length xs = 28 \<Longrightarrow>
    take 32 (to_bl (of_bl (List.concat (map to_bl (word_rsplit w :: byte list)) @ List.concat (map to_bl xs)):: w256)) =
    List.concat (map to_bl (word_rsplit w :: byte list))"
  by (simp add:word_rev_tf takefill_alt size_rcat_lem length_word_rsplit_4)

lemma word_rcat_word_rsplit_div_rep0:
  "length xs = 28 \<Longrightarrow>
  (word_rcat (word_rsplit (w::32 word) @ (xs::byte list))::w256) div (0x100000000000000000000000000000000000000000000000000000000::w256) =
   word_rcat (word_rsplit w :: byte list)"
  apply (subst word_unat.Rep_inject [symmetric])
  apply (subst unat_div)
  apply (simp add: )
  apply (subst two_power_of_224)
  apply (subst shiftr_div_2n'[symmetric])
  apply (simp add: word_rcat_bl shiftr_bl)
  apply (rule arg_cong[where f=of_bl])
  apply (simp add: take_32_concat_to_bl_word_rsplit)
  done
*)


lemma w256_mask_32:
  "(0xFFFFFFFF::w256) = mask 32"
  by (simp add: mask_def)

lemma unat_ucast:
  assumes "LENGTH('a) \<le> LENGTH('b)"
  shows "unat (UCAST ('a::len0\<rightarrow>'b::len) x) = unat x"
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (rule lt2p_lem)
  apply (rule assms)
   apply simp
  done

lemma ucast_le_ucast:
  "LENGTH('a) \<le> LENGTH('b) \<Longrightarrow> (UCAST('a::len0\<rightarrow>'b::len) x \<le> (ucast y)) = (x \<le> y)"
  by (simp add: word_le_nat_alt unat_ucast)

lemma minus_1_w32:
  " (-1::32 word) = 0xffffffff"
  by simp

lemma ucast_32_256_minus_1_eq:
  "UCAST(32 \<rightarrow> 256) (- 1) = 0xFFFFFFFF"
  apply (simp add: ucast_def unat_arith_simps unat_def)
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply (clarsimp split: uint_splits)
  apply (simp add: minus_1_w32)
  done

lemma ucast_frm_32_le_mask_32:
 "UCAST(32\<rightarrow>256) z \<le> mask 32"
  apply (subgoal_tac "mask 32 = UCAST(32\<rightarrow>256) (mask 32)")
   apply (simp add: ucast_le_ucast mask_32_max_word)
  apply (simp add: mask_def)
  apply (simp add: ucast_32_256_minus_1_eq)
  done

lemma dispatcher_hash_extract:
 "length xs = 28 \<Longrightarrow>
  0xFFFFFFFF && word_of_int (uint (word_rcat (bytestr (z::32 word) @ xs) :: w256) div
      0x100000000000000000000000000000000000000000000000000000000) =
    (word_rcat (bytestr z)::w256)"
  apply (simp add: bytestr_def)
  apply(rule subst[where P="\<lambda>x. _ AND word_of_int x = _"])
  apply (rule uint_div[where x="word_rcat (word_rsplit z @ xs)"
        and y="0x100000000000000000000000000000000000000000000000000000000::w256", simplified])
  apply (subst word_rcat_word_rsplit_div_rep0; simp)
  apply (simp add: w256_mask_32)
  apply (subst word_bw_comms(1))
  apply (simp add: and_mask_eq_iff_le_mask)
  apply (simp add: word_rcat_rsplit_ucast)
  apply (simp add: ucast_frm_32_le_mask_32)
  done

lemma word_rsplit_byte_split:
"(word_rsplit (w1::w256) :: byte list) =
       a # aa # ab # ac # ad # ae # af # ag # ah # ai # aj #
 ak # al # am # an # ao # ap # aq # ar # as # a't # au # av #
 aw # ax # ay # az # ba # bb # bc # bd # be # lisue  \<Longrightarrow> lisue = []"
  using length_word_rsplit_32[where x=w1]
  by simp

lemma memory_range_0_w256_append:
  "(memory_range 0 (word_rsplit (w1::w256)) \<and>* memory_range 0x20  (word_rsplit (w2::w256))) =
     memory_range 0 (word_rsplit w1 @ word_rsplit w2)"
  apply (rule ext)
  apply (case_tac "(word_rsplit w1 :: byte list)")
   apply (simp add: length_0_conv[symmetric])
  apply (rename_tac list , case_tac list, solves \<open>simp add: list_eq_iff_zip_eq[where xs="word_rsplit _"]\<close>)+
  apply (simp add:)
  apply (drule word_rsplit_byte_split)
  apply simp
  apply (thin_tac " _ = _ ")+
  apply (rename_tac list)
  apply (simp add: memory_range.simps)  
  done

lemma two_memory_memory_range_eq:
 "(R' \<and>* memory 0x20 w2 \<and>* R  \<and>* memory 0 w1  \<and>* R'') = (memory_range 0 (word_rsplit w1 @ word_rsplit w2) \<and>* R' \<and>* R  \<and>* R'')"
  by (simp add: memory_def, simp add: ac_simps, sep_simp simp: memory_range_0_w256_append)

lemma  stack_topmost_unfold_sep:
  "(stack_topmost h [a, b, c, d, e] ** R)
  = (stack_height (Suc (Suc (Suc (Suc (Suc h))))) ** stack h a ** stack (Suc h) b  ** stack (Suc (Suc h)) c** stack (Suc (Suc (Suc h))) d  
  ** stack (Suc (Suc (Suc (Suc h)))) e ** R)"
  apply (unfold stack_topmost_def)
  apply clarsimp
  apply (rule ext)
  apply (rule iffI)
  apply (clarsimp simp add: sep_basic_simps stack_def stack_height_def )
  apply (rule_tac x="insert (StackElm (Suc (Suc (Suc (Suc h))), e))
                 (insert (StackElm (Suc (Suc (Suc h)), d))
                   (insert (StackElm (Suc (Suc h), c))
                     (insert (StackElm (Suc h, b)) (insert (StackElm (h, a)) y))))" in exI)
  apply clarsimp
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d),
                      StackElm (Suc (Suc h), c), StackElm (Suc h, b)} \<union> y" in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d),
                      StackElm (Suc (Suc h), c)} \<union> y" in exI)
   apply clarsimp
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e), StackElm (Suc (Suc (Suc h)), d) } \<union> y" in exI)
   apply clarsimp
  
   apply (rule conjI)
    apply blast
  apply (rule_tac x="{StackElm (Suc (Suc (Suc (Suc h))), e) } \<union> y" in exI)
 
   apply clarsimp
   apply blast  
  apply (clarsimp simp add: sep_basic_simps stack_def stack_height_def )
  apply (drule_tac x=ye in spec)
  apply blast
  done

lemma sep_stack_topmost_unfold_sep:
  "(R' ** stack_topmost h [a, b, c, d, e] ** R)
  = (R' ** stack_height (Suc (Suc (Suc (Suc (Suc h))))) ** stack h a ** stack (Suc h) b  ** stack (Suc (Suc h)) c** stack (Suc (Suc (Suc h))) d  
  ** stack (Suc (Suc (Suc (Suc h)))) e ** R)"
  by (sep_simp simp: stack_topmost_unfold_sep)

lemma memory_range_last:
 "unat (len::w256) = length data \<Longrightarrow> 
  (a \<and>* memory_range st data \<and>* b) = (a \<and>* b \<and>*  memory_range st data)"
 by (sep_simp simp: memory_range_sep)+

method fast_sep_imp_solve uses simp = 
  (match conclusion  in "triple_blocks _ _ _ _ _"  \<Rightarrow> \<open>succeed\<close> | 
    ( sep_imp_solve2 simp:simp, fast_sep_imp_solve simp: simp) )

method triple_blocks_vcg =
  (clarsimp simp only: sep_conj_ac(2)[symmetric])?,
  ((rule blocks_jumpi_uint_ex blocks_jump_uint_ex blocks_no_ex blocks_next_ex); 
   (clarsimp simp only: sep_conj_ac(2))?),
  triple_seq_vcg

theorem verify_basictoken_return:
notes
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
assumes blk_num: "bn > 2463000"
and net: "at_least_eip150 net"
shows
"\<exists>r. triple net
  (\<langle>balances_mapping anyaddr \<noteq> balances_mapping sender \<and>
    balances_mapping anyaddr \<noteq> balances_mapping to \<and> at_least_eip150 net \<rangle> **
   program_counter 0 ** stack_height 0 **
   sent_data (bytestr transfer_hash @ bytestr (w256 to) @ bytestr val) **
   sent_value 0 ** caller sender ** blk_num bn **
   memory_usage 0 ** continuing ** gas_pred 100000 **
   storage (balances_mapping sender) balance_frm **
   storage (balances_mapping to) balance_to **
   storage (balances_mapping anyaddr) balance_any **
   account_existence sender sender_ex  **
   account_existence to to_ex **
   memory (0::w256) m0x0 **
   memory (0x20::w256) m0x20 **
   memory (0x40::w256) (bytestr_to_w256 [x]) **
   memory (0x60::w256) (bytestr_to_w256 [y]) **
   log_number log_num **
   this_account this)
  blocks_basictoken
  ((let c = requires_cond to val balance_frm balance_to in
   storage (balances_mapping sender) (if c then balance_frm - val else balance_frm) **
   storage (balances_mapping to) (if c \<and> balance_to + val \<ge> balance_to then balance_to + val else balance_to) ** 
   storage (balances_mapping anyaddr) balance_any **
   (if c \<and> balance_to + val \<ge> balance_to then logged log_num \<lparr>log_addr = this,
                              log_topics = [0xDDF252AD1BE2C89B69C2B068FC378DAA952BA7F163C4A11628F55A4DF523B3EF,
                                   UCAST(160 \<rightarrow> 256) sender, UCAST(160 \<rightarrow> 256) to],
                              log_data = word_rsplit val\<rparr> **
               log_number (Suc log_num)
    else emp)) ** r)"
  apply (insert blk_num[simplified word_less_nat_alt] net)
  apply (simp add: Let_def)
  apply (simp add:blocks_basictoken_simp)
  apply(simp add: blocks_simps triple_def )
  apply (triple_blocks_vcg)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
   apply split_conds
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply clarsimp
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
  apply (simp add: word_rcat_simps bytestr_def)
  apply clarsimp
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
   apply (simp add: word_rcat_simps bytestr_def)
  apply clarsimp
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
   apply (simp add: word_rcat_simps bytestr_def)
  prefer 2
   apply split_conds
        apply (subst (asm) dispatcher_hash_extract)
         apply (simp)
   apply (simp add: word_rcat_simps bytestr_def)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (sep_imp_solve2)
  apply (triple_blocks_vcg)

    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
     apply (sep_imp_solve2)
  apply (split_conds)
  apply (split_conds)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
                  apply (sep_imp_solve2)
  apply ( subst (asm) two_memory_memory_range_eq)
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
   apply (sep_imp_solve2 simp: balances_mapping_def bytestr_def w256_def word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
     apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
  apply (rule refl)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (rule refl)
  apply split_conds
  apply split_conds
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)

  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
                      apply (sep_imp_solve2)
  apply ( subst (asm) two_memory_memory_range_eq[symmetric])
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply ( subst (asm) two_memory_memory_range_eq)
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply ( subst (asm) two_memory_memory_range_eq[symmetric])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_select_asm 3)
    apply (sep_select_asm 11)
    apply (subst (asm) two_memory_memory_range_eq[where R'=emp and R=emp, simplified ])
                 apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
                 apply (sep_imp_solve2 simp:  word_rcat_rsplit)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
        apply (sep_imp_solve2)
  apply split_conds
  apply split_conds
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply ( subst (asm) two_memory_memory_range_eq[symmetric])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply ( subst (asm) two_memory_memory_range_eq)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply ( subst (asm) two_memory_memory_range_eq[symmetric])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply ( subst (asm) two_memory_memory_range_eq)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
                  apply (sep_imp_solve2)
                 apply (simp add: sep_stack_topmost_unfold_sep )
                 apply (sep_select 10)
  apply (clarsimp simp only: memory_def)
                 apply (rule conjI)
    apply (sep_imp_solve2 )
    apply (sep_imp_solve2 simp: log_gas_def)
    apply (unfold stack_topmost_def, simp only: stack_topmost_elms.simps )[1]
    apply (unfold stack_height_def)[1]
    apply (sep_imp_solve2 simp: log_gas_def)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply (subgoal_tac "[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0x60::byte] = word_rsplit (0x60::w256)")
        apply (simp only:)
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
   apply ( subst (asm) two_memory_memory_range_eq[symmetric])
  apply (simp (no_asm) only: memory_def)
  apply(erule_tac P="\<lambda>x. (\<langle> _ \<le> 1023 \<and>
            Gverylow - Cmem _ + Cmem (M _ _ 0x20) \<le> _ \<and>
            0 \<le> _ \<and> length (word_rsplit _) = unat 0x20 \<rangle> \<and>*
          stack _ _ \<and>*
          stack_height (_ + 1) \<and>*
          program_counter _ \<and>*
          memory_usage _ \<and>*
          memory_range _ x \<and>* gas_pred _ \<and>* continuing \<and>* _)
          s" in subst)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (simp  only: memory_def diff_Suc_1 unat_1)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (simp  only: memory_def diff_Suc_1 unat_1)
    apply (erule_tac P="\<lambda>x. (_ \<and>*_ \<and>* _ \<and>*_ \<and>*_ \<and>* memory_range _ x \<and>* _) s" in subst)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (simp  only: memory_def diff_Suc_1 unat_1)
         apply (sep_imp_solve2)
  apply(case_tac "balance_to \<le> balance_to + val", clarsimp)
  apply (case_tac "requires_cond to val balance_frm balance_to" ; clarsimp)
   apply (clarsimp simp: balances_mapping_def bytestr_def w256_def word_rcat_simps add.commute[where b=val])
   apply (sep_imp_solve2)
  apply (thin_tac "(_ \<and>* _) _")
  apply (erule notE[where P="requires_cond _ _ _ _"])
  apply (clarsimp simp: requires_cond_def word_rcat_rsplit w256_def)
         apply ((rule conjI)+; unat_arith)
        apply(unat_arith)
  apply (simp add: word_rsplit_def bin_rsplit_def)
  apply split_conds
  apply split_conds
  apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
  apply (case_tac "requires_cond to val balance_frm balance_to" ; clarsimp)
       apply (clarsimp simp: word_rcat_rsplit w256_def word_rcat_simps requires_cond_def balances_mapping_def bytestr_def)
       apply(case_tac "balance_to \<le> balance_to + val", unat_arith)
       apply simp
       apply (sep_imp_solve2)
 apply (erule notE[where P="requires_cond _ _ _ _"])
  apply (clarsimp simp: requires_cond_def word_rcat_rsplit w256_def)
  apply (rule conjI, unat_arith)
apply simp
apply split_conds
apply split_conds
  apply (case_tac "requires_cond to val balance_frm balance_to" ; clarsimp)
   apply (clarsimp simp: requires_cond_def word_rcat_rsplit)
   apply unat_arith
  apply (clarsimp simp: word_rcat_rsplit )
 apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
       apply (clarsimp simp: word_rcat_rsplit w256_def word_rcat_simps requires_cond_def balances_mapping_def bytestr_def)
    apply (sep_imp_solve2)
apply split_conds
apply split_conds
 apply (clarsimp simp: word_rcat_rsplit w256_def word_rcat_simps requires_cond_def balances_mapping_def bytestr_def)
  apply (case_tac "requires_cond to val balance_frm balance_to" )
   apply (clarsimp simp: requires_cond_def word_rcat_rsplit)
   apply (clarsimp simp: requires_cond_def word_rcat_rsplit)
 apply (triple_blocks_vcg)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
       apply (clarsimp simp: word_rcat_rsplit w256_def word_rcat_simps requires_cond_def balances_mapping_def bytestr_def)
    apply (sep_imp_solve2)
apply simp
done

end

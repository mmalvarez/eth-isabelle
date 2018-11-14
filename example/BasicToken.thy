theory BasicToken

imports
  Dispatcher
  "HOL-Eisbach.Eisbach"

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
    require(_value <= balances[msg.sender]);

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
 /usr/bin/solc --optimize --overwrite -o basic --bin-runtime --asm --hashes
  --allow-paths /home/samani/dev/ethereum/seed/zeppelin-solidity/contracts/math/ BasicToken.sol

70a08231: balanceOf(address)
18160ddd: totalSupply()
a9059cbb: transfer(address,uint256)

*)
value"(parse_bytecode ''6060604052600436106100565763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166318160ddd811461005b57806370a0823114610080578063a9059cbb1461009f575b600080fd5b341561006657600080fd5b61006e6100d5565b60405190815260200160405180910390f35b341561008b57600080fd5b61006e600160a060020a03600435166100db565b34156100aa57600080fd5b6100c1600160a060020a03600435166024356100f6565b604051901515815260200160405180910390f35b60015490565b600160a060020a031660009081526020819052604090205490565b6000600160a060020a038316151561010d57600080fd5b600160a060020a03331660009081526020819052604090205482111561013257600080fd5b600160a060020a03331660009081526020819052604090205461015b908363ffffffff61020816565b600160a060020a033381166000908152602081905260408082209390935590851681522054610190908363ffffffff61021a16565b60008085600160a060020a0316600160a060020a031681526020019081526020016000208190555082600160a060020a031633600160a060020a03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef8460405190815260200160405180910390a350600192915050565b60008282111561021457fe5b50900390565b60008282018381101561022957fe5b93925050505600a165627a7a723058205d06b4dc1682b339c944c79aa2261422213d898c8f9bd1f82ffc19214b9784280029'')"

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
  Swap 0, Memory MSTORE, Stack (PUSH_N [0x40]), Swap 0, Arith SHA3, Storage SLOAD, Dup 2, Arith inst_GT,
  Arith ISZERO, Stack (PUSH_N [1, 0x32]), Pc JUMPI, Stack (PUSH_N [0]), Dup 0, Unknown 0xFD, Pc JUMPDEST,
  Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Info CALLER,
  Bits inst_AND, Stack (PUSH_N [0]), Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Dup 1, Swap 0,
  Memory MSTORE, Stack (PUSH_N [0x40]), Swap 0, Arith SHA3, Storage SLOAD, Stack (PUSH_N [1, 0x5B]), Swap 0,
  Dup 3, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Stack (PUSH_N [2, 8]), Bits inst_AND, Pc JUMP, Pc JUMPDEST,
  Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Info CALLER, Dup 1,
  Bits inst_AND, Stack (PUSH_N [0]), Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Dup 1, Swap 0,
  Memory MSTORE, Stack (PUSH_N [0x40]), Dup 0, Dup 2, Arith SHA3, Swap 3, Swap 0, Swap 3, Storage SSTORE,
  Swap 0, Dup 5, Bits inst_AND, Dup 1, Memory MSTORE, Arith SHA3, Storage SLOAD, Stack (PUSH_N [1, 0x90]),
  Swap 0, Dup 3, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF]), Stack (PUSH_N [2, 0x1A]), Bits inst_AND, Pc JUMP,
  Pc JUMPDEST, Stack (PUSH_N [0]), Dup 0, Dup 5, Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]),
  Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]),
  Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]),
  Arith ADD, Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD, Stack (PUSH_N [0]), Arith SHA3,
  Dup 1, Swap 0, Storage SSTORE, Stack POP, Dup 2, Stack (PUSH_N [1]), Stack (PUSH_N [0xA0]),
  Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND, Info CALLER, Stack (PUSH_N [1]),
  Stack (PUSH_N [0xA0]), Stack (PUSH_N [2]), Arith EXP, Arith SUB, Bits inst_AND,
  Stack (PUSH_N
          [0xDD, 0xF2, 0x52, 0xAD, 0x1B, 0xE2, 0xC8, 0x9B, 0x69, 0xC2, 0xB0, 0x68, 0xFC, 0x37, 0x8D, 0xAA,
           0x95, 0x2B, 0xA7, 0xF1, 0x63, 0xC4, 0xA1, 0x16, 0x28, 0xF5, 0x5A, 0x4D, 0xF5, 0x23, 0xB3, 0xEF]),
  Dup 4, Stack (PUSH_N [0x40]), Memory MLOAD, Swap 0, Dup 1, Memory MSTORE, Stack (PUSH_N [0x20]), Arith ADD,
  Stack (PUSH_N [0x40]), Memory MLOAD, Dup 0, Swap 1, Arith SUB, Swap 0, Log LOG3, Stack POP,
  Stack (PUSH_N [1]), Swap 2, Swap 1, Stack POP, Stack POP, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 2,
  Dup 2, Arith inst_GT, Arith ISZERO, Stack (PUSH_N [2, 0x14]), Pc JUMPI, Unknown 0xFE, Pc JUMPDEST,
  Stack POP, Swap 0, Arith SUB, Swap 0, Pc JUMP, Pc JUMPDEST, Stack (PUSH_N [0]), Dup 2, Dup 2, Arith ADD,
  Dup 3, Dup 1, Arith inst_LT, Arith ISZERO, Stack (PUSH_N [2, 0x29]), Pc JUMPI, Unknown 0xFE, Pc JUMPDEST,
  Swap 3, Swap 2, Stack POP, Stack POP, Stack POP, Pc JUMP, Misc STOP, Log LOG1,
  Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58]), Arith SHA3, Unknown 0x5D, Arith MOD, Unknown 0xB4,
  Unknown 0xDC, Bits inst_AND, Dup 2, Unknown 0xB3, Memory CODECOPY, Unknown 0xC9, Info DIFFICULTY,
  Unknown 0xC7, Swap 0xA, Log LOG2, Unknown 0x26, Arith inst_EQ, Unknown 0x22, Unknown 0x21, Unknown 0x3D,
  Dup 9, Dup 0xC, Dup 0xF, Swap 0xB, Unknown 0xD1, Unknown 0xF8, Unknown 0x2F, Unknown 0xFC, Bits inst_NOT,
  Unknown 0x21, Unknown 0x4B, Swap 7, Dup 4, Unknown 0x28, Misc STOP, Unknown 0x29]"
value "length insts_ex"
(* 395 instructions *)

lemma
 "parse_bytecode ''6060604052600436106100565763ffffffff7c010000000000000000000000000000000000000000000000000000000060003504166318160ddd811461005b57806370a0823114610080578063a9059cbb1461009f575b600080fd5b341561006657600080fd5b61006e6100d5565b60405190815260200160405180910390f35b341561008b57600080fd5b61006e600160a060020a03600435166100db565b34156100aa57600080fd5b6100c1600160a060020a03600435166024356100f6565b604051901515815260200160405180910390f35b60015490565b600160a060020a031660009081526020819052604090205490565b6000600160a060020a038316151561010d57600080fd5b600160a060020a03331660009081526020819052604090205482111561013257600080fd5b600160a060020a03331660009081526020819052604090205461015b908363ffffffff61020816565b600160a060020a033381166000908152602081905260408082209390935590851681522054610190908363ffffffff61021a16565b60008085600160a060020a0316600160a060020a031681526020019081526020016000208190555082600160a060020a031633600160a060020a03167fddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef8460405190815260200160405180910390a350600192915050565b60008282111561021457fe5b50900390565b60008282018381101561022957fe5b93925050505600a165627a7a723058205d06b4dc1682b339c944c79aa2261422213d898c8f9bd1f82ffc19214b9784280029'' = insts_ex"
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
         (290, Stack (PUSH_N [0x40])), (292, Swap 0), (293, Arith SHA3), (294, Storage SLOAD), (295, Dup 2),
         (296, Arith inst_GT), (297, Arith ISZERO), (298, Stack (PUSH_N [1, 0x32]))],
   Jumpi),
  (302, [(302, Stack (PUSH_N [0])), (304, Dup 0), (305, Unknown 0xFD)], Terminal),
  (306, [(306, Pc JUMPDEST), (307, Stack (PUSH_N [1])), (309, Stack (PUSH_N [0xA0])),
         (311, Stack (PUSH_N [2])), (313, Arith EXP), (314, Arith SUB), (315, Info CALLER),
         (316, Bits inst_AND), (317, Stack (PUSH_N [0])), (319, Swap 0), (320, Dup 1), (321, Memory MSTORE),
         (322, Stack (PUSH_N [0x20])), (324, Dup 1), (325, Swap 0), (326, Memory MSTORE),
         (327, Stack (PUSH_N [0x40])), (329, Swap 0), (330, Arith SHA3), (331, Storage SLOAD),
         (332, Stack (PUSH_N [1, 0x5B])), (335, Swap 0), (336, Dup 3),
         (337, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (342, Stack (PUSH_N [2, 8])), (345, Bits inst_AND)],
   Jump),
  (347, [(347, Pc JUMPDEST), (348, Stack (PUSH_N [1])), (350, Stack (PUSH_N [0xA0])),
         (352, Stack (PUSH_N [2])), (354, Arith EXP), (355, Arith SUB), (356, Info CALLER), (357, Dup 1),
         (358, Bits inst_AND), (359, Stack (PUSH_N [0])), (361, Swap 0), (362, Dup 1), (363, Memory MSTORE),
         (364, Stack (PUSH_N [0x20])), (366, Dup 1), (367, Swap 0), (368, Memory MSTORE),
         (369, Stack (PUSH_N [0x40])), (371, Dup 0), (372, Dup 2), (373, Arith SHA3), (374, Swap 3),
         (375, Swap 0), (376, Swap 3), (377, Storage SSTORE), (378, Swap 0), (379, Dup 5),
         (380, Bits inst_AND), (381, Dup 1), (382, Memory MSTORE), (383, Arith SHA3), (384, Storage SLOAD),
         (385, Stack (PUSH_N [1, 0x90])), (388, Swap 0), (389, Dup 3),
         (390, Stack (PUSH_N [0xFF, 0xFF, 0xFF, 0xFF])), (395, Stack (PUSH_N [2, 0x1A])),
         (398, Bits inst_AND)],
   Jump),
  (400, [(400, Pc JUMPDEST), (401, Stack (PUSH_N [0])), (403, Dup 0), (404, Dup 5),
         (405, Stack (PUSH_N [1])), (407, Stack (PUSH_N [0xA0])), (409, Stack (PUSH_N [2])),
         (411, Arith EXP), (412, Arith SUB), (413, Bits inst_AND), (414, Stack (PUSH_N [1])),
         (416, Stack (PUSH_N [0xA0])), (418, Stack (PUSH_N [2])), (420, Arith EXP), (421, Arith SUB),
         (422, Bits inst_AND), (423, Dup 1), (424, Memory MSTORE), (425, Stack (PUSH_N [0x20])),
         (427, Arith ADD), (428, Swap 0), (429, Dup 1), (430, Memory MSTORE), (431, Stack (PUSH_N [0x20])),
         (433, Arith ADD), (434, Stack (PUSH_N [0])), (436, Arith SHA3), (437, Dup 1), (438, Swap 0),
         (439, Storage SSTORE), (440, Stack POP), (441, Dup 2), (442, Stack (PUSH_N [1])),
         (444, Stack (PUSH_N [0xA0])), (446, Stack (PUSH_N [2])), (448, Arith EXP), (449, Arith SUB),
         (450, Bits inst_AND), (451, Info CALLER), (452, Stack (PUSH_N [1])), (454, Stack (PUSH_N [0xA0])),
         (456, Stack (PUSH_N [2])), (458, Arith EXP), (459, Arith SUB), (460, Bits inst_AND),
         (461, Stack (PUSH_N
                       [0xDD, 0xF2, 0x52, 0xAD, 0x1B, 0xE2, 0xC8, 0x9B, 0x69, 0xC2, 0xB0, 0x68, 0xFC, 0x37,
                        0x8D, 0xAA, 0x95, 0x2B, 0xA7, 0xF1, 0x63, 0xC4, 0xA1, 0x16, 0x28, 0xF5, 0x5A, 0x4D,
                        0xF5, 0x23, 0xB3, 0xEF])),
         (494, Dup 4), (495, Stack (PUSH_N [0x40])), (497, Memory MLOAD), (498, Swap 0), (499, Dup 1),
         (500, Memory MSTORE), (501, Stack (PUSH_N [0x20])), (503, Arith ADD), (504, Stack (PUSH_N [0x40])),
         (506, Memory MLOAD), (507, Dup 0), (508, Swap 1), (509, Arith SUB), (510, Swap 0), (511, Log LOG3),
         (512, Stack POP), (513, Stack (PUSH_N [1])), (515, Swap 2), (516, Swap 1), (517, Stack POP),
         (518, Stack POP)],
   Jump),
  (520, [(520, Pc JUMPDEST), (521, Stack (PUSH_N [0])), (523, Dup 2), (524, Dup 2), (525, Arith inst_GT),
         (526, Arith ISZERO), (527, Stack (PUSH_N [2, 0x14]))],
   Jumpi),
  (531, [(531, Unknown 0xFE)], Terminal),
  (532, [(532, Pc JUMPDEST), (533, Stack POP), (534, Swap 0), (535, Arith SUB), (536, Swap 0)], Jump),
  (538, [(538, Pc JUMPDEST), (539, Stack (PUSH_N [0])), (541, Dup 2), (542, Dup 2), (543, Arith ADD),
         (544, Dup 3), (545, Dup 1), (546, Arith inst_LT), (547, Arith ISZERO),
         (548, Stack (PUSH_N [2, 0x29]))],
   Jumpi),
  (552, [(552, Unknown 0xFE)], Terminal),
  (553, [(553, Pc JUMPDEST), (554, Swap 3), (555, Swap 2), (556, Stack POP), (557, Stack POP),
         (558, Stack POP)],
   Jump),
  (560, [(560, Misc STOP)], Terminal),
  (561, [(561, Log LOG1), (562, Stack (PUSH_N [0x62, 0x7A, 0x7A, 0x72, 0x30, 0x58])), (569, Arith SHA3),
         (570, Unknown 0x5D)],
   Terminal),
  (571, [(571, Arith MOD), (572, Unknown 0xB4)], Terminal), (573, [(573, Unknown 0xDC)], Terminal),
  (574, [(574, Bits inst_AND), (575, Dup 2), (576, Unknown 0xB3)], Terminal),
  (577, [(577, Memory CODECOPY), (578, Unknown 0xC9)], Terminal),
  (579, [(579, Info DIFFICULTY), (580, Unknown 0xC7)], Terminal),
  (581, [(581, Swap 0xA), (582, Log LOG2), (583, Unknown 0x26)], Terminal),
  (584, [(584, Arith inst_EQ), (585, Unknown 0x22)], Terminal), (586, [(586, Unknown 0x21)], Terminal),
  (587, [(587, Unknown 0x3D)], Terminal),
  (588, [(588, Dup 9), (589, Dup 0xC), (590, Dup 0xF), (591, Swap 0xB), (592, Unknown 0xD1)], Terminal),
  (593, [(593, Unknown 0xF8)], Terminal), (594, [(594, Unknown 0x2F)], Terminal),
  (595, [(595, Unknown 0xFC)], Terminal), (596, [(596, Bits inst_NOT), (597, Unknown 0x21)], Terminal),
  (598, [(598, Unknown 0x4B)], Terminal),
  (599, [(599, Swap 7), (600, Dup 4), (601, Unknown 0x28)], Terminal), (602, [(602, Misc STOP)], Terminal),
  (603, [(603, Unknown 0x29)], Terminal)]"
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

type_synonym erc20_balances = "address \<rightharpoonup> w256"

definition balance_upd :: "address \<Rightarrow> (w256 \<Rightarrow> w256) \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
  where
 "balance_upd addr upd m \<equiv> m(addr \<mapsto> upd (the (m addr)))"

definition
 transfer :: "address \<Rightarrow> address \<Rightarrow> w256 \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
 where
 "transfer from to amount m \<equiv> balance_upd to (\<lambda>v. v + amount) (balance_upd from (\<lambda>v. v - amount) m)"

definition
 zero :: "address \<Rightarrow> erc20_balances \<Rightarrow> erc20_balances"
 where
 "zero addr m \<equiv> m(addr \<mapsto> 0)"

definition
 balances_mapping :: "address \<Rightarrow> w256"
 where
 "balances_mapping addr \<equiv>  keccak (bytestr (w256 addr) @ bytestr (0::w256))"

definition
 balances_to_storage :: "erc20_balances \<Rightarrow> state_element set \<Rightarrow> bool"
 where
 "balances_to_storage m s \<equiv> s = (\<lambda>addr. StorageElm (balances_mapping addr, the (m addr))) ` dom m"

definition
 addrs_hash_consistency :: "address set \<Rightarrow> bool"
 where
 "addrs_hash_consistency s \<equiv>
   \<forall>a1\<in>s.\<forall>a2 \<in> s. a1 \<noteq> a2 \<longrightarrow> balances_mapping a1 \<noteq> balances_mapping a2"

lemma balances_to_storage_sep':
 "addrs_hash_consistency (dom m)
 \<Longrightarrow> m addr = Some v
 \<Longrightarrow>  balances_to_storage m = (storage (balances_mapping addr) v ** balances_to_storage (m(addr:=None)))"
  apply (rule ext)
  apply (rule iffI)
   apply (clarsimp simp add: sep_basic_simps balances_to_storage_def storage_def)
   apply (fastforce simp: balances_mapping_def addrs_hash_consistency_def image_def)
  apply (clarsimp simp: balances_to_storage_def sep_basic_simps  split:if_splits)
  apply (simp add: image_def storage_def)
  apply (rule equalityI)
   apply fastforce
  apply fastforce
  done

lemma balances_to_storage_sep:
 "addrs_hash_consistency (insert addr (dom m))
 \<Longrightarrow> balances_to_storage (m(addr\<mapsto>v)) = (storage (balances_mapping addr) v ** balances_to_storage (m(addr:=None)))"
  by (subst  balances_to_storage_sep'[where addr=addr and v=v]; simp)

lemma balances_to_storage_singleton:
 "a1 \<noteq> a2
 \<Longrightarrow> balances_to_storage ([a1 \<mapsto> v](a2 := None)) = (storage (balances_mapping a1) v)"
  apply (rule ext)
  apply ( simp add: balances_to_storage_def storage_def image_def)
  done

lemma transfer_sep:
 "addrs_hash_consistency {a2,a1}
  \<Longrightarrow> a1 \<noteq> a2
  \<Longrightarrow> (balances_to_storage (transfer a1 a2 v1 ([a1\<mapsto>v1, a2\<mapsto>v2])) ** R) = (storage (balances_mapping a2) (v2 + v1) \<and>* storage (balances_mapping a1) 0 \<and>* R)"
  apply (simp add: transfer_def balance_upd_def)
  apply (sep_simp simp: balances_to_storage_sep)
  apply simp
  apply (sep_simp simp: balances_to_storage_sep)
  apply (simp add: sep_conj_assoc sep_conj_commute)
  apply (sep_simp simp: balances_to_storage_singleton)
  apply (simp)+
  done

definition requires_cond
  where
 "requires_cond to val balance_frm balance_to \<equiv>
  to \<noteq> 0 \<and>  val \<le> balance_frm"


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
"\<exists>r. bbtriple net
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
  apply(simp add: blocks_simps bbtriple_def )
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
  apply ( subst (asm) two_memory_memory_range_eq[symmetric])
   apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
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
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp split:)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply clarsimp
    apply (rule conjI)
  apply (sep_cancel)
  apply (clarsimp split: if_splits)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (clarsimp )
                      apply (rule conjI)
                      apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
                      apply (clarsimp simp: word_rcat_simps)
                      apply (clarsimp split: if_splits)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2 simp: word_rcat_simps)
    apply (sep_imp_solve2 simp: word_rcat_simps)

    apply ( subst (asm) two_memory_memory_range_eq[symmetric])
    apply (sep_imp_solve2 simp: word_rcat_simps)
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
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp simp del: log256floor.simps split:if_split)?)+)|simp add:|rule conjI)+)[1])
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2 simp: log256floor.simps word_rcat_simps)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
    apply (sep_imp_solve2)
  apply  (clarsimp?, order_sep_conj, ((((sep_cancel, (clarsimp simp del: log256floor.simps split:if_split)?)+)|simp add:|rule conjI)+)[1])
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
    apply (sep_imp_solve2)
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

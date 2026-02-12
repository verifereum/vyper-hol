(*
 * Algebraic Optimization (Venom IR) - Shared Definitions
 *)

Theory algebraicOptDefs
Ancestors
  list string words finite_map alist integer arithmetic
  venomState venomInst

(* ==========================================================================
   Operand Helpers
   ========================================================================== *)

Definition is_lit_def:
  is_lit op =
    case op of
      Lit _ => T
    | _ => F
End

Definition is_label_def:
  is_label op =
    case op of
      Label _ => T
    | _ => F
End

Definition lit_eq_def:
  lit_eq op w =
    case op of
      Lit v => (v = w)
    | _ => F
End

Definition lit_is_zero_def:
  lit_is_zero op =
    case op of
      Lit w => (w2n w = 0)
    | _ => F
End

Definition lit_is_one_def:
  lit_is_one op =
    case op of
      Lit w => (w2n w = 1)
    | _ => F
End

Definition lit_is_ones_def:
  lit_is_ones op = lit_eq op (~(0w:bytes32))
End

(* ==========================================================================
   Analysis Hints (per-instruction)
   ========================================================================== *)

Datatype:
  opt_hint = <|
    prefer_iszero: bool;
    is_truthy: bool;
    cmp_flip: bool
  |>
End

Datatype:
  cmp_after_action =
    | CMP_AFTER_REPLACE string
    | CMP_AFTER_INSERT string
End

Definition default_hint_def:
  default_hint = <|
    prefer_iszero := F;
    is_truthy := F;
    cmp_flip := F
  |>
End

Definition hint_lookup_def:
  hint_lookup hints id =
    case ALOOKUP hints id of
      SOME h => h
    | NONE => default_hint
End

Definition lit_int_signed_def:
  lit_int_signed op =
    case op of
      Lit w => SOME (w2i w)
    | _ => NONE
End

Definition lit_int_unsigned_def:
  lit_int_unsigned op =
    case op of
      Lit w => SOME (((& (w2n w)) : int))
    | _ => NONE
End

Definition signed_min_for_bytes_def:
  signed_min_for_bytes n =
    - ((& (2 EXP (8 * (n + 1) - 1))) : int)
End

Definition signed_max_for_bytes_def:
  signed_max_for_bytes n =
    ((& (2 EXP (8 * (n + 1) - 1))) : int) - 1
End

(* ==========================================================================
   Instruction Builders
   ========================================================================== *)

Definition mk_assign_def:
  mk_assign inst op =
    inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>
End

Definition mk_const_def:
  mk_const inst w = mk_assign inst (Lit w)
End

Definition lit_of_num_def:
  lit_of_num n = Lit ((n2w n):bytes32)
End

Definition inst_single_output_def:
  inst_single_output inst =
    case inst.inst_outputs of
      [v] => SOME v
    | _ => NONE
End

Definition mk_not_def:
  mk_not inst op =
    inst with <| inst_opcode := NOT; inst_operands := [op] |>
End

Definition fresh_var_def:
  fresh_var (id:num) = STRCAT "alg_tmp_" (toString id)
End

Definition max_inst_id_insts_def:
  max_inst_id_insts [] = 0 /\
  max_inst_id_insts (inst::rest) =
    MAX inst.inst_id (max_inst_id_insts rest)
End

Definition temp_id_for_inst_def:
  temp_id_for_inst insts inst =
    SUC (max_inst_id_insts insts) + inst.inst_id
End

(* ==========================================================================
   Constants and Predicates
   ========================================================================== *)

Definition max_uint256_def:
  max_uint256 = (~(0w:bytes32))
End

Definition min_uint256_def:
  min_uint256 = (0w:bytes32)
End

Definition min_int256_def:
  min_int256 = word_lsl (1w:bytes32) 255
End

Definition max_int256_def:
  max_int256 = word_1comp min_int256
End

Definition min_int256_i_def:
  min_int256_i = w2i min_int256
End

Definition max_int256_i_def:
  max_int256_i = w2i max_int256
End

Definition is_commutative_def:
  is_commutative ADD = T /\
  is_commutative MUL = T /\
  is_commutative AND = T /\
  is_commutative OR = T /\
  is_commutative XOR = T /\
  is_commutative EQ = T /\
  is_commutative _ = F
End

Definition is_comparator_def:
  is_comparator GT = T /\
  is_comparator LT = T /\
  is_comparator SGT = T /\
  is_comparator SLT = T /\
  is_comparator _ = F
End

Definition flip_comparator_def:
  flip_comparator GT = LT /\
  flip_comparator LT = GT /\
  flip_comparator SGT = SLT /\
  flip_comparator SLT = SGT /\
  flip_comparator op = op
End

Definition is_pow2_num_def:
  is_pow2_num n = (n <> 0 /\ ((2:num) ** LOG2 n = n))
End

Definition log2_num_def:
  log2_num n = LOG2 n
End

Definition is_pow2_lit_def:
  is_pow2_lit op <=>
    case op of
      Lit w => is_pow2_num (w2n w)
    | _ => F
End

Definition log2_lit_def:
  log2_lit op =
    case op of
      Lit w => log2_num (w2n w)
    | _ => 0
End

Definition is_gt_op_def:
  is_gt_op GT = T /\
  is_gt_op SGT = T /\
  is_gt_op _ = F
End

Definition is_signed_cmp_def:
  is_signed_cmp SGT = T /\
  is_signed_cmp SLT = T /\
  is_signed_cmp _ = F
End

(* ==========================================================================
   Instruction Classification (Vyper parity helpers)
   ========================================================================== *)

Definition is_pseudo_opcode_def:
  is_pseudo_opcode PHI = T /\
  is_pseudo_opcode PARAM = T /\
  is_pseudo_opcode _ = F
End

Definition is_volatile_opcode_def:
  is_volatile_opcode PARAM = T /\
  is_volatile_opcode CALL = T /\
  is_volatile_opcode STATICCALL = T /\
  is_volatile_opcode DELEGATECALL = T /\
  is_volatile_opcode CREATE = T /\
  is_volatile_opcode CREATE2 = T /\
  is_volatile_opcode INVOKE = T /\
  is_volatile_opcode SSTORE = T /\
  is_volatile_opcode ISTORE = T /\
  is_volatile_opcode TSTORE = T /\
  is_volatile_opcode MSTORE = T /\
  is_volatile_opcode CALLDATACOPY = T /\
  is_volatile_opcode MCOPY = T /\
  is_volatile_opcode EXTCODECOPY = T /\
  is_volatile_opcode RETURNDATACOPY = T /\
  is_volatile_opcode CODECOPY = T /\
  is_volatile_opcode DLOADBYTES = T /\
  is_volatile_opcode RETURN = T /\
  is_volatile_opcode RET = T /\
  is_volatile_opcode SINK = T /\
  is_volatile_opcode JMP = T /\
  is_volatile_opcode JNZ = T /\
  is_volatile_opcode DJMP = T /\
  is_volatile_opcode LOG = T /\
  is_volatile_opcode SELFDESTRUCT = T /\
  is_volatile_opcode INVALID = T /\
  is_volatile_opcode REVERT = T /\
  is_volatile_opcode ASSERT = T /\
  is_volatile_opcode ASSERT_UNREACHABLE = T /\
  is_volatile_opcode STOP = T /\
  is_volatile_opcode _ = F
End

Definition inst_is_pseudo_def:
  inst_is_pseudo inst = is_pseudo_opcode inst.inst_opcode
End

Definition inst_is_volatile_def:
  inst_is_volatile inst = is_volatile_opcode inst.inst_opcode
End

Definition inst_num_outputs_def:
  inst_num_outputs inst = LENGTH inst.inst_outputs
End

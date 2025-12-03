(*
 * Venom Instructions
 *
 * This theory defines the instruction set for Venom IR.
 *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory stringTheory optionTheory;
open vfmTypesTheory;
open venomStateTheory;

val _ = new_theory "venomInst";

(* --------------------------------------------------------------------------
   Instruction Opcodes

   Venom opcodes closely mirror EVM but with some additions for
   SSA form (phi, param, assign) and internal function calls (invoke, ret).
   -------------------------------------------------------------------------- *)

Datatype:
  opcode =
    (* Arithmetic *)
    | ADD | SUB | MUL | DIV | SDIV | MOD | SMOD | EXP
    | ADDMOD | MULMOD
    (* Comparison *)
    | EQ | LT | GT | SLT | SGT | ISZERO
    (* Bitwise *)
    | AND | OR | XOR | NOT | SHL | SHR | SAR | SIGNEXTEND
    (* Memory *)
    | MLOAD | MSTORE | MCOPY | MSIZE
    (* Storage *)
    | SLOAD | SSTORE
    (* Transient storage *)
    | TLOAD | TSTORE
    (* Immutables (Vyper-specific) *)
    | ILOAD | ISTORE
    (* Control flow *)
    | JMP | JNZ | DJMP | RET | RETURN | REVERT | STOP | SINK
    (* SSA/IR-specific *)
    | PHI | PARAM | ASSIGN | NOP
    (* Allocation (Vyper-specific stack slots) *)
    | ALLOCA | PALLOCA | CALLOCA
    (* Internal function calls *)
    | INVOKE
    (* Environment *)
    | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY
    | ADDRESS | ORIGIN | GASPRICE | GAS | GASLIMIT
    | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | CHAINID
    | SELFBALANCE | BALANCE | BLOCKHASH | BASEFEE
    | CODESIZE | CODECOPY | EXTCODESIZE | EXTCODEHASH | EXTCODECOPY
    | RETURNDATASIZE | RETURNDATACOPY
    | BLOBHASH | BLOBBASEFEE
    (* Hashing *)
    | SHA3 | SHA3_64
    (* External calls *)
    | CALL | STATICCALL | DELEGATECALL | CREATE | CREATE2
    (* Logging *)
    | LOG
    (* Other *)
    | SELFDESTRUCT | INVALID
    (* Assertions (Vyper-specific) *)
    | ASSERT | ASSERT_UNREACHABLE
    (* Data section access (Vyper-specific) *)
    | DLOAD | DLOADBYTES | OFFSET
End

(* --------------------------------------------------------------------------
   Instructions

   Each instruction has:
   - opcode: the operation to perform
   - operands: list of input operands (rightmost = top of conceptual stack)
   - output: optional output variable name (SSA)
   -------------------------------------------------------------------------- *)

Datatype:
  instruction = <|
    inst_opcode : opcode;
    inst_operands : operand list;
    inst_output : string option
  |>
End

(* Construct an instruction *)
Definition mk_inst_def:
  mk_inst op ops out = <|
    inst_opcode := op;
    inst_operands := ops;
    inst_output := out
  |>
End

(* --------------------------------------------------------------------------
   Basic Block

   A basic block is a sequence of instructions with:
   - A label for control flow
   - Phi nodes at the start (if any)
   - Body instructions
   - A terminator at the end
   -------------------------------------------------------------------------- *)

Datatype:
  basic_block = <|
    bb_label : string;
    bb_instructions : instruction list
  |>
End

(* --------------------------------------------------------------------------
   Function

   An IR function contains:
   - A name (entry label)
   - A list of basic blocks (first is entry)
   -------------------------------------------------------------------------- *)

Datatype:
  ir_function = <|
    fn_name : string;
    fn_blocks : basic_block list
  |>
End

(* --------------------------------------------------------------------------
   Context (whole program)

   Contains multiple functions and optional entry point.
   -------------------------------------------------------------------------- *)

Datatype:
  ir_context = <|
    ctx_functions : ir_function list;
    ctx_entry : string option
  |>
End

(* --------------------------------------------------------------------------
   Instruction Classification
   -------------------------------------------------------------------------- *)

(* Terminators end a basic block *)
Definition is_terminator_def:
  is_terminator JMP = T /\
  is_terminator JNZ = T /\
  is_terminator DJMP = T /\
  is_terminator RET = T /\
  is_terminator RETURN = T /\
  is_terminator REVERT = T /\
  is_terminator STOP = T /\
  is_terminator SINK = T /\
  is_terminator _ = F
End

(* Instructions that produce no output value *)
Definition no_output_def:
  no_output MSTORE = T /\
  no_output SSTORE = T /\
  no_output ISTORE = T /\
  no_output TSTORE = T /\
  no_output DLOADBYTES = T /\
  no_output CALLDATACOPY = T /\
  no_output MCOPY = T /\
  no_output RETURNDATACOPY = T /\
  no_output CODECOPY = T /\
  no_output EXTCODECOPY = T /\
  no_output RETURN = T /\
  no_output RET = T /\
  no_output SINK = T /\
  no_output REVERT = T /\
  no_output STOP = T /\
  no_output INVALID = T /\
  no_output JMP = T /\
  no_output JNZ = T /\
  no_output DJMP = T /\
  no_output LOG = T /\
  no_output NOP = T /\
  no_output ASSERT = T /\
  no_output ASSERT_UNREACHABLE = T /\
  no_output SELFDESTRUCT = T /\
  no_output _ = F
End

(* Commutative operations (operand order doesn't matter) *)
Definition is_commutative_def:
  is_commutative ADD = T /\
  is_commutative MUL = T /\
  is_commutative OR = T /\
  is_commutative XOR = T /\
  is_commutative AND = T /\
  is_commutative EQ = T /\
  is_commutative _ = F
End

(* Comparison operations *)
Definition is_comparator_def:
  is_comparator GT = T /\
  is_comparator LT = T /\
  is_comparator SGT = T /\
  is_comparator SLT = T /\
  is_comparator _ = F
End

(* Pseudo-instructions (not real EVM ops) *)
Definition is_pseudo_def:
  is_pseudo PHI = T /\
  is_pseudo PARAM = T /\
  is_pseudo DLOAD = T /\
  is_pseudo DLOADBYTES = T /\
  is_pseudo _ = F
End

(* Volatile instructions (have side effects, can't be eliminated) *)
Definition is_volatile_def:
  is_volatile PARAM = T /\
  is_volatile CALL = T /\
  is_volatile STATICCALL = T /\
  is_volatile DELEGATECALL = T /\
  is_volatile CREATE = T /\
  is_volatile CREATE2 = T /\
  is_volatile INVOKE = T /\
  is_volatile SSTORE = T /\
  is_volatile ISTORE = T /\
  is_volatile TSTORE = T /\
  is_volatile MSTORE = T /\
  is_volatile CALLDATACOPY = T /\
  is_volatile MCOPY = T /\
  is_volatile EXTCODECOPY = T /\
  is_volatile RETURNDATACOPY = T /\
  is_volatile CODECOPY = T /\
  is_volatile DLOADBYTES = T /\
  is_volatile RETURN = T /\
  is_volatile RET = T /\
  is_volatile SINK = T /\
  is_volatile JMP = T /\
  is_volatile JNZ = T /\
  is_volatile DJMP = T /\
  is_volatile LOG = T /\
  is_volatile SELFDESTRUCT = T /\
  is_volatile INVALID = T /\
  is_volatile REVERT = T /\
  is_volatile ASSERT = T /\
  is_volatile ASSERT_UNREACHABLE = T /\
  is_volatile STOP = T /\
  is_volatile _ = F
End

(* --------------------------------------------------------------------------
   Lookup Functions
   -------------------------------------------------------------------------- *)

(* Find a basic block by label *)
Definition lookup_block_def:
  lookup_block lbl [] = NONE /\
  lookup_block lbl (bb::bbs) =
    if bb.bb_label = lbl then SOME bb
    else lookup_block lbl bbs
End

(* Find a function by name *)
Definition lookup_function_def:
  lookup_function name [] = NONE /\
  lookup_function name (fn::fns) =
    if fn.fn_name = name then SOME fn
    else lookup_function name fns
End

(* Get instruction at index in a block *)
Definition get_instruction_def:
  get_instruction bb idx =
    if idx < LENGTH bb.bb_instructions then
      SOME (EL idx bb.bb_instructions)
    else NONE
End

(* Get the entry block of a function *)
Definition entry_block_def:
  entry_block fn =
    if NULL fn.fn_blocks then NONE
    else SOME (HD fn.fn_blocks)
End

(* Get successor labels of a terminator instruction *)
Definition get_successors_def:
  get_successors inst =
    if ~is_terminator inst.inst_opcode then [] else
    FILTER_MAP get_label inst.inst_operands
End

val _ = export_theory();

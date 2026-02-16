(*
 * Venom Instructions
 *
 * This theory defines the instruction set for Venom IR.
 *)

Theory venomInst
Ancestors
  venomState

(* --------------------------------------------------------------------------
   Instruction Opcodes

   Venom opcodes closely mirror EVM but with some additions for
   SSA form (phi, param, assign) and internal function calls (invoke, ret).
   -------------------------------------------------------------------------- *)

Datatype:
  opcode =
    (* Arithmetic - note: Div/Mod to avoid HOL4 name clash *)
    | ADD | SUB | MUL | Div | SDIV | Mod | SMOD | EXP
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
   - id: unique identifier (models object identity from Python)
   - opcode: the operation to perform
   - operands: list of input operands (rightmost = top of conceptual stack)
   - outputs: list of output variable names (SSA)

   Most instructions have 0 or 1 output. The invoke opcode can have multiple
   outputs for multi-return internal function calls.

   The inst_id is used to distinguish instructions that may have identical
   fields but are different objects. This is important for passes that
   track visited instructions or build instruction maps.
   -------------------------------------------------------------------------- *)

Datatype:
  instruction = <|
    inst_id : num;
    inst_opcode : opcode;
    inst_operands : operand list;
    inst_outputs : string list
  |>
End

(* Construct an instruction with a given ID *)
Definition mk_inst_def:
  mk_inst id op ops outs = <|
    inst_id := id;
    inst_opcode := op;
    inst_operands := ops;
    inst_outputs := outs
  |>
End

(* Helper: get single output (for instructions with exactly one output) *)
Definition inst_output_def:
  inst_output inst =
    case inst.inst_outputs of
      [out] => SOME out
    | _ => NONE
End

(* Helper: check if instruction has outputs *)
Definition has_outputs_def:
  has_outputs inst = ~NULL inst.inst_outputs
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

(* Optional invariant: fn_name labels the first block. *)
Definition fn_wf_entry_def:
  fn_wf_entry fn <=>
    fn.fn_blocks <> [] /\
    lookup_block fn.fn_name fn.fn_blocks = SOME (HD fn.fn_blocks)
End

(* Get successor labels of a terminator instruction *)
Definition get_successors_def:
  get_successors inst =
    if ~is_terminator inst.inst_opcode then [] else
    MAP THE (FILTER IS_SOME (MAP get_label inst.inst_operands))
End

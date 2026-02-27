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
   Operand helpers
   -------------------------------------------------------------------------- *)

(* Extract variable name from an operand, if it is a Var. *)
Definition operand_var_def:
  operand_var (Var v) = SOME v ∧
  operand_var _ = NONE
End

(* All variable names referenced by a list of operands. *)
Definition operand_vars_def:
  operand_vars [] = [] ∧
  operand_vars (op::ops) =
    case operand_var op of
      NONE => operand_vars ops
    | SOME v => v :: operand_vars ops
End

(* Variables used (read) by an instruction. *)
Definition inst_uses_def:
  inst_uses inst = operand_vars inst.inst_operands
End

(* Variables defined (written) by an instruction. *)
Definition inst_defs_def:
  inst_defs inst = inst.inst_outputs
End

(* Extract (label, var) pairs from PHI operands.
   PHI format: Label l1, Var v1, Label l2, Var v2, ... *)
Definition phi_pairs_def:
  phi_pairs [] = [] ∧
  phi_pairs [_] = [] ∧
  phi_pairs (Label l :: Var v :: rest) = (l, v) :: phi_pairs rest ∧
  phi_pairs (_ :: _ :: rest) = phi_pairs rest
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

(* The function has an entry block (fn_blocks is non-empty). *)
Definition fn_has_entry_def:
  fn_has_entry fn <=> fn.fn_blocks <> []
End

(* A basic block is well-formed: non-empty and ends with a terminator. *)
Definition bb_well_formed_def:
  bb_well_formed bb <=>
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode
End

(* Get successor labels of a terminator instruction *)
Definition get_successors_def:
  get_successors inst =
    if ~is_terminator inst.inst_opcode then [] else
    MAP THE (FILTER IS_SOME (MAP get_label inst.inst_operands))
End

(* The block labels of a function, in block order. *)
Definition fn_labels_def:
  fn_labels fn = MAP (λbb. bb.bb_label) fn.fn_blocks
End

(* Successor labels of a basic block: the labels targeted by its terminator,
 * reversed to match Vyper's iteration order (see cfg_analysis_parity.md §2). *)
Definition bb_succs_def:
  bb_succs bb =
    case bb.bb_instructions of
      [] => []
    | insts => REVERSE (get_successors (LAST insts))
End

(* All successor labels of every block exist as block labels in the function. *)
Definition fn_succs_closed_def:
  fn_succs_closed fn <=>
    !bb succ.
      MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
      MEM succ (fn_labels fn)
End

(* Structural well-formedness for IR functions:
 * unique labels, has entry, blocks well-formed, successor labels exist. *)
Definition wf_function_def:
  wf_function fn <=>
    ALL_DISTINCT (fn_labels fn) /\
    fn_has_entry fn /\
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed fn
End

(* All instructions across all blocks, in block order. *)
Definition fn_insts_blocks_def:
  fn_insts_blocks [] = [] /\
  fn_insts_blocks (bb::bbs) =
    bb.bb_instructions ++ fn_insts_blocks bbs
End

Definition fn_insts_def:
  fn_insts fn = fn_insts_blocks fn.fn_blocks
End

(* lookup_function succeeds => the name appears in the function list. *)
Theorem lookup_function_mem:
  lookup_function name fns = SOME func ==>
  MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >> rw[] >> gvs[] >>
  Cases_on `h.fn_name = name` >> gvs[]
QED

(* lookup_function fails => the name is not in the function list. *)
Theorem lookup_function_not_mem:
  lookup_function name fns = NONE ==>
  ~MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> simp[lookup_function_def] >>
  rpt strip_tac >>
  Cases_on `h.fn_name = name` >> gvs[]
QED

(* ==========================================================================
   Context well-formedness
   ========================================================================== *)

(* The function names in a context. *)
Definition ctx_fn_names_def:
  ctx_fn_names ctx = MAP (\f. f.fn_name) ctx.ctx_functions
End

(* Function names in the context are distinct. *)
Definition ctx_distinct_fn_names_def:
  ctx_distinct_fn_names ctx <=> ALL_DISTINCT (ctx_fn_names ctx)
End

(* The context has an entry function that names a real function. *)
Definition ctx_has_entry_def:
  ctx_has_entry ctx <=>
    ?entry_name. ctx.ctx_entry = SOME entry_name /\
       MEM entry_name (ctx_fn_names ctx)
End

(* Well-formed context. *)
Definition ctx_wf_def:
  ctx_wf ctx <=> ctx_distinct_fn_names ctx /\ ctx_has_entry ctx
End

(* Every INVOKE instruction's first operand is a Label naming a
 * function in the context.
 * TODO: candidate for inclusion in ctx_wf once we have a
 * ctx_wf => fn_wf => bb_wf => inst_wf hierarchy. *)
Definition wf_invoke_targets_def:
  wf_invoke_targets ctx <=>
    (!func inst.
       MEM func ctx.ctx_functions /\
       MEM inst (fn_insts func) /\
       inst.inst_opcode = INVOKE ==>
       ?lbl rest. inst.inst_operands = Label lbl :: rest /\
                  MEM lbl (ctx_fn_names ctx))
End

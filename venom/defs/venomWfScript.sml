(*
 * Venom Well-Formedness Predicates
 *
 * This theory defines structural well-formedness for Venom IR functions
 * and contexts: entry blocks, block structure, successor closure, and
 * context-level invariants.
 *)

Theory venomWf
Ancestors
  venomInst

(* ==========================================================================
   Per-instruction well-formedness (inst_wf)

   Captures the structural shape (operand count/type, output count) that
   step_inst_base requires for each opcode.  Eliminates ~60 Error branches
   due to wrong operand counts, missing outputs, or wrong operand types.

   Runtime errors (undefined operand, phi predecessor mismatch, param OOB,
   non-terminating ext_call) are NOT eliminated — those require state info.
   ========================================================================== *)

Definition inst_wf_def:
  inst_wf inst ⇔
    case inst.inst_opcode of
    (* ---- exec_pure2: 2 operands, 1 output ---- *)
    | ADD => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SUB => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | MUL => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Div => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Mod => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SDIV => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SMOD => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | Exp => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | EQ => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | LT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | GT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SLT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SGT => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | AND => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | OR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | XOR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SHL => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SHR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SAR => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | SIGNEXTEND => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | BYTE => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    | GEP => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_pure1: 1 operand, 1 output ---- *)
    | ISZERO => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | NOT => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_pure3: 3 operands, 1 output ---- *)
    | ADDMOD => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    | MULMOD => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_read0: 0 operands, 1 output ---- *)
    | CALLER => LENGTH inst.inst_outputs = 1
    | ADDRESS => LENGTH inst.inst_outputs = 1
    | CALLVALUE => LENGTH inst.inst_outputs = 1
    | GAS => LENGTH inst.inst_outputs = 1
    | ORIGIN => LENGTH inst.inst_outputs = 1
    | GASPRICE => LENGTH inst.inst_outputs = 1
    | CHAINID => LENGTH inst.inst_outputs = 1
    | COINBASE => LENGTH inst.inst_outputs = 1
    | TIMESTAMP => LENGTH inst.inst_outputs = 1
    | NUMBER => LENGTH inst.inst_outputs = 1
    | PREVRANDAO => LENGTH inst.inst_outputs = 1
    | GASLIMIT => LENGTH inst.inst_outputs = 1
    | BASEFEE => LENGTH inst.inst_outputs = 1
    | BLOBBASEFEE => LENGTH inst.inst_outputs = 1
    | CALLDATASIZE => LENGTH inst.inst_outputs = 1
    | RETURNDATASIZE => LENGTH inst.inst_outputs = 1
    | MSIZE => LENGTH inst.inst_outputs = 1
    | CODESIZE => LENGTH inst.inst_outputs = 1
    | SELFBALANCE => LENGTH inst.inst_outputs = 1
    (* ---- exec_read1: 1 operand, 1 output ---- *)
    | MLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | SLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | TLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | ILOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | DLOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BLOCKHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BLOBHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | BALANCE => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | CALLDATALOAD => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | EXTCODESIZE => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | EXTCODEHASH => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    (* ---- exec_write2: 2 operands ---- *)
    | MSTORE => LENGTH inst.inst_operands = 2
    | SSTORE => LENGTH inst.inst_operands = 2
    | TSTORE => LENGTH inst.inst_operands = 2
    | ISTORE => LENGTH inst.inst_operands = 2
    (* ---- 3 operands, no output constraint ---- *)
    | MCOPY => LENGTH inst.inst_operands = 3
    | CALLDATACOPY => LENGTH inst.inst_operands = 3
    | RETURNDATACOPY => LENGTH inst.inst_operands = 3
    | DLOADBYTES => LENGTH inst.inst_operands = 3
    | CODECOPY => LENGTH inst.inst_operands = 3
    (* ---- 4 operands ---- *)
    | EXTCODECOPY => LENGTH inst.inst_operands = 4
    (* ---- SHA3: 2 operands, 1 output ---- *)
    | SHA3 => LENGTH inst.inst_operands = 2 ∧ LENGTH inst.inst_outputs = 1
    (* ---- Control flow ---- *)
    | JMP => ∃lbl. inst.inst_operands = [Label lbl]
    | JNZ => ∃c l1 l2. inst.inst_operands = [c; Label l1; Label l2]
    | DJMP => ∃sel label_ops.
               inst.inst_operands = sel :: label_ops ∧
               EVERY (λop. IS_SOME (get_label op)) label_ops
    | RET => T
    | RETURN => LENGTH inst.inst_operands = 2
    | REVERT => LENGTH inst.inst_operands = 2
    | STOP => T
    | SINK => T
    (* ---- SSA ---- *)
    | PHI => LENGTH inst.inst_outputs = 1
    | ASSIGN => LENGTH inst.inst_operands = 1 ∧ LENGTH inst.inst_outputs = 1
    | NOP => T
    | PARAM => ∃idx. inst.inst_operands = [Lit idx] ∧
                     LENGTH inst.inst_outputs = 1
    (* ---- Allocation ---- *)
    | ALLOCA => ∃sz id. inst.inst_operands = [Lit sz; Lit id] ∧
                        LENGTH inst.inst_outputs = 1
    | PALLOCA => ∃sz id. inst.inst_operands = [Lit sz; Lit id] ∧
                         LENGTH inst.inst_outputs = 1
    | CALLOCA => ∃sz id rest. inst.inst_operands = Lit sz :: Lit id :: rest ∧
                              LENGTH inst.inst_outputs = 1
    (* ---- External calls ---- *)
    | CALL => LENGTH inst.inst_operands = 7 ∧ LENGTH inst.inst_outputs = 1
    | STATICCALL => LENGTH inst.inst_operands = 6 ∧ LENGTH inst.inst_outputs = 1
    | DELEGATECALL => LENGTH inst.inst_operands = 6 ∧ LENGTH inst.inst_outputs = 1
    | CREATE => LENGTH inst.inst_operands = 3 ∧ LENGTH inst.inst_outputs = 1
    | CREATE2 => LENGTH inst.inst_operands = 4 ∧ LENGTH inst.inst_outputs = 1
    (* ---- Special ---- *)
    | OFFSET => ∃op lbl. inst.inst_operands = [op; Label lbl] ∧
                         LENGTH inst.inst_outputs = 1
    | LOG => ∃tc rest. inst.inst_operands = Lit tc :: rest ∧
                       LENGTH rest = w2n tc + 2
    | SELFDESTRUCT => LENGTH inst.inst_operands = 1
    | INVALID => T
    (* ---- Assertions ---- *)
    | ASSERT => LENGTH inst.inst_operands = 1
    | ASSERT_UNREACHABLE => LENGTH inst.inst_operands = 1
    (* ---- INVOKE: Label + args ---- *)
    | INVOKE => ∃lbl args. inst.inst_operands = Label lbl :: args
End

(* The function has an entry block (fn_blocks is non-empty). *)
Definition fn_has_entry_def:
  fn_has_entry fn <=> fn.fn_blocks <> []
End

(* A basic block is well-formed: non-empty and ends with a terminator. *)
Definition bb_well_formed_def:
  bb_well_formed bb <=>
    bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode /\
    (* PHI instructions form a prefix of the block *)
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
           (EL j bb.bb_instructions).inst_opcode = PHI ==>
           (EL i bb.bb_instructions).inst_opcode = PHI)
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

(* ==========================================================================
   SSA and instruction predicates (general IR concepts)
   ========================================================================== *)

(* SSA form: each variable is defined at most once across all instructions. *)
Definition ssa_form_def:
  ssa_form fn <=>
    !v inst1 inst2.
      MEM inst1 (fn_insts fn) /\
      MEM inst2 (fn_insts fn) /\
      inst1.inst_outputs = [v] /\
      inst2.inst_outputs = [v]
      ==>
      inst1 = inst2
End

(* Check if instruction is a PHI. *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* ==========================================================================
   Context well-formedness
   ========================================================================== *)

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

(* ==========================================================================
   Whole-function inst_wf: every instruction in the function is well-formed.
   ========================================================================== *)

Definition fn_inst_wf_def:
  fn_inst_wf fn ⇔
    ∀bb inst.
      MEM bb fn.fn_blocks ∧
      MEM inst bb.bb_instructions ==>
      inst_wf inst
End

(* ==========================================================================
   Composed venom_wf — single precondition for high-level theorems.

   Level 1 (syntactic/structural): eliminates ~60 structural Error branches
   from step_inst_base.  No analysis required.
   ========================================================================== *)

Definition venom_wf_def:
  venom_wf ctx ⇔
    ctx_wf ctx ∧
    wf_invoke_targets ctx ∧
    (∀fn. MEM fn ctx.ctx_functions ==>
          wf_function fn ∧ fn_inst_wf fn)
End

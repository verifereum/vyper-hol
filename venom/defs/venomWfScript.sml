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

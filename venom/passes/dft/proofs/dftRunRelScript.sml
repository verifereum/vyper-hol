(*
 * Runs of a context and of its DFT schedule, with the same fuel.
 *
 * C' is C with every function rescheduled as dftScheduleOrder describes
 * (dft_fn_rel).  A run of a function of C and the run of its schedule in
 * C', from the function's entry block and with the same fuel, end alike
 * (dft_res_rel): the same continuing, returning or halting state, an
 * abort for an abort, and a revert for a revert.  When the run of C
 * errors, the run of C' does not continue or return either.
 *
 * Why the abort state may differ: the schedule can run instructions with
 * independent effects in another order before an instruction that stops
 * the run (an INVOKE whose callee aborts, a failing ASSERT).  It keeps the
 * fallible instructions in order (dft_fallible_order_kept), so the first
 * one to stop the run is the same on both sides; what can run early is an
 * instruction that cannot stop the run.  ctx_labels_bound keeps one with
 * a label operand (OFFSET) from erroring there.
 *)
Theory dftRunRel
Ancestors
  dftScheduleOrder dftStructural dftDefs venomExecSemantics venomWf
  venomInst venomState venomEffects list finite_map

Definition dft_res_rel_def:
  dft_res_rel r r' <=>
    case r of
      OK s => r' = OK s
    | IntRet v s => r' = IntRet v s
    | Halt s => r' = Halt s
    | Abort a s =>
        ?a' s'. r' = Abort a' s' /\ (a = Revert_abort ==> a' = Revert_abort)
    | Error e => (!s. r' <> OK s) /\ (!v s. r' <> IntRet v s)
End

(* Every label an instruction reads as a value is bound.  Jumps, INVOKE
   and PHIs use their labels as targets, not values. *)
Definition ctx_labels_bound_def:
  ctx_labels_bound C s <=>
    !fn inst l.
      MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
      MEM (Label l) inst.inst_operands /\ inst.inst_opcode <> INVOKE /\
      ~is_terminator inst.inst_opcode /\ ~is_pseudo inst.inst_opcode ==>
      l IN FDOM s.vs_labels
End

(* fn' is a DFT schedule of the well-formed, ALLOCA-free SSA function fn
   that keeps its fallible instructions in order. *)
Definition dft_fn_rel_def:
  dft_fn_rel fn fn' <=>
    fn'.fn_name = fn.fn_name /\
    wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\ fn_pseudos_prefix fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\
    LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks /\
    dft_fallible_order_kept fn fn'
End

(* Why it holds (unchecked notes):
   - Same fuel works: fuel is per block and per call depth, and the
     schedule visits the same blocks and makes the same calls.
   - Non-terminator Abort/Halt comes only from fallible opcodes (ASSERT,
     ASSERT_UNREACHABLE, RETURNDATACOPY) and INVOKE, which keep their order.
   - A non-fallible instruction with no effects (pure ops, ASSIGN, BUMP,
     OFFSET, environment reads such as GAS) changes only vs_vars and
     vs_inst_idx, and returns OK when inst_wf holds, its variables are
     defined and its labels are bound (ctx_labels_bound; nothing writes
     vs_labels).
   - Definedness at the earlier position: def_dominates_uses plus a
     strict-dominator invariant on the original run, like
     strict_dom_vars_defined (sccpCorrectnessProofs); vacuous at the entry.
   - Instructions with no must-order relation commute: the declared effects
     cover every state field each opcode reads or writes (STATICCALL changes
     no accounts, CREATE's memory write is empty, SSTORE only storage).
   - INVOKE: setup_callee resets vs_vars and vs_inst_idx, so hoisted
     effect-free instructions don't change the callee's run;
     merge_callee_state keeps the caller's variables and SSA keeps
     bind_outputs' names distinct from theirs.
   - Halt states are equal: a terminator runs last, after the whole block,
     and an INVOKE's halt is the callee's state. *)
Theorem dft_run_blocks_rel:
  !C C'.
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
    !fuel name fn fn' s.
      lookup_function name C.ctx_functions = SOME fn /\
      lookup_function name C'.ctx_functions = SOME fn' /\
      fn_entry_label fn = SOME s.vs_current_bb /\
      ctx_labels_bound C s ==>
      dft_res_rel (run_blocks fuel C fn s) (run_blocks fuel C' fn' s)
Proof
  cheat
QED

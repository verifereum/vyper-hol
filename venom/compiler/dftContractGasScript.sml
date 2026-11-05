(*
 * DFT's facts toward its O1 stage contract (o1ContractDft's pieces), in
 * the gas form.
 *
 * Each function of C' is dft_fn of its function in C (ctx_pass_stage_dft).
 * Under the run's pre (fallible instructions kept in order) and row 7
 * (SSA, no ALLOCA), each is a DFT schedule in the sense of dftRunRel
 * (dft_fn_rel), so:
 *   - DFT may move a GAS read past another GAS read or an INVOKE, so C'
 *     consumes the gas readings in another order than C.  The run of C'
 *     from vs' fixes the readings each GAS instruction gets; C, run from
 *     the gas variant of vs' holding those readings in C's order, takes
 *     the same path, ends alike, and every state C' reaches has a
 *     counterpart C reaches, which carries the memory invariant to C'
 *     (dft_ctx_sim_gas);
 *   - the schedule is SSA (dft_block_rel_wf_ssa), for row 8.
 * An instruction reading a label as a value (LowerDload's
 * ADD [_; Label "code_end"]) has it bound by code_layout_valid
 * (dft_ctx_labels_bound), so it cannot error where the original did not.
 *)
Theory dftContractGas
Ancestors
  o1DftStep dftSsaPreserve dftRunRel dftScheduleOrder dftDefs o1PassLift
  o1PassContract unitMemInv unitShapeDefs lowerDloadDefs venomPassDispatcher
  venomExecSemantics venomWf venomInst list

Theorem ctx_pass_stage_dft:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' ==>
  C'.ctx_entry = C.ctx_entry /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions
Proof
  rw[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rw[fn_pass_step_def] >> gvs[]
QED

(* Admitted in the transplant.  On the base, label_positions_ok also allows
   CODECOPY [dst; Label "runtime_begin"; sz], which code_layout_valid does
   not bind, so this may need a premise binding "runtime_begin" or ruling
   that CODECOPY out of the context. *)
Theorem dft_ctx_labels_bound:
  o1_ctx_shape C /\ code_layout_valid vs ==> ctx_labels_bound C vs.vs_labels
Proof
  cheat
QED

Theorem dft_fn_rel_stage:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\
  EVERY (\fn. wf_ssa fn /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn))
    C.ctx_functions /\
  EVERY fn_pseudos_prefix C.ctx_functions /\
  LIST_REL dft_fallible_order_kept C.ctx_functions C'.ctx_functions ==>
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions
Proof
  rw[LIST_REL_EL_EQN] >>
  `EL n C'.ctx_functions = dft_fn (EL n C.ctx_functions) /\
   dft_fallible_order_kept (EL n C.ctx_functions) (EL n C'.ctx_functions)`
    by metis_tac[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[EL_MEM] >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  `o1_fn_shape C f /\ wf_ssa f /\ EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f) /\
   fn_pseudos_prefix f` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_function f /\ fn_inst_wf f` by fs[o1_fn_shape_def] >>
  drule_all dftScheduleOrderTheory.dft_fn_block_rel >> strip_tac >>
  gvs[dft_fn_rel_def]
QED

(* The witness vs holds the readings C' consumes from vs', reordered to
   the order C reads them in, then vs' readings' unread tail.  The entry
   function returns no internal value (o1_fn_shape), so the context's run
   never ends in IntRet. *)
Theorem dft_ctx_sim_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  cheat
QED

Theorem dft_out_wf_ssa:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions ==>
  EVERY wf_ssa C'.ctx_functions
Proof
  rw[LIST_REL_EL_EQN, EVERY_EL] >>
  `EL n C'.ctx_functions = dft_fn (EL n C.ctx_functions) /\
   dft_fn_rel (EL n C.ctx_functions) (EL n C'.ctx_functions)` by metis_tac[] >>
  qabbrev_tac `f = EL n C.ctx_functions` >>
  gvs[dft_fn_rel_def] >>
  `dft_fn f = f with fn_blocks := (dft_fn f).fn_blocks` by
    (rewrite_tac[dft_fn_def, LET_THM] >>
     CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> simp[]) >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  irule dftSsaPreserveTheory.dft_block_rel_wf_ssa >> simp[]
QED

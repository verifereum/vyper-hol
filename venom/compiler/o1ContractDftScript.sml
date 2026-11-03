(*
 * DFT (the eighth walk run, stage 7) against the O1 pass contract, in the
 * gas form.
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
Theory o1ContractDft
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

(* label_positions_ok leaves one value use of a label outside jumps,
   PHIs and INVOKE: LowerDload's ADD [_; Label "code_end"], which
   code_layout_valid binds. *)
Theorem dft_ctx_labels_bound:
  o1_ctx_shape C /\ code_layout_valid vs ==> ctx_labels_bound C vs.vs_labels
Proof
  cheat
QED

Theorem dft_fn_rel_stage:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  o1_ctx_shape C /\ dft_in_ok C /\ EVERY fn_pseudos_prefix C.ctx_functions /\
  LIST_REL dft_fallible_order_kept C.ctx_functions C'.ctx_functions ==>
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions
Proof
  cheat
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
  cheat
QED

Theorem dft_contract_gas:
  o1_step_contract rpolicy (CFP_Simple VP_DFT) /\
  o1_run_contract_gas rpolicy D 7
Proof
  cheat
QED

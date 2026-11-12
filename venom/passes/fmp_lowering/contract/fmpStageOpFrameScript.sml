(*
 * The stage relation after one ordinary instruction, rebuilt from the
 * local result fmpStageOpSimPure and fmpStageOpSimMem give: the frame moves to the next index
 * of its block with its runner, ledger and site map unchanged.
 *
 * TOP-LEVEL:
 *   fmp_stage_op_frame - the stage relation at the next index
 *)
Theory fmpStageOpFrame
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLedgerProps livenessProofs ptrDiscipline
  o1PassContract venomExecSemantics venomState venomInst

(* Why: an ordinary instruction is no reclaim point and changes no
   analysis stack, so the next index has no restore and the same stack;
   the control map moves by one (no DALLOCA, and the only step reaching
   the root is RETPC_PARAM, by fmp_stage_root_crossing and
   fmp_stage_witness_pin); variables live after it were live before it
   or are its outputs (live_vars_at_propagate); its outputs are neither
   the runner (fmp_stage_witness_pin) nor a ledger mark, a DALLOCA's
   output (ssa_form); and coverage carries over (fmp_stage_covers_step). *)
Theorem fmp_stage_op_frame:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = OK s1 /\
  (!v. ~MEM v inst.inst_outputs ==>
       FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
       FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
     ?y. FLOOKUP t1.vs_vars v = SOME y /\
         (~retpc_var fn v ==>
          fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
            (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\
  ~s1.vs_halted /\ ~t1.vs_halted /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
  s1.vs_block_ctx = s.vs_block_ctx /\
  s1.vs_data_section = s.vs_data_section /\
  s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
  s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
  t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
  t1.vs_block_ctx = t.vs_block_ctx /\
  t1.vs_data_section = t.vs_data_section /\
  t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
  t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  cheat
QED

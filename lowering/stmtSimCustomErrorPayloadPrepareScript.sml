(* Registered argument transport and shifted payload preparation. *)
Theory stmtSimCustomErrorPayloadPrepare
Ancestors
  stmtSimCustomErrorPrefix abiEncoderWindowContract abiEncoderRegisteredEffect
  registeredAllocationWindow allocaSiteResource venomMemDefs finite_map pred_set list
  windowPhaseMem abiEncoderWindowPhase compilerInstructionSuffix freshWrites
  exprLoweringProps memContinuation words arithmetic venomState emitHelperProps loweringHalt

Theorem custom_error_registered_source_transport:
  abi_encoder_registered_effect ids [] s t /\ alloca_inv t /\
  FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid NOTIN ids /\ cap <= n /\
  abi_encoder_window_input ei at av a cap s.vs_memory ==>
  abi_encoder_window_input ei at av a cap t.vs_memory
Proof
  strip_tac >>
  irule abi_encoder_window_effect_source >>
  qexistsl_tac [`ids`, `[]`, `s`] >> simp[] >>
  rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (a,n)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `venomMemDefs$regions_disjoint (a,n) (b,sz)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem custom_error_payload_prepare:
  compile_alloc_buffer (B+32) sm = (buf,sa) /\
  emit_void MSTORE [buf.buf_operand; Lit selector] sa = ((),sc) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sc = (payload,st) /\
  fn_has_code sm sa func /\ fn_has_code sa sc func /\ fn_has_code sc st func /\
  alloca_room ctx func s /\ alloca_inv s /\ B+32 < 2 ** 64 /\
  (!b sz. FLOOKUP s.vs_allocas sm.cs_next_id = SOME (b,sz) ==> sz = B+32) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  FLOOKUP s.vs_allocas aid = SOME (a,n) /\ aid <> sm.cs_next_id /\ cap <= n /\
  eval_operand src s = SOME (n2w a) /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  abi_encoder_window_input ei at av a cap s.vs_memory ==>
  ?u d. mem_cont_sim ctx func s u /\ ~u.vs_halted /\
    u.vs_current_bb = st.cs_current_bb /\
    u.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME (n2w d) /\
    eval_operand payload u = SOME (n2w (d+32)) /\
    eval_operand src u = SOME (n2w a) /\
    (!x. src = Var x \/ payload = Var x \/ buf.buf_operand = Var x ==>
      not_fresh_at st x) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (d,B+32) /\
    FLOOKUP u.vs_allocas aid = SOME (a,n) /\
    d+(B+32) <= u.vs_alloca_next /\ d+(B+32) < dimword (:256) /\
    alloca_room ctx func u /\ alloca_inv u /\
    abi_encoder_window_input ei at av a cap u.vs_memory /\
    abi_encoder_registered_effect {sm.cs_next_id} [] s u
Proof
  strip_tac >> drule_all custom_error_selector_prefix_run >> strip_tac >>
  `eval_operand (Lit 32w) t = SOME 32w` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_mem >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  drule window_phase_control >> strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_effect >> strip_tac >>
  `abi_encoder_registered_effect {sm.cs_next_id} [] t u` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{}`, `[]`] >> simp[]) >>
  `abi_encoder_registered_effect {sm.cs_next_id} [] s u` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  `FLOOKUP u.vs_allocas sm.cs_next_id = SOME (d,B+32) /\
   FLOOKUP u.vs_allocas aid = SOME (a,n)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `sm.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= st.cs_next_var` by
    (drule compile_alloc_buffer_parts >> strip_tac >>
     imp_res_tac added_insts_emit_void >> imp_res_tac added_insts_emit_op >>
     qpat_x_assum `ci_mono sa sc` mp_tac >>
     qpat_x_assum `ci_mono sc st` mp_tac >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `!x. src = Var x ==> not_fresh_at sc x` by
    metis_tac[not_fresh_at_mono] >>
  `eval_operand src t = SOME (n2w a)` by metis_tac[] >>
  `eval_operand src u = SOME (n2w a) /\
   eval_operand buf.buf_operand u = SOME (n2w d)` by
    metis_tac[window_phase_operand] >>
  `!x. src = Var x \/ payload = Var x \/ buf.buf_operand = Var x ==>
    not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  `d+(B+32) <= u.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  `abi_encoder_window_input ei at av a cap u.vs_memory` by
    (irule custom_error_registered_source_transport >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`aid`, `{sm.cs_next_id}`, `n`, `s`] >> simp[]) >>
  qexistsl_tac [`u`, `d`] >>
  simp[GSYM word_add_n2w] >> metis_tac[mem_cont_sim_trans]
QED

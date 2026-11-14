(*
 * O1 source safety up to a gas cut.
 *
 * o1_src_inv asks every reachable state of a run to be safe.  A run that is
 * only known to be safe until the n-th GAS read (a prefix of a semantic gas
 * mask) has the same facts for the states before that read: gas_cut n vs s
 * says s has popped fewer than n of vs's gas readings.  o1_ptr_safe_upto
 * keeps o1_src_inv's context-only facts and guards its pointer discipline
 * and taint bound by the cut; o1_safe_upto adds the whole-run DLOAD
 * headroom and the guarded raw memory and DLOAD offset facts.  Every n
 * holds when o1_src_inv does (o1_src_inv_safe_upto).
 *)
Theory o1SafeUpto
Ancestors
  gasEvents
  o1PassContract memSafeRun contextRawReachable contextCodegenRel unitMemInv
  ptrDiscipline lowerDloadDefs staticLayoutDefs venomExecSemantics
  venomExecProofs venomState stateFrame frameRawProjection list

Definition gas_cut_def:
  gas_cut n (vs:venom_state) (s:venom_state) <=>
    LENGTH vs.vs_gas_readings < n + LENGTH s.vs_gas_readings
End

(* ptr_discipline's clauses, each per-state one guarded by the cut. *)
Definition ptr_discipline_upto_def:
  ptr_discipline_upto (lo:num) n ctx vs <=>
    lo <= vs.vs_alloca_next /\
    (?P. EVERY (\fn. fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn))
           ctx.ctx_functions) /\
    !stk PG G tn fn inst s.
      frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s ==>
      access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
      allocas_from lo s /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s)
End

(* taint_within's request clause and its halt clause (final_taint
   inlined), guarded by the cut at the pre-step state. *)
Definition taint_within_upto_def:
  taint_within_upto D n ctx vs <=>
    (!stk PG G tn fn inst s fuel s'.
       frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = OK s' /\
       LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
       tn.t_stor SUBSET
         D.d_stor s.vs_call_ctx.cc_address
           (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
       tn.t_trans SUBSET
         D.d_trans s.vs_call_ctx.cc_address
           (s.vs_transient s.vs_call_ctx.cc_address)) /\
    (!stk PG G tn fn inst s fuel s_h.
       frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
       active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel ctx inst s = Halt s_h ==>
       (step_taint inst s s_h tn).t_stor SUBSET
         D.d_stor s_h.vs_call_ctx.cc_address
           (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
       (step_taint inst s s_h tn).t_trans SUBSET
         D.d_trans s_h.vs_call_ctx.cc_address
           (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
       (step_taint inst s s_h tn).t_imm SUBSET D.d_imm s_h.vs_immutables /\
       ret_taint tn inst s SUBSET D.d_ret s_h.vs_returndata)
End

(* The context facts and the guarded pointer and taint halves. *)
Definition o1_ptr_safe_upto_def:
  o1_ptr_safe_upto D lo n C vs <=>
    reserved_intervals_wf C.ctx_global_reserved /\
    EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ ~ctx_has_dalloca C /\
    fmp_free_ctx C /\ fixed_region_reserved lo C /\
    ptr_discipline_upto lo n C vs /\ taint_within_upto D n C vs
End

Definition o1_safe_upto_def:
  o1_safe_upto D lo n C vs <=>
    o1_ptr_safe_upto D lo n C vs /\ mem_inv dload_headroom_ok C vs /\
    (!fn inst s.
       raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
       raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s)
End

Theorem gas_cut_mono:
  m <= n /\ gas_cut m vs s ==> gas_cut n vs s
Proof
  rw[gas_cut_def]
QED

Theorem gas_cut_readings_mono:
  gas_cut n vs t /\ LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings ==>
  gas_cut n vs s
Proof
  simp[gas_cut_def]
QED

Theorem ptr_discipline_upto_mono:
  m <= n /\ ptr_discipline_upto lo n ctx vs ==> ptr_discipline_upto lo m ctx vs
Proof
  rw[ptr_discipline_upto_def] >> metis_tac[gas_cut_mono]
QED

Theorem taint_within_upto_mono:
  m <= n /\ taint_within_upto D n ctx vs ==> taint_within_upto D m ctx vs
Proof
  rw[taint_within_upto_def] >> metis_tac[gas_cut_mono]
QED

Theorem o1_ptr_safe_upto_mono:
  m <= n /\ o1_ptr_safe_upto D lo n C vs ==> o1_ptr_safe_upto D lo m C vs
Proof
  rw[o1_ptr_safe_upto_def] >>
  metis_tac[ptr_discipline_upto_mono, taint_within_upto_mono]
QED

Theorem o1_safe_upto_mono:
  m <= n /\ o1_safe_upto D lo n C vs ==> o1_safe_upto D lo m C vs
Proof
  rw[o1_safe_upto_def] >>
  metis_tac[gas_cut_mono, o1_ptr_safe_upto_mono]
QED

Theorem ptr_discipline_upto_whole:
  ptr_discipline lo ctx vs ==> !n. ptr_discipline_upto lo n ctx vs
Proof
  rw[ptr_discipline_def, ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem taint_within_upto_whole:
  taint_within D ctx vs ==> !n. taint_within_upto D n ctx vs
Proof
  rw[taint_within_def, taint_within_upto_def] >>
  fs[final_taint_def] >> metis_tac[]
QED

Theorem o1_src_inv_ptr_safe_upto:
  o1_src_inv D C vs /\ fixed_region_reserved lo C /\
  ptr_discipline lo C vs ==>
  !n. o1_safe_upto D lo n C vs
Proof
  rw[o1_src_inv_def, o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  fs[mem_inv_raw_reachable] >>
  metis_tac[ptr_discipline_upto_whole, taint_within_upto_whole]
QED

Theorem o1_src_inv_safe_upto:
  o1_src_inv D C vs ==> ?lo. !n. o1_safe_upto D lo n C vs
Proof
  strip_tac >> drule o1_src_inv_ptr_safe_upto >>
  fs[o1_src_inv_def] >> metis_tac[]
QED

(* Code and data section never change along a raw run. *)
Theorem raw_reachable_code_data:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rw[enters_block_def, setup_callee_def] >>
  imp_res_tac venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  imp_res_tac step_inst_ok_code_data >>
  gvs[setup_callee_def, AllCaseEqs()] >>
  qpat_x_assum `s_phi = _` (fn th => once_rewrite_tac [th]) >> simp[]
QED

(* A producer that checks DLOAD offsets against the data section (the
   mem_safe checker) gets o1_safe_upto's offset bound. *)
Theorem dload_offset_ok_upto_intro:
  code_layout_valid vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     inst_dload_in_section inst s) ==>
  !fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    dload_offset_ok C fn inst s
Proof
  rw[dload_offset_ok_def] >>
  first_x_assum drule_all >> rw[inst_dload_in_section_def] >>
  drule raw_reachable_code_data >> strip_tac >>
  gvs[code_layout_valid_def] >>
  `dimword (:256) DIV 2 < dimword (:256)` by
    (irule arithmeticTheory.DIV_LESS >> simp[wordsTheory.ZERO_LT_dimword]) >>
  decide_tac
QED

(* At n past every reading the cut holds of every state. *)
Theorem gas_cut_whole[simp]:
  gas_cut (SUC (LENGTH vs.vs_gas_readings)) vs s
Proof
  simp[gas_cut_def]
QED

(* States with the same execution frame have popped the same readings. *)
Theorem gas_cut_execution_frame:
  gas_cut n vs s' /\ execution_frame s' = execution_frame s ==>
  gas_cut n vs s
Proof
  strip_tac >>
  `s'.vs_gas_readings = s.vs_gas_readings` by
    (qpat_x_assum `execution_frame _ = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  fs[gas_cut_def]
QED

(* The whole-run facts are the guarded ones at that n. *)
Theorem ptr_discipline_upto_all:
  ptr_discipline_upto lo (SUC (LENGTH vs.vs_gas_readings)) ctx vs ==>
  ptr_discipline lo ctx vs
Proof
  rw[ptr_discipline_def, ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem taint_within_upto_all:
  taint_within_upto D (SUC (LENGTH vs.vs_gas_readings)) ctx vs ==>
  taint_within D ctx vs
Proof
  rw[taint_within_def, taint_within_upto_def, final_taint_def] >>
  metis_tac[]
QED

(* The alloca frontier fits a word at every frame-reachable state before the
   cut.  ConcretizeMemLoc's layout chain needs it (cache entries stay below
   dimword); LowerDload's output provides it on the lowered context. *)
Definition alloca_frontier_upto_def:
  alloca_frontier_upto n C vs <=>
    !stk PG G tn fn inst s.
      frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s ==>
      s.vs_alloca_next < dimword (:256)
End

Theorem alloca_frontier_upto_mono:
  m <= n /\ alloca_frontier_upto n C vs ==> alloca_frontier_upto m C vs
Proof
  rw[alloca_frontier_upto_def] >> metis_tac[gas_cut_mono]
QED

Theorem mem_inv_raw_alloca_frontier_upto:
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs ==>
  !n. alloca_frontier_upto n C vs
Proof
  rw[alloca_frontier_upto_def, mem_inv_raw_reachable] >>
  drule_all frame_reachable_raw >> strip_tac >>
  first_x_assum drule >> simp[raw_mem_ok_def]
QED

Theorem o1_safe_upto_alloca_frontier:
  EVERY wf_function C.ctx_functions /\ o1_safe_upto D lo n C vs ==>
  alloca_frontier_upto n C vs
Proof
  rw[alloca_frontier_upto_def, o1_safe_upto_def] >>
  drule_all frame_reachable_raw >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> fs[raw_mem_ok_def]
QED

Theorem enters_block_readings:
  enters_block fn s s1 ==> s1.vs_gas_readings = s.vs_gas_readings
Proof
  rw[enters_block_def] >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem ptr_discipline_upto_at:
  ptr_discipline_upto lo n C vs0 /\
  frame_reachable vs0 C stk PG G tn fn inst s /\ gas_cut n vs0 s ==>
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca C ==> allocas_below_fmp s)
Proof
  simp[ptr_discipline_upto_def] >> metis_tac[]
QED

Theorem taint_within_upto_request:
  taint_within_upto D n ctx vs /\
  frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' /\
  LENGTH s.vs_requests < LENGTH s'.vs_requests ==>
  tn.t_stor SUBSET
    D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET
    D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)
Proof
  strip_tac >> fs[taint_within_upto_def] >> first_x_assum drule_all >> simp[]
QED

Theorem taint_within_upto_halt:
  taint_within_upto D n ctx vs /\
  frame_reachable vs ctx stk PG G T0 fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = Halt s_h ==>
  (step_taint inst s s_h T0).t_stor SUBSET
    D.d_stor s_h.vs_call_ctx.cc_address
      (s_h.vs_accounts s_h.vs_call_ctx.cc_address).storage /\
  (step_taint inst s s_h T0).t_trans SUBSET
    D.d_trans s_h.vs_call_ctx.cc_address
      (s_h.vs_transient s_h.vs_call_ctx.cc_address) /\
  (step_taint inst s s_h T0).t_imm SUBSET D.d_imm s_h.vs_immutables /\
  ret_taint T0 inst s SUBSET D.d_ret s_h.vs_returndata
Proof
  strip_tac >> fs[taint_within_upto_def] >> first_x_assum drule_all >> simp[]
QED

Theorem ptr_discipline_upto_fn_ptr_ok:
  ptr_discipline_upto lo n ctx vs ==>
  lo <= vs.vs_alloca_next /\
  ?P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
      !stk PG G tn fn inst s.
        frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut n vs s ==>
        access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
        allocas_from lo s /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp s)
Proof
  rewrite_tac[ptr_discipline_upto_def] >> strip_tac >> asm_rewrite_tac[] >>
  qexists_tac `P` >> asm_rewrite_tac[] >>
  fs[EVERY_MEM]
QED

Theorem frame_next_gas_cut:
  step_inst fuel ctx inst s = OK s' /\
  gas_cut cut vs (s' with vs_inst_idx := k) ==> gas_cut cut vs s
Proof
  rw[] >> drule gasCountTheory.step_inst_gas_le >> strip_tac >>
  `LENGTH (s' with vs_inst_idx := k).vs_gas_readings <=
   LENGTH s.vs_gas_readings` by simp[] >>
  metis_tac[gas_cut_readings_mono]
QED

Theorem frame_block_gas_cut:
  step_inst fuel ctx inst s = OK s' /\ enters_block fn s' s1 /\
  gas_cut cut vs s1 ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac gasCountTheory.step_inst_gas_le >> imp_res_tac enters_block_readings >>
  `LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings` by gvs[] >>
  metis_tac[gas_cut_readings_mono]
QED

Theorem frame_call_gas_cut:
  setup_callee callee args s = SOME cs /\ enters_block callee cs s1 /\
  gas_cut cut vs s1 ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac gasOracleReplayTheory.gas_setup_callee_readings >>
  imp_res_tac enters_block_readings >>
  `LENGTH s1.vs_gas_readings <= LENGTH s.vs_gas_readings` by gvs[] >>
  metis_tac[gas_cut_readings_mono]
QED

Theorem frame_ret_gas_cut:
  step_inst fuel ctx rinst s = IntRet ret s_end /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state c s_end)) = SOME s' /\
  gas_cut cut vs (s' with vs_inst_idx := k) ==> gas_cut cut vs s
Proof
  rw[] >> imp_res_tac gasCountTheory.step_inst_int_ret_gas_le >>
  imp_res_tac gasOracleReplayTheory.gas_bind_outputs_readings >>
  `(s' with vs_inst_idx := k).vs_gas_readings = s_end.vs_gas_readings` by
    (Cases_on `ret.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `gas_cut cut vs s_end` by gvs[gas_cut_def] >>
  metis_tac[gas_cut_readings_mono]
QED

Theorem ld_budget_cut:
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  0 < j ==>
  gas_cut ncut vs s
Proof
  rw[gas_cut_def] >> decide_tac
QED

Theorem ld_blocks_ret_cut:
  run_blocks k C fn s = IntRet ir se /\
  j + LENGTH vs.vs_gas_readings <= ncut + LENGTH s.vs_gas_readings /\
  LENGTH (gas_events_blocks k C fn s) < j ==>
  gas_cut ncut vs se
Proof
  strip_tac >> fs[gas_events_length] >>
  mp_tac (cj 3 gasCountTheory.gas_count_suffix) >>
  disch_then (qspecl_then [`k`,`C`,`fn`,`s`] mp_tac) >>
  simp[gasCountTheory.gas_count_suffix_def] >> strip_tac >>
  simp[gas_cut_def, LENGTH_DROP] >> decide_tac
QED

Theorem run_state_ok_gas_readings:
  o1_run_state_ok vs ==> o1_run_state_ok (vs with vs_gas_readings := g)
Proof
  simp[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
       lowerDloadDefsTheory.code_layout_valid_def]
QED

Theorem ld_run_enters:
  terminates (run_blocks k C fn v) \/ gas_events_blocks k C fn v <> [] ==>
  ?sn. enters_block fn v sn
Proof
  Cases_on `k` >- simp[venomExecProofsTheory.run_blocks_zero_error, Once gas_events_blocks_def, passSimulationDefsTheory.terminates_def] >>
  simp[Once run_blocks_def, Once gas_events_blocks_def] >>
  Cases_on `lookup_block v.vs_current_bb fn.fn_blocks` >> simp[passSimulationDefsTheory.terminates_def] >>
  rename1 `lookup_block v.vs_current_bb fn.fn_blocks = SOME dest` >>
  `(?p. eval_phis v dest.bb_instructions = OK p) \/
   (?e. eval_phis v dest.bb_instructions = Error e)` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  gvs[passSimulationDefsTheory.terminates_def, enters_block_def]
QED

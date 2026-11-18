(* Couple the final private MLOAD to its operational and indexed successors. *)
Theory gasFocusLowerDloadPrivateFrameSuccessor
Ancestors
  gasFocusLowerDloadScratchNext gasFocusLowerDloadScratchFrame
  lowerDloadCurrentSafety lowerDloadPtrDloadOrigins lowerDloadPtrPhase
  lowerDloadAllocationOrigins lowerDloadPublicTrace lowerDloadSafetyLocations
  o1ContractLowerDload ptrDisciplineEmptyTaint oracleExecProps
  venomFnScheduleRunner o1SafeUpto o1PassContract lowerDloadDefs ptrDiscipline
  lowerDloadSafetyRelation lowerDloadSafetyAmbient lowerDloadSafetyKernel
  lowerDloadSafetyAllocation lowerDloadOracleCallAssembly lowerDloadPtrRel
  lowerDloadPtrReplay venomInst venomState irSupply unitTransformDefs
  finite_map pred_set list words arithmetic

Theorem ld_private_fresh_limit[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ mem_inv dload_headroom_ok C vs /\
  ALL_DISTINCT (MAP (\g. g.lf_fn) (f::fs)) /\
  ld_private f d ai /\ FLOOKUP t0.vs_allocas ai = NONE ==>
  t0.vs_alloca_next + 32 < dimword (:256) /\
  t0.vs_alloca_next + 32 <= dyn_floor C vs
Proof
  strip_tac >> drule_all ld_sync_fresh_charge >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `dload_headroom_ok C fn inst s` by
    (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  `t0.vs_alloca_next + 32 <= s.vs_alloca_next + 32 * ctx_dload_count C` by decide_tac >>
  qpat_x_assum `dload_headroom_ok _ _ _ _` mp_tac >>
  simp[dload_headroom_ok_def, GSYM ctx_has_dalloca_def, dyn_floor_def] >>
  IF_CASES_TAC >> simp[] >> strip_tac >-
    (`s.vs_initial_fmp = vs.vs_initial_fmp` by
       (drule ld_sync_source >> metis_tac[frame_reachable_initial_fmp]) >>
     gvs[] >> decide_tac) >>
  decide_tac
QED

Theorem ld_private_reset_position[local]:
  dload_control_match supply fn gn s t inst X 0 ==>
  ld_envelope supply fn s s.vs_inst_idx X t.vs_inst_idx /\
  ld_prefix C gn X t.vs_inst_idx 0 t t
Proof
  simp[dload_control_match_def, ld_envelope_def, ld_prefix_zero] >>
  rpt strip_tac >> metis_tac[pairTheory.FST, pairTheory.SND]
QED

Theorem ld_focus_private_frame_successor:
  let U = set (fn_ir_vars fn) in
  let V = U DIFF {v | retpc_var fn v} in
  let orig = set (fn_ir_inst_ids fn) in
  let q = u with vs_inst_idx := SUC t.vs_inst_idx in
  let m = EL 3 X in
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\ o1_safe_upto D lo n C vs /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
     list_precedes (EL j (f::fs)).lf_fn.fn_name (EL k (f::fs)).lf_fn.fn_name names) /\
  ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ t0.vs_inst_idx = p /\
  ld_prefix C' (ld_image f) X p 3 t0 t /\
  dload_boundary_core (dyn_floor C vs) lo (r::rs) V Ws PG PH G H0 tn un0 s t0 stk ds /\
  r.dr_scratch = FDOM t0.vs_allocas DIFF orig /\
  dload_control_match f.lf_supply fn (ld_image f) s t0 inst X 0 /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
  dload_prefix_match pf C' PH X 3 t0 H0 un0 t H un /\
  s.vs_gas_readings = t0.vs_gas_readings /\ t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs) /\
  step_inst fuel C' m t = OK u /\ active_inst (ld_image f) j q /\ gas_cut n vs q ==>
  ?ss g r1 i Y.
    let ss1 = ss with vs_inst_idx := SUC s.vs_inst_idx in
    let G1 = step_prov PG G inst ss in
    let tn1 = step_taint inst s ss tn in
    let H1 = step_prov PH H m u in
    let un1 = step_taint m t u un in
    step_inst 0 C inst s = OK ss /\
    g = f with <|lf_src := ss1; lf_tgt := q; lf_H := set_prov f.lf_H [out] NONE;
                 lf_tv := tn1.t_var; lf_E := inst.inst_id INSERT f.lf_E|> /\
    ld_global lo A (g::fs) /\
    ld_sync lo P C vs stk PG G1 tn1 fn i ss1 q A (g::fs) N /\
    ld_image g = ld_image f /\
    ld_envelope g.lf_supply fn ss1 ss1.vs_inst_idx Y q.vs_inst_idx /\
    ld_prefix C' (ld_image g) Y q.vs_inst_idx 0 q q /\
    0 < LENGTH Y /\ j = EL 0 Y /\
    r1.dr_source = r.dr_source /\ r1.dr_scratch = (EL 0 X).inst_id INSERT r.dr_scratch /\
    r1.dr_scratch = FDOM q.vs_allocas DIFF orig /\
    dload_boundary_core (dyn_floor C vs) lo (r1::rs) V Ws PG PH G1 H1 tn1 un1 ss1 q stk ds /\
    dload_control_match g.lf_supply fn (ld_image g) ss1 q i Y 0 /\
    dload_prefix_match pf C' PH Y 0 q H1 un1 q H1 un1 /\
    (!v. v IN U ==> (lookup_var v ss1 = NONE <=> lookup_var v q = NONE)) /\
    ss1.vs_gas_readings = q.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH ss1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (g::fs)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_then strip_assume_tac ld_sync_source >>
  drule_then (strip_assume_tac o REWRITE_RULE [HD]) ld_sync_active >>
  drule_all_then strip_assume_tac ld_sync_fn_shape >>
  drule_then strip_assume_tac o1_fn_shape_components >>
  drule_all ld_dload_envelope_temporary >>
  disch_then (qx_choose_then `ai` (qx_choose_then `zi` (qx_choose_then `ci`
    (qx_choose_then `mi` (qx_choose_then `a` (qx_choose_then `z` strip_assume_tac)))))) >>
  `LENGTH X = 4 /\ (EL 0 X).inst_id = ai /\ (EL 3 X).inst_opcode = MLOAD` by simp[] >>
  `u.vs_gas_readings = t.vs_gas_readings` by
    (`(EL 3 X).inst_opcode <> INVOKE /\ (EL 3 X).inst_opcode <> GAS` by simp[] >>
     drule_all step_inst_noninvoke_gas_readings >> simp[]) >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  mp_tac (Q.INST [`h` |-> `3`] ld_focus_dload_scratch_next) >>
  (impl_tac >- simp[]) >>
  strip_tac >> suspend "ghost"
QED

Resume ld_focus_private_frame_successor[ghost]:
  `mem_inv dload_headroom_ok C vs /\ ptr_discipline_upto lo n C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  `taint_ok fn tn inst s` by
    (drule_all (cj 2 concretizeLayoutCutSafeTheory.ptr_discipline_upto_at) >> simp[]) >>
  `dload_offset_ok C fn inst s` by
    (`raw_reachable vs C fn inst s` by metis_tac[ld_frame_raw_reachable] >>
     qpat_assum `o1_safe_upto _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [o1_safe_upto_def]) >>
     qpat_assum `!fn inst s. raw_reachable _ _ fn inst s /\ _ ==> _`
       (qspecl_then [`fn`, `inst`, `s`] mp_tac) >> simp[]) >>
  `code_layout_valid s` by (irule ld_sync_source_code_layout_static >> metis_tac[]) >>
  `ai NOTIN set (fn_ir_inst_ids fn)` by
    (drule ld_private_supply_bound >>
     fs[ir_supply_covers_fn_def, EVERY_MEM] >> metis_tac[NOT_LESS]) >>
  `FDOM s.vs_allocas SUBSET set (fn_ir_inst_ids fn)` by
    (`vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
     drule_all ld_frame_allocation_origins >> simp[]) >>
  `FLOOKUP t0.vs_allocas ai = NONE ==>
     t0.vs_alloca_next + 32 < dimword (:256) /\
     t0.vs_alloca_next + 32 <= dyn_floor C vs` by
    (strip_tac >> irule ld_private_fresh_limit >>
     goal_assum (drule_at Any) >> metis_tac[ld_frames_distinct]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) (ld_image f).fn_blocks)` by
    (`?next. lower_dload_function_supply f.lf_supply fn = (ld_image f,next)` by
       (qexists `SND (lower_dload_function_supply f.lf_supply fn)` >>
        simp[ld_image_def, pairTheory.PAIR]) >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `?x. eval_operand off s = SOME x /\ eval_operand off t0 = SOME x` by
    suspend "offset" >>
  `?supply nxt. lower_dload_inst_supply supply inst = (X,nxt)` by
    metis_tac[dload_control_match_expansion] >>
  `(EL 0 X).inst_outputs = [a] /\ (EL 1 X).inst_outputs = [z] /\
    a NOTIN set (fn_ir_vars fn) /\ z NOTIN set (fn_ir_vars fn) /\
    (EL 0 X).inst_id NOTIN set (fn_ir_inst_ids fn)` by simp[] >>
  mp_tac (Q.INST [`fl` |-> `dyn_floor C vs`, `orig` |-> `set (fn_ir_inst_ids fn)`,
                  `av` |-> `a`, `cv` |-> `z`, `sigma` |-> `f.lf_supply`,
                  `gn` |-> `ld_image f`]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] ld_focus_scratch_actual_next))) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `r1` (qx_choose_then `i` (qx_choose_then `Y` strip_assume_tac))) >>
  suspend "reset"
QED

Resume ld_focus_private_frame_successor[offset]:
  `?ow basew. eval_operand off t0 = SOME ow /\
      eval_operand (Label "code_end") t0 = SOME basew` by
    (irule ld_dload_trace_offset >>
     qexistsl [`C'`, `X`, `a`, `ld_image f`, `p`, `t`] >> simp[]) >>
  drule_then strip_assume_tac ld_sync_ptr_ok >>
  drule_then strip_assume_tac ld_sync_labels >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `eval_operand off s = SOME ow` by
    (drule ld_dload_operand_equal >> simp[] >>
     disch_then drule >> simp[] >> disch_then (qspec_then `tn` mp_tac) >> simp[]) >>
  qexists `ow` >> simp[]
QED

Resume ld_focus_private_frame_successor[reset]:
  `3 < LENGTH X /\ (EL 3 X).inst_opcode <> INVOKE` by simp[] >>
  drule_all dload_prefix_extend_mixed >>
  disch_then (assume_tac o REWRITE_RULE [numLib.REDUCE_CONV ``SUC 3``]) >>
  drule_all dload_supply_prefix_alloca_domain >> strip_tac >>
  `r1.dr_scratch = FDOM (u with vs_inst_idx := SUC t.vs_inst_idx).vs_allocas DIFF
                   set (fn_ir_inst_ids fn)` by simp[INSERT_DIFF] >>
  `g.lf_supply = f.lf_supply /\ ld_image g = ld_image f` by simp[ld_image_def] >>
  qpat_assum `dload_control_match _ _ _ _ _ i Y 0`
    (fn th => assume_tac (MATCH_MP (cj 1 dload_control_match_boundary) th) >>
      strip_assume_tac (MATCH_MP ld_private_reset_position th)) >>
  suspend "finish"
QED

Resume ld_focus_private_frame_successor[finish]:
  `0 < LENGTH Y /\ j = EL 0 Y` by
    (`0 < LENGTH Y` by fs[lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
     Cases_on `Y` >> gvs[]) >>
  qpat_x_assum `SUC t.vs_inst_idx = _` kall_tac >>
  `active_inst fn i g.lf_src` by simp[] >>
  qpat_assum `!next. active_inst fn next g.lf_src ==> _`
    (qspec_then `i` (fn th => drule_then assume_tac th)) >>
  qexistsl [`ss`, `g`, `r1`, `i`, `Y`] >>
  gs[lowerDloadPtrPhaseTheory.dload_prefix_zero]
QED

Finalise ld_focus_private_frame_successor

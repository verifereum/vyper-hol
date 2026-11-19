(* Resume a successful evaluator suffix at the end of the private expansion. *)
Theory gasFocusLowerDloadScratchBody
Ancestors
  gasFocusLowerDloadScratchNext lowerDloadExpansionGhost lowerDloadReturnOrdinary
  lowerDloadSafetyLocations lowerDloadSafetyAmbient lowerDloadSafetyKernel
  lowerDloadSafetyRelation lowerDloadPublicTrace o1PassContract passSharedField
  venomExecProofs venomInst venomState contextCodegenRel list
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_scratch_body_next:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs s /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
     list_precedes (EL j (f::fs)).lf_fn.fn_name (EL k (f::fs)).lf_fn.fn_name names) /\
  ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ t0.vs_inst_idx = p /\
  ld_prefix C' (ld_image f) X p h t0 t /\ SUC h = LENGTH X /\
  step_inst fuel C' (EL h X) t = OK u /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  ld_return_cont C fn cs s /\ s.vs_gas_readings = t0.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs) /\
  lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
  get_instruction bb (SUC t.vs_inst_idx) = SOME j ==>
  ?ss g i Y.
    step_inst 0 C inst s = OK ss /\ g.lf_fn = fn /\
    g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
    g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx) /\ ld_image g = ld_image f /\
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn i g.lf_src (u with vs_inst_idx := SUC t.vs_inst_idx) A (g::fs) N /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs) /\
    ld_envelope g.lf_supply fn g.lf_src g.lf_src.vs_inst_idx Y (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx /\
    ld_prefix C' (ld_image g) Y (u with vs_inst_idx := SUC t.vs_inst_idx).vs_inst_idx 0 (u with vs_inst_idx := SUC t.vs_inst_idx) (u with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block (u with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb (ld_image g).fn_blocks = SOME bb /\ HD Y = j /\
    ld_return_cont C fn cs g.lf_src /\ g.lf_src.vs_gas_readings = (u with vs_inst_idx := SUC t.vs_inst_idx).vs_gas_readings /\
    EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
      LENGTH g.lf_src.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) (g::fs)
Proof
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  drule_all ld_focus_dload_scratch_next >>
  disch_then (qx_choose_then `ss` (qx_choose_then `v`
    (qx_choose_then `g` (qx_choose_then `c` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  drule_all ld_sync_fn_shape >> disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  drule ld_sync_active >> simp[NoAsms] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD]) X /\
   MEM (EL h X).inst_opcode [ALLOCA; ADD; CODECOPY; MLOAD; DLOAD]` by
    (drule_all ld_dload_envelope_temporary >> strip_tac >> simp[]) >>
  drule_all ld_expansion_prefix_nonghost >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (drule_all ld_expansion_step_nonghost >> simp[]) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `step_inst 0 C inst s = OK ss`
       (mp_then Any mp_tac step_inst_preserves_all) >>
     simp[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  `q.vs_current_bb = t.vs_current_bb /\ q.vs_inst_idx = SUC t.vs_inst_idx` by simp[Abbr `q`] >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X` by simp[] >>
  `lookup_block q.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
   get_instruction bb q.vs_inst_idx = SOME j` by
    (qpat_assum `q.vs_current_bb = t.vs_current_bb` SUBST1_TAC >>
     qpat_assum `q.vs_inst_idx = SUC t.vs_inst_idx` SUBST1_TAC >>
     asm_rewrite_tac[]) >>
  `active_inst (ld_image f) j q` by
    (simp[active_inst_def] >> qexists_tac `bb` >>
     qpat_assum `get_instruction bb q.vs_inst_idx = SOME j` mp_tac >>
     simp[NoAsms, get_instruction_def] >> strip_tac >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `ld_image f = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  `?i Y. active_inst fn i (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
     ld_envelope f.lf_supply fn (ss with vs_inst_idx := SUC s.vs_inst_idx)
       (SUC s.vs_inst_idx) Y (p + LENGTH X) /\
     0 < LENGTH Y /\ j = EL 0 Y` by
    (irule ld_envelope_successor_head >> conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`ld_image f`, `q`, `s`] >> asm_rewrite_tac[]) >>
  suspend "resume_point"
QED

Resume ld_focus_scratch_body_next[resume_point]:
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
   g.lf_Q = f.lf_Q /\ g.lf_supply = f.lf_supply /\
   g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\ g.lf_tgt = q` by
    simp[Abbr `q`] >>
  qpat_x_assum `g = _` kall_tac >>
  `^ld_probe_stable lo P Sigma names fs0 f0 A0 A (g::fs)` by
    (`fs = fs0` by fs[] >>
     qpat_assum `fs = fs0` (SUBST_ALL_TAC o SYM) >>
     BETA_TAC >> irule (BETA_RULE ld_stable_head_replace) >>
     metis_tac[]) >>
  `ld_return_cont C fn cs (ss with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ld_return_cont_next >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`inst`,`0`] >> simp[is_terminator_def]) >>
  `active_inst fn i g.lf_src` by simp[] >>
  qpat_x_assum `!next. active_inst fn next g.lf_src ==> _` drule >> strip_tac >>
  `ld_image g = ld_image f` by simp[ld_image_def] >>
  `q.vs_gas_readings = t0.vs_gas_readings` by simp[Abbr `q`] >>
  qexistsl_tac [`ss`,`g`,`i`,`Y`] >>
  asm_rewrite_tac[] >> gvs[ld_prefix_zero]
QED

Finalise ld_focus_scratch_body_next

(* Frame preservation for the supplied source and lowered byte writes. *)
Theory gasFocusLowerDloadBytesNext
Ancestors lowerDloadSafetyKernel[qualified,ignore_grammar] venomState[qualified,ignore_grammar]
  lowerDloadPublicEffect lowerDloadExternalBoundary lowerDloadExpansionGhost
  lowerDloadSafetyAdvance lowerDloadSafetyAmbient lowerDloadSafetyAllocBounds
  lowerDloadFrontier lowerDloadSafetyRelation ctxLookupAgree o1SafeUpto

Theorem ld_focus_bytes_classified_next:
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  lo <= vs.vs_alloca_next /\ mem_inv dload_headroom_ok C vs /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ t0.vs_inst_idx = p /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  step_inst 0 C inst s = OK ss /\ LENGTH X = 2 /\ ~MEM z (fn_ir_vars fn) /\
  t1 = ((update_var z v t0) with vs_inst_idx := p+1) /\
  eval_operand dest s = SOME dw /\ eval_operand off s = SOME ow /\
  eval_operand len s = SOME nw /\ LENGTH bs = w2n nw /\
  ss = write_memory_with_expansion (w2n dw) bs s /\
  u = write_memory_with_expansion (w2n dw') bs t1 /\
  (bs = [] \/ (w2n dw = w2n dw' /\ w2n dw + LENGTH bs <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\ w2n dw = b+delta /\
      w2n dw' = c+delta /\ delta+LENGTH bs <= sz) \/
   (w2n dw = w2n dw' /\ dyn_floor C vs <= w2n dw)) ==>
  let tn' = step_taint inst s ss tn; G' = step_prov PG G inst ss;
      g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                   lf_tgt := u with vs_inst_idx := SUC t1.vs_inst_idx|> in
    G' = G /\ tn' = (tn with t_mem := tn.t_mem DIFF {w2n dw+j | j < LENGTH bs}) /\
    u.vs_inst_idx = t1.vs_inst_idx /\ SUC t1.vs_inst_idx = p + LENGTH X /\
    ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t0.vs_gas_readings /\
    ld_memory lo A tn' ss u /\ ld_nonghost tn' ss u /\
    ld_dyn_agree (dyn_floor C vs) tn'.t_mem ss.vs_memory u.vs_memory /\
    ld_ghost_ok (dyn_floor C vs) A g.lf_H G' /\
    ld_vars P A g /\ ld_maps A g /\ ld_global lo A (g::fs) /\
    FDOM A = ld_slots A (g::fs) /\ EVERY (ld_maps A) fs /\
    (!next. active_inst fn next g.lf_src ==>
       ld_sync lo P C vs stk PG G' tn' fn next g.lf_src g.lf_tgt A (g::fs) N)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule ld_sync_active >> simp[NoAsms] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[NoAsms] >> strip_tac >>
  `inst.inst_outputs = []` by
    (irule ld_dloadbytes_outputs >> simp[] >> qexists_tac `fn` >>
     metis_tac[ld_sync_fn_shape, o1_fn_shape_components,
               lowerDloadOracleCallAssemblyTheory.ld_active_inst_member]) >>
  `step_prov PG G inst ss = G` by simp[ld_empty_outputs_prov] >>
  `step_taint inst s ss tn = tn with t_mem := tn.t_mem DIFF {w2n dw+j | j < LENGTH bs}` by
    (qpat_assum `LENGTH bs = _` (fn th => rewrite_tac[th]) >>
     irule ld_dloadbytes_taint >> simp[venomStateTheory.write_memory_with_expansion_def] >>
     metis_tac[]) >>
  `lo <= dyn_floor C vs /\
   !k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
      b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by suspend "floor" >>
  `ld_memory lo A (step_taint inst s ss tn) ss u` by suspend "memory" >>
  `ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory` by
    suspend "dyn" >>
  `ld_nonghost (step_taint inst s ss tn) ss u` by
    (qpat_x_assum `ld_nonghost tn s t0` mp_tac >>
     simp[lowerDloadSafetyKernelTheory.ld_nonghost_def,
          venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def] >>
     strip_tac >> metis_tac[]) >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := u|>)` by
    (irule ld_vars_observation_cong >>
     simp[venomStateTheory.write_memory_with_expansion_def,
          venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    (rpt strip_tac >> irule ld_global_selected >>
     qexistsl_tac [`f`, `f::fs`, `lo`] >> simp[]) >>
  `f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
             lf_tv := (step_taint inst s ss tn).t_var|> =
   f with <|lf_src := ss; lf_tgt := u|>` by
    simp[lowerDloadSafetyRelationTheory.ld_frame_component_equality] >>
  `ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t0.vs_allocas /\
   ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t0.vs_alloca_next /\
   ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t0.vs_current_bb /\
   ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t0.vs_prev_bb /\
   u.vs_inst_idx = t1.vs_inst_idx /\ SUC t1.vs_inst_idx = p + LENGTH X /\
   ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t0.vs_gas_readings` by
     simp[venomStateTheory.write_memory_with_expansion_def, venomStateTheory.update_var_def] >>
  suspend "advance"
QED

Resume ld_focus_bytes_classified_next[floor]:
  `raw_reachable vs C fn inst s` by metis_tac[ld_frame_raw_reachable] >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule raw_reachable_initial_fmp >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `dload_headroom_ok C fn inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `t0.vs_alloca_next <= dyn_floor C vs` by
    (simp[ptrDisciplineTheory.dyn_floor_def] >> IF_CASES_TAC >>
     gvs[lowerDloadDefsTheory.dload_headroom_ok_def, ptrDisciplineTheory.ctx_has_dalloca_def] >>
     decide_tac) >>
  conj_tac >- decide_tac >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_slots >> strip_tac >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_maps >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all ld_alloc_frontiers >> simp[] >> decide_tac
QED

Resume ld_focus_bytes_classified_next[memory]:
  `ld_memory lo A tn s t1` by
    ((qpat_x_assum `ld_memory lo A tn s t0` mp_tac >>
     simp[lowerDloadSafetyKernelTheory.ld_memory_def, venomStateTheory.update_var_def] >> (metis_tac[lowerDloadSafetyKernelTheory.ld_memory_def, venomStateTheory.update_var_def]))) >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[lowerDloadOracleCallAssemblyTheory.ld_sync_slots, lowerDloadOracleCallAssemblyTheory.ld_sync_maps] >>
  qpat_assum `step_taint inst s ss tn = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `ss = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u = _` (fn th => pure_rewrite_tac[th]) >>
  `(!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> lo <= b /\ lo <= c) /\
   (!k k' b c sz b' c' sz'.
      FLOOKUP A k = SOME (b,c,sz) /\ FLOOKUP A k' = SOME (b',c',sz') /\
      k <> k' /\ 0 < sz /\ 0 < sz' ==>
      (b+sz <= b' \/ b'+sz' <= b) /\ (c+sz <= c' \/ c'+sz' <= c))` by
    metis_tac[ld_alloc_bounds, ld_alloc_separate] >>
  irule ld_memory_write_classified >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `dyn_floor C vs` >> asm_rewrite_tac[]) >>
  qexists_tac `tn` >> simp[]
QED

Resume ld_focus_bytes_classified_next[dyn]:
  `ld_dyn_agree (dyn_floor C vs) tn.t_mem s.vs_memory t1.vs_memory` by
    (drule ld_sync_dyn_agree >> simp[venomStateTheory.update_var_def]) >>
  qpat_assum `step_taint inst s ss tn = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `ss = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `u = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac (srw_ss()) [] >> irule ld_dyn_agree_write_classified >>
  conj_tac >- (qexistsl_tac [`A`, `lo`] >> asm_rewrite_tac[]) >>
  first_assum ACCEPT_TAC
QED

Resume ld_focus_bytes_classified_next[advance]:
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[venomInstTheory.is_terminator_def] >>
  `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
                         lf_tv := (step_taint inst s ss tn).t_var|>)` by
    (qpat_assum `f with <|lf_src := ss; lf_tgt := u; lf_H := _; lf_tv := _|> = _`
       (fn eq => pure_rewrite_tac[eq]) >> first_assum ACCEPT_TAC) >>
  `ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst ss)` by
    asm_rewrite_tac[] >>
  `f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
            lf_tgt := u with vs_inst_idx := p + LENGTH X;
            lf_H := f.lf_H; lf_tv := (step_taint inst s ss tn).t_var|> =
   f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
            lf_tgt := u with vs_inst_idx := SUC t1.vs_inst_idx|>` by
    simp[lowerDloadSafetyRelationTheory.ld_frame_component_equality] >>
  drule_all ld_nonallocating_endpoint >>
  qpat_assum `f with <|lf_src := ss with vs_inst_idx := _; lf_tgt := _;
                      lf_H := _; lf_tv := _|> = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [] o REWRITE_RULE [eq])) >>
  simp[]
QED

Finalise ld_focus_bytes_classified_next

(* Classified memory reads and comparisons through the ordinary adapter. *)
Theory lowerDloadSafetyClassifiedReadCoverage
Ancestors
  lowerDloadSafetyMloadEffects lowerDloadSafetyIloadEffects
  lowerDloadSafetyComparisonEffects lowerDloadSafetyOrdinaryCoverage
  lowerDloadOracleCallAssembly lowerDloadSafetyAssemblyPremises
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline venomExecSemantics finite_map pred_set list words

Theorem ld_sync_classified_read_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\
  (MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s) /\
  MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov PG G inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ld_sync_access_ok, ld_sync_taint_ok] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `FDOM A = ld_slots A (f::fs) /\ EVERY (ld_maps A) (f::fs)` by
    metis_tac[ld_sync_slots, ld_sync_maps] >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
     metis_tac[ld_alloc_target_no_wrap, HD]) >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  (Cases_on `inst.inst_opcode = MLOAD`
  >- (gvs[Excl "MEM"] >>
      `~in_revert_forward f.lf_fn f.lf_src` by metis_tac[MEM] >>
      drule_all ld_mload_effect >>
      disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
      qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
      simp[] >> (qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
       gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])) >>
  (Cases_on `inst.inst_opcode = ILOAD`
  >- (gvs[Excl "MEM"] >>
      `~in_revert_forward f.lf_fn f.lf_src` by metis_tac[MEM] >>
      drule_all ld_iload_effect >>
      disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
      qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
      simp[] >> (qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
       gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])) >>
  `MEM inst.inst_opcode [LT;GT;EQ]` by gvs[MEM] >>
  drule_all ld_comparison_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >> (qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
       gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])))
QED

Theorem ld_sync_classified_read_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\
  (MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s) /\
  MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] /\
  inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C' inst t = OK ts /\
  active_inst (ld_image f) ti (ts with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) (f::fs) /\
  (!j k. j < k /\ k < LENGTH (f::fs) ==>
    list_precedes (EL j (f::fs)).lf_fn.fn_name
                  (EL k (f::fs)).lf_fn.fn_name names) ==>
  ld_pair lo P names Sigma C C' vs0 (ld_image f) ti
    (ts with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ld_sync_classified_read_effect >> strip_tac >>
  irule ld_sync_ordinary_coverage >> metis_tac[]
QED

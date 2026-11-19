(* Classified LowerDload effects at one synchronized source instruction. *)
Theory lowerDloadClassifiedReadPointEffect
Ancestors
  lowerDloadSafetyMloadEffects lowerDloadSafetyIloadEffects
  lowerDloadSafetyComparisonEffects lowerDloadOracleCallAssembly
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadSafetyKernel
  ptrDiscipline venomExecSemantics finite_map pred_set list words

Theorem ld_sync_classified_read_effect_at:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> b+n <= dyn_floor C vs0) /\
  (!a b c n. FLOOKUP A a = SOME (b,c,n) ==> c+n < dimword(:256)) /\
  (MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s) /\
  MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] /\
  step_inst fuel C' inst t = OK ts ==>
  ?ss H'. step_inst fuel C inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := ts; lf_H := H';
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss ts /\
    ld_nonghost (step_taint inst s ss tn) ss ts /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H)
      inst ss = ld_erase A o_f H' /\
    (!a. a IN FRANGE H' ==> a IN FDOM A) /\
    ss.vs_allocas = s.vs_allocas /\ ts.vs_allocas = t.vs_allocas /\
    ss.vs_alloca_next = s.vs_alloca_next /\ ts.vs_alloca_next = t.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ts.vs_current_bb = t.vs_current_bb /\
    ss.vs_prev_bb = s.vs_prev_bb /\ ts.vs_prev_bb = t.vs_prev_bb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `FDOM A = ld_slots A (f::fs)` by metis_tac[ld_sync_slots] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  drule ld_sync_dyn_agree >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  let val select =
    disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
    qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
    simp[] >> qpat_assum `FDOM A = _` (fn th => rewrite_tac[GSYM th]) >>
    gen_tac >> strip_tac >> irule ld_set_prov_selected >>
    qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[]
  in
    Cases_on `inst.inst_opcode = MLOAD`
    >- (gvs[Excl "MEM"] >>
        `~in_revert_forward f.lf_fn f.lf_src` by metis_tac[MEM] >>
        drule_all ld_mload_effect >> select) >>
    Cases_on `inst.inst_opcode = ILOAD`
    >- (gvs[Excl "MEM"] >>
        `~in_revert_forward f.lf_fn f.lf_src` by metis_tac[MEM] >>
        drule_all ld_iload_effect >> select) >>
    `MEM inst.inst_opcode [LT;GT;EQ]` by gvs[MEM] >>
    drule_all ld_comparison_effect >> select
  end
QED

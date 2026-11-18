(* Pointwise simulation of scalar, masked and affine LowerDload arithmetic. *)
Theory lowerDloadArithmeticPointEffect
Ancestors
  lowerDloadSafetyScalarEffects lowerDloadSafetyAffineEffects lowerDloadSafetyShiftEffects
  lowerDloadOracleCallAssembly lowerDloadSafetyAssemblyPremises lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline
  venomExecSemantics finite_map pred_set list

Theorem ld_first_prov_range[local]:
  !ops H a. first_prov H ops = SOME a ==> a IN FRANGE H
Proof
  Induct >> simp[first_prov_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP H s` >> simp[] >> metis_tac[IN_FRANGE_FLOOKUP]
QED

Theorem ld_set_first_prov_in_domain:
  (!a. a IN FRANGE H ==> a IN FDOM A) ==>
  !a. a IN FRANGE (set_prov H outs (first_prov H ops)) ==> a IN FDOM A
Proof
  rpt strip_tac >> irule ld_set_prov_selected >>
  qexistsl_tac [`H`,`outs`,`first_prov H ops`] >>
  simp[] >> metis_tac[ld_first_prov_range]
QED

Theorem ld_sync_arithmetic_effect_at:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ taint_ok fn tn inst s /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] /\
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_shape_ok fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by
    metis_tac[ld_global_selected, MEM] >>
  `inst.inst_opcode <> INVOKE` by (fs[MEM] >> gvs[]) >>
  drule ld_sync_active >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_ghosts >> simp[Excl "MEM"] >> strip_tac >>
  drule ld_sync_memory >> strip_tac >>
  gvs[step_inst_non_invoke, Excl "MEM"] >>
  qpat_assum `f.lf_tv = tn.t_var` (assume_tac o SYM) >>
  (Cases_on `MEM inst.inst_opcode [ADD;SUB]`
  >- (drule_all ld_affine_effect >>
      disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
      qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs
        (first_prov f.lf_H inst.inst_operands)`] >>
      simp[] >> metis_tac[ld_set_first_prov_in_domain]) >>
  (Cases_on `MEM inst.inst_opcode [MUL;SHL;SHR;SAR]`
  >- (drule_all ld_masked_scalar_effect >>
      disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
      qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
      simp[] >> (gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])) >>
  `MEM inst.inst_opcode
    [Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by
    (gvs[MEM]) >>
  drule_all ld_scalar_pure_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >> (gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])))
QED

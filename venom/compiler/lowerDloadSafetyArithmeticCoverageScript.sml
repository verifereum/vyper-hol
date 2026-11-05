(* Aggregated arithmetic effects, consumed by ordinary successor coverage. *)
Theory lowerDloadSafetyArithmeticCoverage
Ancestors
  lowerDloadSafetyScalarEffects lowerDloadSafetyAffineEffects lowerDloadSafetyShiftEffects
  lowerDloadSafetyOrdinaryCoverage lowerDloadOracleCallAssembly
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyAmbient
  lowerDloadSafetyRelation lowerDloadSafetyKernel ptrDiscipline
  venomExecSemantics finite_map pred_set list

Theorem ld_first_prov_range[local]:
  !ops H a. first_prov H ops = SOME a ==> a IN FRANGE H
Proof
  Induct >> simp[first_prov_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP H s` >> simp[] >> metis_tac[IN_FRANGE_FLOOKUP]
QED

Theorem ld_set_first_prov_selected:
  (!a. a IN FRANGE H ==> a IN FDOM A) ==>
  !a. a IN FRANGE (set_prov H outs (first_prov H ops)) ==> a IN FDOM A
Proof
  rpt strip_tac >> irule ld_set_prov_selected >>
  qexistsl_tac [`H`,`outs`,`first_prov H ops`] >>
  simp[] >> metis_tac[ld_first_prov_range]
QED

Theorem ld_sync_arithmetic_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
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
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
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
      simp[] >> metis_tac[ld_set_first_prov_selected]) >>
  (Cases_on `MEM inst.inst_opcode [SHL;SHR;SAR]`
  >- (drule_all ld_shift_effect >>
      disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
      qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
      simp[] >> (gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])) >>
  `MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by
    (gvs[MEM]) >>
  drule_all ld_scalar_pure_effect >>
  disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q` strip_assume_tac) >>
  qexistsl_tac [`ss`,`set_prov f.lf_H inst.inst_outputs NONE`] >>
  simp[] >> (gen_tac >> strip_tac >> irule ld_set_prov_selected >>
       qexistsl_tac [`f.lf_H`,`inst.inst_outputs`,`NONE`] >> simp[])))
QED

Theorem ld_sync_arithmetic_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  MEM inst.inst_opcode
    [MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET;
     ADD; SUB; SHL; SHR; SAR] /\
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
  drule_all ld_sync_arithmetic_effect >> strip_tac >>
  irule ld_sync_ordinary_coverage >> metis_tac[]
QED

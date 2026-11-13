Theory lowerDloadSafetyIdentityCoverage
Ancestors
  lowerDloadSafetyOrdinaryCoverage lowerDloadOracleCallAssembly
  lowerDloadSafetyAssemblyPremises lowerDloadSafetyValues
  lowerDloadSafetyRelation lowerDloadSafetyKernel lowerDloadSafetyAmbient
  ptrDiscipline venomWf memLocDefs pointerConfinedDefs venomExecSemantics
  venomState venomInst codegenRel unitShapeDefs finite_map pred_set list

Theorem ld_identity_step[local]:
  MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst_base inst t = OK ts ==>
  ts = t /\ step_inst_base inst s = OK s
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >>
  simp[Once step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
  gvs[eval_operands_def, AllCaseEqs()] >>
  simp[Once step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED

Theorem ld_identity_ghosts[local]:
  MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
  inst.inst_outputs = [] ==>
  step_taint inst s s tn = tn /\ step_prov PG G inst s = G
Proof
  strip_tac >>
  gvs[MEM] >>
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
       written_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def,
       taint_component_equality, FLOOKUP_DEF, DRESTRICT_UNIV, SF CONJ_ss] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >> SET_TAC[]
QED

Theorem ld_sync_identity_effect:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
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
  `fn_shape_ok fn /\ fn_inst_wf fn` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `MEM inst (fn_insts fn)` by
    (drule ld_sync_source >> metis_tac[ld_active_inst_member]) >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  `inst.inst_outputs = []` by
    (fs[inst_wf_def, MEM] >> rpt strip_tac >> gvs[] >>
     Cases_on `inst.inst_outputs` >> gvs[]) >>
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
  `!v. MEM (Var v) inst.inst_operands ==>
     MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> strip_tac >> conj_tac
     >- metis_tac[ld_inst_input_ir] >>
     irule ld_ptr_use_scalar >> simp[Excl "MEM"] >> qexists_tac `inst` >>
     gvs[MEM, mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
  `~MEM inst.inst_opcode
     [ASSIGN;PHI;RET;RETFMP;DRET;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by
    gvs[MEM] >>
  `eval_operands inst.inst_operands f.lf_src =
   eval_operands inst.inst_operands f.lf_tgt` by
    (drule_all ld_vars_numeric_operands_equal >> simp[]) >>
  `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]` by simp[] >>
  drule_all ld_identity_step >> strip_tac >> gvs[Excl "MEM"] >>
  `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]` by simp[] >>
  `step_taint inst f.lf_src f.lf_src tn = tn /\
   step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q)
     (ld_erase A o_f f.lf_H) inst f.lf_src = ld_erase A o_f f.lf_H` by
    (metis_tac[ld_identity_ghosts]) >>
  qexists_tac `f.lf_H` >> simp[] >>
  `f with <|lf_src := f.lf_src; lf_tgt := f.lf_tgt;
            lf_H := f.lf_H; lf_tv := tn.t_var|> = f` by
    simp[ld_frame_component_equality] >> simp[]
QED

Theorem ld_sync_identity_coverage:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE] /\
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
  drule_all ld_sync_identity_effect >> strip_tac >>
  irule ld_sync_ordinary_coverage >> metis_tac[]
QED

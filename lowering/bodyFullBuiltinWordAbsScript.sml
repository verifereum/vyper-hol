(* Joint finite-horizon simulation of Abs. *)
Theory bodyFullBuiltinWordAbs
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame gasOutcomeFullCompose
  exprSimWordBuiltins exprSimUnopProps fragGasSeqPtr builtinProps
  fragExecMem instMemFrontier memSafeRun instIdxIndep venomExecSemantics
  ghostPcTransportPtr
  ptrDiscipline ptrSafeRun finite_map pred_set codegenRel contextCodegenRel venomState
  builtinSimple emitHelper emitHelperProps freshWrites
  exprLoweringProps exprLowering compileEnv venomInst list rich_list

val _ = Parse.hide "body";

Theorem abs_suffix_opcodes:
  !x sa op sb.
    compile_builtin_abs x sa = (op,sb) ==>
    MAP (\i. i.inst_opcode) (emitted_insts sa sb) =
      [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL; XOR]
Proof
  rpt gen_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem abs_suffix_mem_ok:
  !x sa op sb s.
    compile_builtin_abs x sa = (op,sb) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >> drule abs_suffix_opcodes >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  `EVERY (\opc. MEM opc [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL])
     (MAP (\i. i.inst_opcode) (emitted_insts sa sb))` by simp[] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem abs_inst_transition[local]:
  compile_builtin_abs x sa = (op,sb) /\
  MEM i (emitted_insts sa sb) /\
  (!a. MEM a i.inst_operands ==> op_prov G a = NONE /\ op_taint tn a = {}) /\
  step_inst_base i s = OK t /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G1 tn1. G1 = step_prov PG G i t /\ tn1 = step_taint i s t tn /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  t.vs_requests = s.vs_requests /\ t.vs_memory = s.vs_memory /\
  (!D k. ptr_inst_ok D lo 0 ctx fn G tn i (s with vs_inst_idx := k)) /\
  (!v. MEM v i.inst_outputs ==>
    op_prov G1 (Var v) = NONE /\ op_taint tn1 (Var v) = {}) /\
  (!a. op_prov G a = NONE /\ op_taint tn a = {} ==>
    op_prov G1 a = NONE /\ op_taint tn1 a = {}) /\
  (!v. ~MEM v i.inst_outputs ==>
    lookup_var v t = lookup_var v s /\
    FLOOKUP G1 v = FLOOKUP G v /\
    op_taint tn1 (Var v) = op_taint tn (Var v)) /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def,
       emitted_insts_def] >>
  rpt gen_tac >> disch_tac >> gvs[] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND] >>
  (qpat_assum `step_inst_base _ s = OK t`
    (mp_tac o PURE_REWRITE_RULE [step_inst_base_def]) >>
  pure_rewrite_tac [venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM,
    venomInstTheory.opcode_case_def] >>
  pure_rewrite_tac [exec_pure2_def, exec_pure1_def,
    venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM] >>
  simp_tac (srw_ss()) [AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  rpt (conj_tac >- simp[update_var_def]) >>
  conj_tac >-
   (simp[ptr_inst_ok_def, step_inst_non_invoke, update_var_def,
         access_ok_def, taint_ok_def, source_memory_write_ranges_def,
         source_memory_read_ranges_def, step_inst_inst_idx_indep,
         is_terminator_def, exec_result_map_def, allocas_from_def] >>
    fs[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DEF] >>
    rpt strip_tac >> gvs[] >>
    fs[allocas_from_def, FLOOKUP_DEF] >> metis_tac[]) >>
  pure_rewrite_tac [step_prov_def, out_prov_def, step_taint_def,
    venomInstTheory.instruction_accessors,
    venomInstTheory.instruction_accfupds, combinTheory.K_THM,
    venomInstTheory.opcode_case_def] >>
  simp[set_prov_def, first_prov_def, op_prov_def, set_var_taint_def,
    out_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    update_var_def] >>
  simp[op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
    lookup_var_def, mem_taint_def, step_writes_def,
    source_memory_write_ranges_def, written_taint_def, new_site_bytes_def,
    DRESTRICT_UNIV, FLOOKUP_DEF, FAPPLY_FUPDATE_THM, range_bytes_def] >>
  simp[EXTENSION] >>
  rpt conj_tac >> Cases >> simp[] >> rpt IF_CASES_TAC >> gvs[] >>
  metis_tac[])
QED


Theorem abs_suffix_ghost_success[local]:
  compile_builtin_abs x sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. !D. inst_seq_ptr D lo ctx fn PG G tn
    (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule abs_inst_transition >> disch_tac >>
  qpat_x_assum `compile_builtin_abs _ _ = _` mp_tac >>
  simp[compile_builtin_abs_def, compile_select_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, mk_inst_def] >>
  strip_tac >> gvs[] >> gvs[emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  fs[rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `step_inst_base i0 s = OK s1` >>
  `!a. MEM a i0.inst_operands ==> op_prov G a = NONE /\ op_taint tn a = {}` by
    (rw[Abbr `i0`] >> simp[op_prov_def, op_taint_def]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i0 s = OK s1`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `!D. ptr_inst_ok D lo 0 ctx fn G tn i0 s` by
    (gen_tac >> qpat_assum `!D k. ptr_inst_ok _ _ _ _ _ _ _ _ _`
      (qspecl_then [`D`, `s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
  qmatch_asmsub_abbrev_tac `op_prov G1 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn1 (Var _)` >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by metis_tac[] >>
  `allocas_from lo s1` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i1 s1 = OK s2` >>
  `!a. MEM a i1.inst_operands ==> op_prov G1 a = NONE /\ op_taint tn1 a = {}` by
    (rw[Abbr `i1`] >> simp[op_prov_def, op_taint_def]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i1 s1 = OK s2`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G2 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn2 (Var _)` >>
  `op_prov G2 x = NONE /\ op_taint tn2 x = {}` by metis_tac[] >>
  `allocas_from lo s2` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i2 s2 = OK s3` >>
  `!a. MEM a i2.inst_operands ==> op_prov G2 a = NONE /\ op_taint tn2 a = {}` by
    (rw[Abbr `i2`] >>
     simp[Abbr `i0`, Abbr `i1`]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i2 s2 = OK s3`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G3 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn3 (Var _)` >>
  `op_prov G3 x = NONE /\ op_taint tn3 x = {}` by metis_tac[] >>
  `allocas_from lo s3` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i3 s3 = OK s4` >>
  `!a. MEM a i3.inst_operands ==> op_prov G3 a = NONE /\ op_taint tn3 a = {}` by
    (rw[Abbr `i3`] >> simp[Abbr `i0`, Abbr `i1`, Abbr `i2`]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i3 s3 = OK s4`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G4 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn4 (Var _)` >>
  `op_prov G4 x = NONE /\ op_taint tn4 x = {}` by metis_tac[] >>
  `allocas_from lo s4` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i4 s4 = OK s5` >>
  `!a. MEM a i4.inst_operands ==> op_prov G4 a = NONE /\ op_taint tn4 a = {}` by
    (rw[Abbr `i4`] >> simp[Abbr `i3`]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i4 s4 = OK s5`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G5 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn5 (Var _)` >>
  `op_prov G5 x = NONE /\ op_taint tn5 x = {}` by metis_tac[] >>
  `allocas_from lo s5` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i5 s5 = OK s6` >>
  `!a. MEM a i5.inst_operands ==> op_prov G5 a = NONE /\ op_taint tn5 a = {}` by
    (rw[Abbr `i5`] >> simp[Abbr `i4`]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i5 s5 = OK s6`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G6 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn6 _` >>
  `op_prov G6 x = NONE /\ op_taint tn6 x = {}` by metis_tac[] >>
  `allocas_from lo s6` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i6 s6 = OK s7` >>
  `!a. MEM a i6.inst_operands ==> op_prov G6 a = NONE /\ op_taint tn6 a = {}` by
    (qpat_x_assum `!tn' t' s' lo' i fn ctx' PG G'. _` kall_tac >>
     qpat_assum `!v. MEM v i0.inst_outputs ==> _`
       (qspec_then `STRING #"%" (toString sa.cs_next_var)` mp_tac) >>
     simp[NoAsms, Abbr `i0`] >> strip_tac >>
     rw[Abbr `i6`] >> metis_tac[]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i6 s6 = OK s7`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G7 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn7 (Var _)` >>
  `op_prov G7 x = NONE /\ op_taint tn7 x = {}` by metis_tac[] >>
  `allocas_from lo s7` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i7 s7 = OK s8` >>
  `!a. MEM a i7.inst_operands ==> op_prov G7 a = NONE /\ op_taint tn7 a = {}` by
    (qpat_x_assum `!tn' t' s' lo' i fn ctx' PG G'. _` kall_tac >>
     qpat_assum `!v. MEM v i1.inst_outputs ==> _`
       (qspec_then `STRING #"%" (toString (sa.cs_next_var + 1))` mp_tac) >>
     simp[NoAsms, Abbr `i1`] >> strip_tac >>
     qpat_assum `!v. MEM v i6.inst_outputs ==> _`
       (qspec_then `STRING #"%" (toString (sa.cs_next_var + 5))` mp_tac) >>
     simp[NoAsms, Abbr `i6`] >> strip_tac >>
     rw[Abbr `i7`] >> metis_tac[]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i7 s7 = OK s8`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G8 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn8 (Var _)` >>
  `op_prov G8 x = NONE /\ op_taint tn8 x = {}` by metis_tac[] >>
  `allocas_from lo s8` by (fs[allocas_from_def] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base i8 s8 = OK t` >>
  `!a. MEM a i8.inst_operands ==> op_prov G8 a = NONE /\ op_taint tn8 a = {}` by
    (rw[Abbr `i8`] >> simp[Abbr `i7`]) >>
  qpat_assum `!tn' t' s' lo' i fn ctx' PG G'. _` (fn rule =>
    qpat_assum `step_inst_base i8 s8 = OK t`
      (mp_then (Pat `step_inst_base _ _ = OK _`) mp_tac rule)) >>
  simp[NoAsms] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `op_prov G9 (Var _)` >>
  qmatch_asmsub_abbrev_tac `op_taint tn9 (Var _)` >>
  qexistsl_tac [`G9`, `tn9`] >> gen_tac >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[Once inst_seq_ptr_def] >>
  qpat_assum `Abbrev (G1 = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `Abbrev (tn1 = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  simp[] >>
  `~is_terminator i1.inst_opcode` by simp[Abbr `i1`, is_terminator_def] >>
  simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  qpat_assum `Abbrev (G2 = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `Abbrev (tn2 = _)`
    (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  `~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode /\
   ~is_terminator i4.inst_opcode /\ ~is_terminator i5.inst_opcode /\
   ~is_terminator i6.inst_opcode /\ ~is_terminator i7.inst_opcode /\
   ~is_terminator i8.inst_opcode` by
    simp[Abbr `i2`, Abbr `i3`, Abbr `i4`, Abbr `i5`, Abbr `i6`,
         Abbr `i7`, Abbr `i8`, is_terminator_def] >>
  map_every (fn (gp,tp) =>
    simp[Once inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
    qpat_assum gp
      (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
    qpat_assum tp
      (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
    [(`Abbrev (G3 = _)`, `Abbrev (tn3 = _)`),
     (`Abbrev (G4 = _)`, `Abbrev (tn4 = _)`),
     (`Abbrev (G5 = _)`, `Abbrev (tn5 = _)`),
     (`Abbrev (G6 = _)`, `Abbrev (tn6 = _)`),
     (`Abbrev (G7 = _)`, `Abbrev (tn7 = _)`),
     (`Abbrev (G8 = _)`, `Abbrev (tn8 = _)`),
     (`Abbrev (G9 = _)`, `Abbrev (tn9 = _)`)] >>
  simp[inst_seq_ptr_def]
QED

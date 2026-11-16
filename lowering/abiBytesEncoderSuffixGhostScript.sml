Theory abiBytesEncoderSuffixGhost
Ancestors
  abiBytestringCode emitHelperProps exprLoweringProps fragGasSeqPtr bodyPtrDefs
  ghostPcTransportPtr instIdxIndep ptrSafeRun ptrDiscipline
  venomInstProofs venomExecSemantics venomState venomInst words list arithmetic finite_map

Theorem bytes_encoder_suffix_ghosts:
  LENGTH N = 9 /\ ALL_DISTINCT N /\
  eval_operand (Var (EL 0 N)) a = SOME (n2w n) /\
  op_taint tn (Var (EL 0 N)) = {} /\ n+32 < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo a /\
  run_inst_seq (DROP 7 (bytestring_encoder_insts id N dst src)) a = OK b ==>
  ?H tm.
    (!D k. inst_seq_ptr D lo ctx func PG G tn
      (DROP 7 (bytestring_encoder_insts id N dst src))
      (a with vs_inst_idx := k) H tm) /\
    op_taint tm (Var (EL 8 N)) = {} /\
    tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
    tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    b.vs_allocas = a.vs_allocas /\ b.vs_alloca_next = a.vs_alloca_next /\
    (!x. x NOTIN set (DROP 5 N) ==>
      lookup_var x b = lookup_var x a /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt strip_tac >>
  `?v0 v1 v2 v3 v4 v5 v6 v7 v8. N = [v0;v1;v2;v3;v4;v5;v6;v7;v8]` by
    (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  gvs[bytestring_encoder_insts_def] >>
  `step_inst_base (mk_inst (id+7) NOT [Lit 31w] [v5]) a =
    OK (update_var v5 (~31w) a)` by
    (irule step_NOT >> simp[eval_operand_def]) >>
  qabbrev_tac `a1 = update_var v5 (~31w) a` >>
  `step_inst_base (mk_inst (id+8) ADD [Var v0; Lit 31w] [v6]) a1 =
    OK (update_var v6 (n2w n + 31w) a1)` by
    (irule step_ADD >> simp[Abbr `a1`, eval_operand_def, lookup_var_update_var] >>
     gvs[eval_operand_def]) >>
  qabbrev_tac `a2 = update_var v6 (n2w n + 31w) a1` >>
  `step_inst_base (mk_inst (id+9) AND [Var v6; Var v5] [v7]) a2 =
    OK (update_var v7 ((n2w n + 31w) && ~31w) a2)` by
    (irule step_AND >> simp[Abbr `a2`, Abbr `a1`, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `a3 = update_var v7 ((n2w n + 31w) && ~31w) a2` >>
  `step_inst_base (mk_inst (id+10) ADD [Var v7; Lit 32w] [v8]) a3 =
    OK (update_var v8 (((n2w n + 31w) && ~31w) + 32w) a3)` by
    (irule step_ADD >> simp[Abbr `a3`, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `a4 = update_var v8 (((n2w n + 31w) && ~31w) + 32w) a3` >>
  `b = a4` by gvs[run_inst_seq_def] >>
  qabbrev_tac `i0 = mk_inst (id+7) NOT [Lit 31w] [v5]` >>
  qabbrev_tac `i1 = mk_inst (id+8) ADD [Var v0; Lit 31w] [v6]` >>
  qabbrev_tac `i2 = mk_inst (id+9) AND [Var v6; Var v5] [v7]` >>
  qabbrev_tac `i3 = mk_inst (id+10) ADD [Var v7; Lit 32w] [v8]` >>
  qabbrev_tac `G1 = step_prov PG G i0 a1` >>
  qabbrev_tac `G2 = step_prov PG G1 i1 a2` >>
  qabbrev_tac `G3 = step_prov PG G2 i2 a3` >>
  qabbrev_tac `G4 = step_prov PG G3 i3 a4` >>
  qabbrev_tac `tn1 = step_taint i0 a a1 tn` >>
  qabbrev_tac `tn2 = step_taint i1 a1 a2 tn1` >>
  qabbrev_tac `tn3 = step_taint i2 a2 a3 tn2` >>
  qabbrev_tac `tn4 = step_taint i3 a3 a4 tn3` >>
  `tn1 = tn with t_var := tn.t_var |+ (v5,{})` by
    (simp[Abbr `tn1`, Abbr `i0`, Abbr `a1`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DEF, op_taint_def, taint_component_equality,
       pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn2 = tn1 with t_var := tn1.t_var |+ (v6,{})` by
    (Cases_on `lookup_var v0 a1` >> simp[Abbr `tn2`, Abbr `i1`, Abbr `a2`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DEF, op_taint_def, taint_component_equality,
       pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn3 = tn2 with t_var := tn2.t_var |+ (v7,{})` by
    (Cases_on `lookup_var v6 a2` >> simp[Abbr `tn3`, Abbr `i2`, Abbr `a3`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DEF, op_taint_def, taint_component_equality,
       pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `tn4 = tn3 with t_var := tn3.t_var |+ (v8,{})` by
    (Cases_on `lookup_var v7 a3` >> simp[Abbr `tn4`, Abbr `i3`, Abbr `a4`,
       step_taint_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, out_taint_def, set_var_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, codegenRelTheory.source_memory_write_ranges_def,
       memLocDefsTheory.mem_write_ops_def, range_bytes_def, update_var_def, mk_inst_def,
       eval_operand_def, lookup_var_def, FLOOKUP_DEF, op_taint_def, taint_component_equality,
       pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  `G1 = DRESTRICT G (COMPL {v5}) /\
   G2 = set_prov G1 [v6] (FLOOKUP G v0) /\
   G3 = DRESTRICT G2 (COMPL {v7}) /\
   G4 = DRESTRICT G3 (COMPL {v8})` by
    (Cases_on `FLOOKUP G v0` >> simp[Abbr `G1`, Abbr `G2`, Abbr `G3`, Abbr `G4`,
       Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`,
       step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`G4`, `tn4`] >>
  reverse conj_tac >-
    (Cases_on `FLOOKUP G v0` >>
     simp[Abbr `a4`, Abbr `a3`, Abbr `a2`, Abbr `a1`, update_var_def,
       lookup_var_def, set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def]) >>
  `~is_terminator i0.inst_opcode /\ ~is_terminator i1.inst_opcode /\
   ~is_terminator i2.inst_opcode /\ ~is_terminator i3.inst_opcode` by
    simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def, is_terminator_def] >>
  `!D k. ptr_inst_ok D lo 0 ctx func G tn i0 (a with vs_inst_idx := k)` by
    (simp[Abbr `i0`, ptr_inst_ok_def, step_inst_non_invoke,
       step_inst_inst_idx_indep, exec_result_map_def, allocas_from_def,
       access_ok_def, taint_ok_def, mk_inst_def, op_taint_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       Abbr `a1`, update_var_def] >> gvs[allocas_from_def] >> metis_tac[]) >>
  `!D k. ptr_inst_ok D lo 0 ctx func G1 tn1 i1 (a1 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G2 tn2 i2 (a2 with vs_inst_idx := k) /\
    ptr_inst_ok D lo 0 ctx func G3 tn3 i3 (a3 with vs_inst_idx := k)` by
    (`i1.inst_opcode = ADD /\ i2.inst_opcode = AND /\ i3.inst_opcode = ADD` by
       simp[Abbr `i1`, Abbr `i2`, Abbr `i3`, mk_inst_def] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_inst_idx_indep,
       exec_result_map_def] >>
     rw[Abbr `i1`, Abbr `i2`, Abbr `i3`, access_ok_def, taint_ok_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
       mk_inst_def, op_taint_def, FLOOKUP_UPDATE, allocas_from_def,
       Abbr `a4`, Abbr `a3`, Abbr `a2`, Abbr `a1`, update_var_def] >>
     gvs[op_taint_def, allocas_from_def] >>
     (all_tac >>~- ([`_ \/ _`], Cases_on `op` >> gvs[] >>
       spose_not_then strip_assume_tac >> gvs[] >> metis_tac[])) >> metis_tac[]) >>
  qpat_x_assum `G1 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G2 = set_prov _ _ _` kall_tac >>
  qpat_x_assum `G3 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `G4 = DRESTRICT _ _` kall_tac >>
  qpat_x_assum `tn1 = tn with t_var := _` kall_tac >>
  qpat_x_assum `tn2 = tn1 with t_var := _` kall_tac >>
  qpat_x_assum `tn3 = tn2 with t_var := _` kall_tac >>
  qpat_x_assum `tn4 = tn3 with t_var := _` kall_tac >>
  gvs[] >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
    Abbr `G4`, Abbr `G3`, Abbr `G2`, Abbr `G1`,
    Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`]
QED

(* Checked scalar instructions in the storage/transient append suffix. *)
Theory stmtAppendStorageRunPtr
Ancestors
  appendStorageGhostPtr fragGasSeqPtr stmtSimAppendStorage
  typedCopyLoopHeaderPtr ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomInst venomState emitHelperProps finite_map list
  ghostPcTransportPtr exprLoweringProps compileEnv loweringStateRelDefs instSeqComposePtr instIdxIndep fragExec

Theorem append_scalar_inst_check:
  MEM opc [ADD; SLOAD; TLOAD; SSTORE; TSTORE; ASSERT] /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops outs) s = OK s' /\
  s'.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops outs) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem append_assert_abort_check:
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ASSERT [op] []) s = Abort a t ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ASSERT [op] []) s
Proof
  rpt strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke]
QED

Theorem scalar_step_old_prov:
  x <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id opc ops [out]) s') x = FLOOKUP G x
Proof
  simp[step_prov_def] >>
  Cases_on `out_prov PG G (mk_inst id opc ops [out]) s'` >>
  simp[set_prov_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem scalar_step_old_taint:
  x <> out ==>
  op_taint (step_taint (mk_inst id opc ops [out]) s s' tn) (Var x) =
  op_taint tn (Var x)
Proof
  simp[step_taint_def, set_var_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_UPDATE]
QED

Theorem scalar_storage_load_taint:
  eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if tr then TLOAD else SLOAD) [bop] [out]) s s' tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `tr` >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem scalar_add_taint:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id ADD [a;b] [out]) s s' tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem scalar_void_prov:
  step_prov PG G (mk_inst id opc ops []) s' = G
Proof
  simp[step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem scalar_storage_store_taint:
  eval_operand a s = SOME slot /\ op_taint tn v = {} /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id (if tr then TSTORE else SSTORE) [a;v] []) s s' tn =
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `tr` >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem scalar_assert_taint:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id ASSERT [a] []) s s' tn = tn
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem emit_storage_load_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] st = (lop,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn bop = {} /\ eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G' tn' /\
    op_taint tn' lop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule append_scalar_inst_check >>
     Cases_on `tr` >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`] >>
  conj_tac >- simp[inst_seq_ptr_def] >>
  `step_taint i s t tn =
    tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})` by
    (simp[Abbr `i`] >> irule scalar_storage_load_taint >> simp[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by
    (fs[not_fresh_at_def]) >>
  simp[Abbr `i`, scalar_step_old_prov, scalar_step_old_taint,
       op_taint_def, FLOOKUP_UPDATE]
QED

Theorem emit_append_arith_ptr:
  emit_op opc ops st = (rop,st') /\ (?a b. ops = [a;b]) /\
  (opc = ADD \/ opc = MUL \/
   opc = LT /\ (?v k. ops = [Var v; Lit k])) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G' tn' /\
    op_taint tn' rop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >>
     Cases_on `opc = ADD`
     >- (irule append_scalar_inst_check >> simp[] >> metis_tac[]) >>
     irule typed_copy_loop_test_check >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`] >>
  conj_tac >- simp[inst_seq_ptr_def] >>
  `step_taint i s t tn =
    tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})` by
    (simp[Abbr `i`] >> Cases_on `opc = ADD`
     >- (gvs[] >> irule scalar_add_taint >> simp[]) >>
     gvs[] >> irule (cj 2 typed_copy_loop_arith_ghost_clean) >> simp[] >> metis_tac[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by
    (fs[not_fresh_at_def]) >>
  simp[Abbr `i`, scalar_step_old_prov, scalar_step_old_taint,
       op_taint_def, FLOOKUP_UPDATE]
QED

Theorem emit_storage_store_ptr:
  emit_void (if tr then TSTORE else SSTORE) [a;v] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ op_taint tn v = {} /\
  eval_operand a s = SOME slot /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule append_scalar_inst_check >>
     Cases_on `tr` >> gvs[] >> metis_tac[]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac >- simp[Abbr `i`, scalar_void_prov] >>
  simp[Abbr `i`] >> sym_tac >> irule scalar_storage_store_taint >> simp[]
QED

Theorem emit_append_assert_ptr:
  emit_void ASSERT [a] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G tn
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule append_scalar_inst_check >> simp[] >> metis_tac[]) >>
  simp[inst_seq_ptr_def] >>
  conj_tac >- simp[Abbr `i`, scalar_void_prov] >>
  simp[Abbr `i`] >> sym_tac >> irule scalar_assert_taint >> simp[]
QED

Theorem emit_append_assert_abort_ptr:
  emit_void ASSERT [a] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = Abort ex t /\
  op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s G tn
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = Abort ex t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  simp[inst_seq_ptr_def] >> simp[Abbr `i`] >>
  irule append_assert_abort_check >> simp[] >> metis_tac[]
QED

Theorem emit_append_assert_uniform_ptr:
  emit_void ASSERT [a] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
        (s with vs_inst_idx := k) G tn
Proof
  rpt strip_tac >> irule emit_append_assert_ptr >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qexists_tac `t with vs_inst_idx := k` >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, mk_inst_def,
       is_terminator_def] >> metis_tac[]
QED

Theorem emit_append_assert_abort_uniform_ptr:
  emit_void ASSERT [a] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = Abort ex t /\
  op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
        (s with vs_inst_idx := k) G tn
Proof
  rpt strip_tac >> irule emit_append_assert_abort_ptr >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`ex`, `t with vs_inst_idx := k`] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, mk_inst_def,
       is_terminator_def] >> metis_tac[]
QED

(* Scalar successful singleton endpoints do not depend on the instruction
   cursor. This moves witnesses outside the uniform quantifier, not checks. *)
Theorem scalar_uniform_endpoints:
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK t /\
  (!k. ?G' tn'.
     inst_seq_ptr D lo ctx fn PG G tn [i]
       (s with vs_inst_idx := k) G' tn' /\ P G' tn') ==>
  ?G' tn'.
    (!k. inst_seq_ptr D lo ctx fn PG G tn [i]
       (s with vs_inst_idx := k) G' tn') /\ P G' tn'
Proof
  rpt strip_tac >>
  gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  metis_tac[]
QED

Theorem emit_append_arith_uniform_ptr:
  emit_op opc ops st = (rop,st') /\ (?a b. ops = [a;b]) /\
  (opc = ADD \/ opc = MUL \/
   opc = LT /\ (?v k. ops = [Var v; Lit k])) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' rop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts st st' = [i]` >>
  `~is_terminator i.inst_opcode` by
    (gvs[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  simp[] >> ho_match_mp_tac scalar_uniform_endpoints >>
  simp[] >> gen_tac >>
  qpat_assum `emitted_insts st st' = [i]` (SUBST1_TAC o SYM) >>
  irule emit_append_arith_ptr >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `t with vs_inst_idx := k` >>
  simp[run_inst_seq_def, step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem emit_storage_load_uniform_ptr:
  emit_op (if tr then TLOAD else SLOAD) [bop] st = (lop,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn bop = {} /\ eval_operand bop s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' lop = {} /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts st st' = [i]` >>
  `~is_terminator i.inst_opcode` by
    (Cases_on `tr` >> gvs[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  simp[] >> ho_match_mp_tac scalar_uniform_endpoints >>
  simp[] >> gen_tac >>
  qpat_assum `emitted_insts st st' = [i]` (SUBST1_TAC o SYM) >>
  irule emit_storage_load_ptr >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `t with vs_inst_idx := k` >>
  simp[run_inst_seq_def, step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem emit_storage_store_uniform_ptr:
  emit_void (if tr then TSTORE else SSTORE) [a;v] st = ((),st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ op_taint tn v = {} /\
  eval_operand a s = SOME slot /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
    (s with vs_inst_idx := k) G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  rpt strip_tac >> irule emit_storage_store_ptr >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `t with vs_inst_idx := k` >>
  drule emitted_insts_emit_void >> strip_tac >>
  Cases_on `tr` >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, mk_inst_def,
       is_terminator_def] >> metis_tac[]
QED

(* Raw load certificates keep the output provenance fact that the generic
   storage append interface does not expose. *)
Theory bodyPtrBopInLoadRun
Ancestors
  wordLoadStorePtr bodyPtrBopInLoadOutput stmtAppendStorageRunPtr fragGasSeqPtr
  emitHelperProps exprLoweringProps ptrDiscipline venomInst venomState
  venomExecSemantics finite_map list typedCopyPtr pred_set ptrSafeRun codegenRel instIdxIndep
  ghostPcTransportPtr compileEnv contextCodegenRel

Theorem emitted_load_output_prov:
  emit_op opc [a] st = (out,st') /\
  (opc = MLOAD \/ opc = ILOAD \/ opc = SLOAD \/ opc = TLOAD \/
   opc = CALLDATALOAD \/ opc = DLOAD) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts st st') s G' tn' ==>
  op_prov G' out = NONE
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, AllCaseEqs()] >>
  simp[op_prov_def] >> irule scalar_load_output_prov >> simp[]
QED

Theorem storage_load_uniform_clean:
  emit_op (if tr then TLOAD else SLOAD) [a] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ eval_operand a s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all emit_storage_load_uniform_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] mp_tac) >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule emitted_load_output_prov >>
  disch_then irule >> simp[] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >>
  gvs[] >> conj_tac >- (Cases_on `tr` >> simp[]) >>
  qpat_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

(* The counted adapter is shared by all six load opcodes. *)
Theorem emitted_load_counted_path:
  emit_op opc [a] st = (out,st') /\
  (opc = MLOAD \/ opc = ILOAD \/ opc = SLOAD \/ opc = TLOAD \/
   opc = CALLDATALOAD \/ opc = DLOAD) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts st st') s G' tn' /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH (emitted_insts st st') + s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st') /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem storage_load_path_clean:
  emit_op (if tr then TLOAD else SLOAD) [a] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ eval_operand a s = SOME slot /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all storage_load_uniform_clean >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] mp_tac) >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >>
  gvs[] >>
  drule emitted_load_counted_path >> disch_then irule >>
  simp[] >> Cases_on `tr` >> simp[]
QED

Theorem readonly_load_taint:
  (opc = MLOAD \/ opc = ILOAD \/ opc = CALLDATALOAD \/ opc = DLOAD) /\
  eval_operand a s = SOME w /\
  (opc = MLOAD \/ opc = ILOAD ==> mem_word_taint tn.t_mem (w2n w) = {}) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp ==>
  step_taint (mk_inst id opc [a] [out]) s t tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `new_site_bytes s t = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  gvs[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
      mem_taint_def, step_writes_def, source_memory_write_ranges_def,
      written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem mload_uniform_clean:
  emit_op MLOAD [Var src] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn i s` by
    (simp[Abbr `i`] >> irule ptr_inst_ok_mload >> simp[]) >>
  `step_taint i s t tn =
     tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})` by
    (simp[Abbr `i`] >> irule readonly_load_taint >>
     simp[eval_operand_def]) >>
  `~is_terminator i.inst_opcode` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`] >>
  conj_tac >-
    (gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
       exec_result_map_def] >>
     simp[Abbr `i`] >> irule ptr_inst_ok_mload >> simp[]) >>
  simp[op_prov_def, Abbr `i`, scalar_load_output_prov,
       op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by fs[not_fresh_at_def] >>
  simp[scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem mload_path_clean:
  emit_op MLOAD [Var src] st = (out,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME w /\
  mem_word_taint tn.t_mem (w2n w) = {} /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all mload_uniform_clean >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] mp_tac) >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `s.vs_inst_idx` assume_tac) >> gvs[] >>
  drule emitted_load_counted_path >> disch_then irule >> simp[]
QED

Theorem external_load_check:
  (opc = CALLDATALOAD \/ opc = DLOAD) /\ op_taint tn a = {} /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc [a] [out]) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >> metis_tac[]
QED

Theorem external_load_uniform_clean:
  emit_op opc [a] st = (out,st') /\
  (opc = CALLDATALOAD \/ opc = DLOAD) /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  op_taint tn a = {} /\ eval_operand a s = SOME w /\
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_requests = s.vs_requests /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
            (s with vs_inst_idx := k) G' tn') /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    (tn' with t_var := tn.t_var) = tn /\
    (!x. not_fresh_at st x ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qmatch_asmsub_abbrev_tac `run_inst_seq [i] s` >>
  `step_inst_base i s = OK t` by
    (fs[run_inst_seq_def, AllCaseEqs()]) >>
  `step_taint i s t tn =
     tn with t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{})` by
    (simp[Abbr `i`] >> irule readonly_load_taint >> gvs[]) >>
  `~is_terminator i.inst_opcode` by
    gvs[Abbr `i`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`] >>
  conj_tac >-
    (gen_tac >> simp[inst_seq_ptr_def, step_inst_inst_idx_indep,
       exec_result_map_def] >>
     simp[Abbr `i`] >> irule external_load_check >> simp[] >>
     qexists_tac `t with vs_inst_idx := k` >>
     simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  `FLOOKUP (step_prov PG G i t) (STRING #"%" (toString st.cs_next_var)) = NONE` by
    (simp[Abbr `i`] >> irule scalar_load_output_prov >> simp[]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by fs[not_fresh_at_def] >>
  simp[Abbr `i`, scalar_step_old_prov, op_taint_def, FLOOKUP_UPDATE]
QED

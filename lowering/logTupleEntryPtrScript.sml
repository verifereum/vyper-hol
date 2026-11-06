(* Allocation ownership and robust input transport at dynamic tuple entry. *)
Theory logTupleEntryPtr
Ancestors
  logCursorAllocPtr logAllocFramePtr logMembersInvariantPtr
  stmtSimLogTrace fragGasSeqPtr ASCIInumbers string instIdxIndep codegenRel
  stmtSimLogEncodeLayout abiEncoderComplexDynamic abiEncoderInput
  allocationPtr loweringHalt bodyPtrDefs abiBuiltinAllocation emitHelperProps exprLoweringProps
  context compileEnv venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  finite_map words list arithmetic pred_set

(* ALLOCA can taint its own newly registered bytes, never exterior bytes. *)
Theorem alloca_step_taint_outside_site:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (p,n) ==>
  !tn.
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_imm = tn.t_imm /\
    (!i. ~(p <= i /\ i < p+n) ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem <=>
       i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`,`FEMPTY`] assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`,`[]`,`FEMPTY`] assume_tac) >> simp[]
QED

(* The layout constructor needs no initialization of destination bytes when the
   processed prefix is empty.  Only source robustness and output capacity matter. *)
Theorem log_tuple_layout_entry:
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  (!q. mem_agree_outside m mem q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  mem_agree_outside writes mem' mem /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> i NOTIN writes) /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> (i IN m' <=> i IN m)) /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= cap ==>
  log_members_layout infos tys avs [] [] sb 0 0 d
    (SUM (MAP (\(_,asz,_,_). asz) infos)) cap mem' /\
  (!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q)
Proof
  strip_tac >>
  `!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q` by
    (rpt strip_tac >> irule robust_abi_encoder_input_separated_write >>
     qexistsl_tac [`m`,`m'`,`mem`,`mem'`,`writes`] >> asm_simp_tac bool_ss []) >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) mem'` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  conj_tac >- (asm_rewrite_tac[] >> irule log_members_layout_initial >> simp[] >>
    qexists_tac `abi_encoder_member_span infos` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

(* Ghost fields omitted by the semantic allocation/init boundary. *)
Theorem log_cursor_prefix_frames:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sm ++ emitted_insts sm sb) s Gf tm /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) ==>
  (!x. x <> STRING #"%" (toString sa.cs_next_var) ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!i. ~(p <= i /\ i < p+32) ==> (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, AllCaseEqs()] >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule alloca_step_old_ghost >>
  disch_then (qspecl_then [`ss'`,
    `STRING #"%" (toString sa.cs_next_var)`,`32`,`sa.cs_next_id`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`PG`,`G`,`tn`] assume_tac) >>

  gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
      exec_result_map_def] >>
  qpat_x_assum `step_inst_base _ ss' = OK t` mp_tac >>
  simp[Once step_inst_base_def, exec_write2_def, eval_operand_def,
       AllCaseEqs()] >> strip_tac >>
  `FLOOKUP ss'.vs_allocas sa.cs_next_id = SOME (p,32)` by gvs[mstore_def] >>
  `!tt. (step_taint
     (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_stor = tt.t_stor /\
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_trans = tt.t_trans /\
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_imm = tt.t_imm /\
    (!i. ~(p <= i /\ i < p+32) ==> (i IN (step_taint
       (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_mem <=> i IN tt.t_mem))` by
    (irule alloca_step_taint_outside_site >> simp[mk_inst_def] >> metis_tac[]) >>
  `?b. FLOOKUP ss'.vs_allocas sa.cs_next_id = SOME (b,32) /\
    b+32 < dimword(:256) /\
    eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) ss' = SOME (n2w b)` by
    (irule alloca_step_site >> simp[mk_inst_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  gvs[mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `step_prov PG ga _ _` >>
  qmatch_goalsub_abbrev_tac `step_taint _ ss' _ ta` >>
  simp[step_prov_def, set_prov_def, mk_inst_def, step_taint_def,
       set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, eval_operand_def, mstore_def, op_taint_def,
       w2n_n2w] >>
  gvs[FLOOKUP_DEF, DRESTRICT_UNIV, GSYM op_taint_def] >>
  qpat_x_assum `!tt. _` (qspec_then `tn` mp_tac) >>
  simp[GSYM (markerTheory.Abbrev_def)] >>
  strip_tac >> gvs[op_taint_def, FLOOKUP_DEF] >> metis_tac[]
QED

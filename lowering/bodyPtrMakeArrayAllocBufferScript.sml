(* Compiler-facing counted allocation prelude for materialized buffers. *)
Theory bodyPtrMakeArrayAllocBuffer
Ancestors
  bodyPtrMakeArrayAllocationPost exprSimAlloc fragGasPathPtr exprLoweringProps
  context compileEnv loweringStateRelDefs emitHelperProps venomInst venomState list rich_list
  fragGasSeqAbort venomExecProps venomInstProps arithmetic venomExecSemantics
  allocationPtr finite_map ptrDiscipline fragExecPtr bodyPtrDefs loweringHalt

Theorem alloc_buffer_emitted:
  compile_alloc_buffer sz sa = (buf,sm) ==>
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> simp[]
QED

Theorem literal_alloc_buffer_ptr_run:
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?u w G1 tn1.
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) u /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn /\
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    stmt_state_rel ctx func cenv cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p /\
      ptr_covers G1 tn1 p (u with vs_inst_idx := SUC s.vs_inst_idx) sz) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  drule alloc_buffer_emitted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [inst]` >>
  `step_inst_base inst s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (irule (cj 1 instruction_prefix_cursor) >>
     qexists_tac `[]` >> gvs[]) >>
  `gas_path_ptr_edge D 0 ctx func PG G tn s 0
     (step_prov PG G inst t) (step_taint inst s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
   ptr_covers (step_prov PG G inst t) (step_taint inst s t tn)
     (STRING #"%" (toString sa.cs_next_var))
     (t with vs_inst_idx := SUC s.vs_inst_idx) sz` by
    (simp[Abbr `inst`] >> irule literal_alloca_ptr_capacity >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `w`, `step_prov PG G inst t`, `step_taint inst s t tn`] >>
  conj_tac >- simp[Abbr `inst`] >> conj_tac >- simp[Abbr `inst`] >>
  gvs[] >>
  `~t.vs_halted` by
    (`step_inst 0 ctx inst s = OK t` by
       simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def] >>
     drule step_preserves_halted >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG (step_prov PG G inst t)
     (step_taint inst s t tn) (t with vs_inst_idx := SUC s.vs_inst_idx)
     0 (step_prov PG G inst t) (step_taint inst s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

Theorem literal_alloca_root_bound:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  ?b. b+n < dimword (:256) /\
    step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u = G |+ (out,(b,n)) /\
    lookup_var out u = SOME (n2w b)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[] >> qexists_tac `s.vs_alloca_next` >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  qexists_tac `site0` >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem literal_alloca_static_frame:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
  u.vs_labels = s.vs_labels /\
  u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
  u.vs_fmp = s.vs_fmp /\ u.vs_memory = s.vs_memory /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\
  (!p. p <> out ==> lookup_var p u = lookup_var p s)
Proof
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem literal_alloca_old_ghost:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_trans = tn.t_trans /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) (Var p) =
      op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      simp[FLOOKUP_UPDATE, op_taint_def]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[FLOOKUP_UPDATE, op_taint_def]
QED

Theorem alloc_buffer_root_fresh:
  ~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))
Proof
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem literal_alloca_exterior_taint:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  FLOOKUP u.vs_allocas id = SOME (b,n) /\
  tn1 = step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn ==>
  tn1.t_imm = tn.t_imm /\
  (!i. i < b \/ b+n <= i ==> (i IN tn1.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all exprSimPtrLiteralBufferTheory.literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  gvs[] >> gvs[pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >> simp[pred_setTheory.IN_UNION] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

(* Allocation/bounds prefix boundaries for self.code slicing. *)
Theory bodyPtrCodeSliceSelfPrefix
Ancestors
  bodyPtrHashBuiltinsAllocFrame exprSimPtrLiteralOps exprSimSliceMemory
  bodyPtrHashBuiltinsGhostFrame fragGasSeqPtr fragExecPtr
  bodyPtrDefs ptrDiscipline venomState venomInst venomExecSemantics
  compileEnv loweringStateRelDefs codegenRel ptrSafeRun memLocDefs
  contextCodegenRel words finite_map pred_set
  bodyPtrCodeSliceBounds exprSimCalldataSlice ghostPcTransportPtr
  loweringHalt emitHelperProps exprLoweringProps exprSimPtrLiteralChunks

Theorem self_code_data_add_frame:
  !d cenv cx es G tn s sa dst src site off v PG id.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p. not_fresh_at sa p ==> p <> dst) /\
    FLOOKUP G src = SOME site ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
        (update_var dst v s))
      (step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
        (update_var dst v s) tn) (update_var dst v s) /\
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
        (update_var dst v s))
      (step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
        (update_var dst v s) tn)
Proof
  rpt gen_tac >> strip_tac >> drule literal_add_ghost >> strip_tac >>
  simp[] >> conj_tac
  >- (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
      rpt strip_tac >> metis_tac[]) >>
  irule hash_ghost_kept_frame >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt strip_tac >> metis_tac[]
QED

Theorem self_code_data_add_checked:
  !D ctx fn PG G tn s id src dst p b sz k.
    lookup_var src s = SOME p /\ FLOOKUP G src = SOME (b,sz) /\
    op_taint tn (Var src) = {} /\ ~ctx_has_dalloca ctx /\
    b <= w2n p /\ w2n p + 32 + k <= b+sz /\
    w2n p + 32 < dimword (:256) ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var src; Lit 32w] [dst]] s
      (G |+ (dst,(b,sz))) (tn with t_var := tn.t_var |+ (dst,{})) /\
    ptr_covers (G |+ (dst,(b,sz)))
      (tn with t_var := tn.t_var |+ (dst,{})) dst
      (update_var dst (n2w (w2n p + 32)) s) k
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id ADD [Var src; Lit 32w] [dst]) s =
    OK (update_var dst (n2w (w2n p + 32)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
      eval_operand_def, GSYM word_add_n2w] >>
  drule literal_add_ghost >> strip_tac >> conj_tac
  >- simp[inst_seq_ptr_def, literal_add_ptr_inst_ok] >>
  simp[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    op_taint_def, w2n_n2w]
QED

Theorem self_code_codesize_ghost:
  !PG G tn s id dst.
    step_prov PG G (mk_inst id CODESIZE [] [dst])
      (update_var dst (n2w (LENGTH s.vs_code)) s) = G \\ dst /\
    step_taint (mk_inst id CODESIZE [] [dst]) s
      (update_var dst (n2w (LENGTH s.vs_code)) s) tn =
      tn with t_var := tn.t_var |+ (dst,{})
Proof
  rpt gen_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
    step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
    new_site_bytes_def, update_var_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, written_taint_def,
    store_taint_def, imm_taint_def, adopt_reset_def,
    taint_component_equality, FLOOKUP_DEF, DRESTRICT_DOMSUB,
    EXTENSION] >>
  conj_tac >- simp[fmap_domsub] >> metis_tac[]
QED

Theorem self_code_codesize_checked:
  !D ctx fn PG G tn s id dst.
    ~ctx_has_dalloca ctx ==>
    inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id CODESIZE [] [dst]] s
      (G \\ dst) (tn with t_var := tn.t_var |+ (dst,{}))
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id CODESIZE [] [dst]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, step_inst_non_invoke] >>
     PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
     simp[exec_read0_def, update_var_def]) >>
  `step_inst_base (mk_inst id CODESIZE [] [dst]) s =
    OK (update_var dst (n2w (LENGTH s.vs_code)) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  simp[inst_seq_ptr_def, self_code_codesize_ghost]
QED

Theorem self_code_alloca_operand_prov:
  !ctx fn cenv cx es s id n out t b PG G tn value.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    FLOOKUP t.vs_allocas id = SOME (b,n) /\
    (!x. value = Var x ==> x <> out) ==>
    op_prov (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) value =
      op_prov G value
Proof
  rpt gen_tac >> strip_tac >> drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  Cases_on `value` >> gvs[op_prov_def]
QED

Theorem self_code_size_bounds_checked:
  !D ctx fn PG G tn s a n limit sa sb sc wa wn.
    emit_op CODESIZE [] sa = (limit,sb) /\
    compile_assert_slice_bounds a n limit sb = ((),sc) /\
    eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
    op_taint tn a = {} /\ op_taint tn n = {} /\
    op_prov G a = NONE /\ op_prov G n = NONE /\
    (!z. a = Var z ==> not_fresh_at sa z) /\
    (!z. n = Var z ==> not_fresh_at sa z) /\ ~ctx_has_dalloca ctx ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[] >>
  `a <> Var (STRING #"%" (toString sa.cs_next_var)) /\
   n <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_fresh_at sb (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `?Gf tnf. inst_seq_ptr D 0 ctx fn PG
    (G \\ STRING #"%" (toString sa.cs_next_var))
    (tn with t_var := tn.t_var |+ (STRING #"%" (toString sa.cs_next_var),{}))
    (emitted_insts sb sc)
    (update_var (STRING #"%" (toString sa.cs_next_var))
      (n2w (LENGTH s.vs_code)) s with vs_inst_idx := SUC s.vs_inst_idx) Gf tnf` by
    (irule slice_bounds_checked_ptr >> simp[] >>
     goal_assum (drule_at Any) >>
     simp[eval_operand_inst_idx, GSYM DRESTRICT_DOMSUB,
       slice_bounds_scalar_operand_frame] >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       op_taint_def, op_prov_def, DOMSUB_FLOOKUP_THM, FLOOKUP_UPDATE] >>
     conj_tac >- (Cases_on `a` >> gvs[op_prov_def]) >>
     Cases_on `n` >> gvs[op_prov_def]) >>
  qexistsl_tac [`Gf`, `tnf`] >>
  simp[Once inst_seq_ptr_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst sa.cs_next_id CODESIZE []
      [STRING #"%" (toString sa.cs_next_var)]) s` by
    (mp_tac self_code_codesize_checked >> simp[inst_seq_ptr_def]) >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def,
    SRULE [mk_inst_def] self_code_codesize_ghost]
QED

Theorem self_code_out_buffer_checked:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  32 <= sz /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) ==>
  ?t G1 tn1 p q. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
    ghost_inv d cenv cx es G1 tn1 t /\
    ghost_kept cenv es sa G tn s G1 tn1 /\
    out = Var p /\ dst = Var q /\
    ptr_covers G1 tn1 p t sz /\ ptr_covers G1 tn1 q t (sz - 32)
Proof
  strip_tac >> drule slice_out_buf_decompose >> strip_tac >> gvs[] >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> gvs[emitted_insts_def]) >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `ptr_covers Ga tna ap t az` >>
  qabbrev_tac `p = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `q = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  `p <> q` by simp[Abbr `p`, Abbr `q`] >>
  gvs[Abbr `ap`, Abbr `az`] >> suspend "compose"
QED

Resume self_code_out_buffer_checked[compose]:
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w buf.buf_size)] [p]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_assum `ptr_covers Ga tna p t _`
    (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  gvs[eval_operand_def] >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  `w2n w + 32 + (buf.buf_size - 32) <= b + sz'` by decide_tac >>
  drule_all self_code_data_add_checked >>
  disch_then (qspecl_then [`D`, `fn`, `PG`, `sa.cs_next_id+1`, `q`] strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> x <> q` by
    simp[Abbr `q`, not_fresh_at_def] >>
  drule_all self_code_data_add_frame >>
  disch_then (qspecl_then [`32w`, `n2w (w2n w+32)`, `PG`, `sa.cs_next_id+1`] strip_assume_tac) >>
  drule literal_add_ghost >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`update_var q (n2w (w2n w+32)) t`, `Ga |+ (q,(b,sz'))`,
    `tna with t_var := tna.t_var |+ (q,{})`] >>
  conj_tac >- simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
    exec_pure2_def, eval_operand_def, GSYM word_add_n2w] >>
  conj_tac >- suspend "checked" >>
  conj_tac >- simp[] >>
  conj_tac >- (irule hash_ghost_kept_clean_tail >>
    qexistsl_tac [`Ga`, `tna`] >> simp[op_taint_def, FLOOKUP_UPDATE] >>
    rpt strip_tac >> metis_tac[]) >>
  reverse conj_tac >- simp[] >>
  qpat_x_assum `ptr_covers Ga tna p t _` mp_tac >>
  simp[ptr_covers_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  conj_tac >- (qpat_x_assum `op_taint tna (Var p) = {}` mp_tac >> simp[op_taint_def]) >>
  qexists_tac `w` >> qpat_x_assum `lookup_var p t = SOME w` mp_tac >> simp[lookup_var_def]
QED

Resume self_code_out_buffer_checked[checked]:
  simp[Once inst_seq_ptr_def, literal_alloca_ptr_inst_ok, Abbr `Ga`, Abbr `tna`] >>
  irule (cj 1 self_code_data_add_checked) >>
  simp[lookup_var_def] >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `0` >> gvs[lookup_var_def]
QED

Finalise self_code_out_buffer_checked

Theorem self_code_prefix_operand_frame:
  ghost_kept cenv es sa G tn s G1 tn1 /\
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!x. value = Var x ==> not_fresh_at sa x) ==>
  eval_operand value t = eval_operand value s /\
  op_prov G1 value = op_prov G value /\
  op_taint tn1 value = op_taint tn value
Proof
  strip_tac >> Cases_on `value` >>
  gvs[eval_operand_def, op_prov_def, ghost_kept_def, op_taint_def] >>
  metis_tac[]
QED

Theorem self_code_prefix_checked:
  compile_slice_out_buf sz sa = ((out,dst),sb) /\
  emit_op CODESIZE [] sb = (src_len,sc) /\
  compile_assert_slice_bounds sop lop src_len sc = ((),sd) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  32 <= sz /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  eval_operand sop s = SOME wa /\ eval_operand lop s = SOME wn /\
  op_taint tn sop = {} /\ op_taint tn lop = {} /\
  op_prov G sop = NONE /\ op_prov G lop = NONE /\
  (!x. sop = Var x ==> not_fresh_at sa x) /\
  (!x. lop = Var x ==> not_fresh_at sa x) ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sd) s Gf tnf
Proof
  strip_tac >> drule_all self_code_out_buffer_checked >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all slice_out_buf_run >> strip_tac >> gvs[] >>
  `!value. (!x. value = Var x ==> not_fresh_at sa x) ==>
    eval_operand value t = eval_operand value s /\
    op_prov G1 value = op_prov G value /\ op_taint tn1 value = op_taint tn value` by
    (gen_tac >> disch_tac >> irule self_code_prefix_operand_frame >>
     metis_tac[]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`sz`, `sa`] ci_mono_compile_slice_out_buf) >>
     simp[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    simp[not_fresh_at_def] >>
  `?Gf tnf. inst_seq_ptr D 0 ctx fn PG G1 tn1
     (emitted_insts sb sc ++ emitted_insts sc sd)
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)) Gf tnf` by
    (irule self_code_size_bounds_checked >>
     simp[eval_operand_inst_idx] >>
     goal_assum (drule_at (Pat `compile_assert_slice_bounds _ _ _ _ = _`)) >>
     simp[]) >>
  `emitted_insts sa sd = emitted_insts sa sb ++
    (emitted_insts sb sc ++ emitted_insts sc sd)` by suspend "emission" >>
  qexistsl_tac [`Gf`, `tnf`] >>
  qpat_x_assum `emitted_insts sa sd = _` (fn th => pure_once_rewrite_tac [th]) >>
  irule literal_inst_seq_ptr_append >>
  conj_tac >- suspend "nonterm" >>
  qexistsl_tac [`G1`, `tn1`, `t`] >> simp[]
QED

Resume self_code_prefix_checked[emission]:
  drule slice_out_buf_decompose >> strip_tac >>
  qpat_assum `emit_op CODESIZE [] sb = _`
    (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
  drule slice_bounds_shape >> strip_tac >>
  `emitted_insts sb sd = emitted_insts sb sc ++ emitted_insts sc sd` by
    (irule emitted_insts_append >> simp[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    simp[emitted_insts_append] >>
  `emitted_insts sa sd = emitted_insts sa sb ++ emitted_insts sb sd` by
    (irule emitted_insts_append >> simp[]) >> simp[]
QED

Resume self_code_prefix_checked[nonterm]:
  drule slice_out_buf_decompose >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `emitted_insts sa sm = emitted_insts sx sm` by
    (qpat_x_assum `sx = _` SUBST1_TAC >>
     simp[NoAsms, emitted_insts_def]) >>
  simp[mk_inst_def, is_terminator_def]
QED

Finalise self_code_prefix_checked

Theorem self_code_bounds_cursor_frame:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) /\
  (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) ==>
  ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule slice_bounds_shape >> strip_tac >> simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) (s with vs_inst_idx := k) =
    OK (t with vs_inst_idx := k)` by simp[fragExecTheory.run_inst_seq_inst_idx, instIdxIndepTheory.exec_result_map_def] >>
  `ghost_inv d cenv cx es G tn (s with vs_inst_idx := k)` by
    simp[hash_ghost_inv_inst_idx] >>
  drule_all slice_bounds_ghost_frame >>
  simp[hash_ghost_inv_inst_idx, ghost_kept_def, local_region_def, eval_operand_def,
    lookup_var_def] >> metis_tac[]
QED

Theorem self_code_size_bounds_frame:
  emit_op CODESIZE [] sa = (limit,sb) /\
  compile_assert_slice_bounds a n limit sb = ((),sc) /\
  inst_seq_ptr D 0 ctx fn PG G tn
    (emitted_insts sa sb ++ emitted_insts sb sc) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) /\
  (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) ==>
  ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  gvs[] >>
  qabbrev_tac `v = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var v (n2w (LENGTH s.vs_code)) s` >>
  `step_inst_base (mk_inst sa.cs_next_id CODESIZE [] [v]) s = OK u` by
    simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def] >>
  `run_inst_seq (emitted_insts sb sc) u = OK t` by
    gvs[Once run_inst_seq_def, mk_inst_def, is_terminator_def] >>
  `inst_seq_ptr D 0 ctx fn PG (G \\ v)
    (tn with t_var := tn.t_var |+ (v,{})) (emitted_insts sb sc)
    (u with vs_inst_idx := SUC s.vs_inst_idx) Gf tnf` by
    gvs[Once inst_seq_ptr_def, Abbr `u`, self_code_codesize_ghost] >>
  `~not_fresh_at sa v` by simp[Abbr `v`, not_fresh_at_def] >>
  drule_all slice_bounds_scalar_frame >>
  disch_then (qspec_then `n2w (LENGTH s.vs_code)` strip_assume_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by simp[not_fresh_at_def] >>
  `local_ptrs_reserved cenv sb` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sb p) /\
   (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sb p)` by
    metis_tac[] >>
  `ghost_inv d cenv cx es (G \\ v) (tn with t_var := tn.t_var |+ (v,{})) u` by
    gvs[Abbr `u`, fmap_domsub] >>
  drule_all self_code_bounds_cursor_frame >> strip_tac >>
  conj_tac >- simp[] >> suspend "kept_runtime"
QED

Resume self_code_size_bounds_frame[kept_runtime]:
  `writes_fresh sb (emitted_insts sb sc)` by
    (irule exprSimSliceBoundsTheory.slice_bounds_writes_fresh >> metis_tac[]) >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (simp[Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes u name b sz <=>
    local_region cenv es.scopes s name b sz` by
    (gvs[local_region_def, local_ptrs_reserved_def, eval_operand_def] >>
     metis_tac[]) >>
  conj_tac
  >- (irule wordArgsPtrTheory.ghost_kept_trans >>
      goal_assum (drule_at (Pat `ghost_kept _ _ sb _ _ _ _ _`)) >>
      gvs[Abbr `u`, fmap_domsub]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `t = _ with vs_vars := _` (fn th => once_rewrite_tac [th]) >>
  simp[Abbr `u`, update_var_def]
QED

Finalise self_code_size_bounds_frame

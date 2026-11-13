Theory exprSimAbiEncodeArgsTuplePost
Ancestors
  loweringStateRelDefs
  exprSimAbiEncodeArgsTupleLayout exprSimAbiEncodeArgsTupleTarget
  abiDecodeStaticProps exprSimAlloc loweringHalt emitHelper fragExec
  loweringPosts exprLoweringProps compileEnv venomState venomInst
  finite_map words allocaFootprint exprSimAbiEncodeArgsTupleProbe
  exprSimAbiEncodeArgsTupleSource vyperTypeSystem valueEncodingProps

Theorem tuple_post_mstore_fields[local,simp]:
  (mstore a w s).vs_allocas = s.vs_allocas /\
  local_region ce scopes (mstore a w s) name b len =
    local_region ce scopes s name b len
Proof
  simp[mstore_def, local_region_def, lookup_var_def]
QED

Theorem tuple_target_writes_state_rel:
  stmt_state_rel ctx fn ce cx es r /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP r.vs_allocas inst.inst_id = SOME (w2n (p:bytes32),128) /\
  w2n p + 128 < dimword (:256) /\
  (!name b len. local_region ce es.scopes r name b len ==>
     regions_disjoint (w2n p) 128 b len) ==>
  stmt_state_rel ctx fn ce cx es (tuple_target_writes p r)
Proof
  strip_tac >>
  `w2n (p + 32w) = w2n p + 32 /\
   w2n (p + 64w) = w2n p + 64 /\
   w2n (p + 96w) = w2n p + 96` by
    (rpt conj_tac >> irule w2n_add_n2w_lt >> decide_tac) >>
  simp[tuple_target_writes_def] >>
  rpt (irule literal_mstore_state_rel >> conj_tac
       >- (qexistsl_tac [`w2n p`, `inst`, `128`] >>
           gvs[mstore_def, local_region_def, lookup_var_def,
               regions_disjoint_def] >> gvs[])) >> simp[]
QED

Theorem tuple_target_return_value:
  eval_operand op r = SOME (p:bytes32) /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n p,128) /\
  sa.cs_next_id < sb.cs_next_id /\
  w2n p + 128 < dimword (:256) /\
  (!name b len. local_region ce es.scopes r name b len ==>
     regions_disjoint (w2n p) 128 b len) ==>
  expr_val_rel cx tuple_narrow
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) op
    (tuple_target_writes p r) /\
  expr_val_at ce cx tuple_narrow sa sb es
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) op
    (tuple_target_writes p r) /\
  expr_val_own ce cx tuple_narrow sa sb es
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) op
    (tuple_target_writes p r)
Proof
  strip_tac >>
  `eval_operand op (tuple_target_writes p r) = SOME p` by
    (Cases_on `op` >>
     fs[eval_operand_def, lookup_var_def] >>
     simp[tuple_target_writes_def, lookup_var_def]) >>
  `val_in_memory
     (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
     (ArrayV (TupleV [BytesV [170w]; BytesV [187w]]))
     (w2n p) (tuple_target_writes p r).vs_memory` by
    simp[tuple_target_writes_value] >>
  simp[expr_val_rel_def, expr_val_at_def, expr_val_own_def,
       cj 1 tuple_return_value_typed, tuple_narrow_def, is_word_type_def] >>
  `val_wf (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
     (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) /\
   val_footprint (TupleTV [BaseTV (BytesT (Dynamic 32)); BaseTV (BytesT (Dynamic 32))])
     (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) = 128` by
    (EVAL_TAC >> simp[wordsTheory.dimword_def]) >>
  simp[] >>
  `?aid b sz.
     FLOOKUP (tuple_target_writes p r).vs_allocas aid = SOME (b,sz) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
     b <= w2n p /\ w2n p + 128 <= b + sz /\
     (!n lb lsz. local_region ce es.scopes (tuple_target_writes p r) n lb lsz ==>
        b + sz <= lb \/ lb + lsz <= b)` by
    (qexistsl_tac [`sa.cs_next_id`, `w2n p`, `128`] >>
     simp[tuple_target_writes_def] >>
     gvs[regions_disjoint_def]) >>
  metis_tac[]
QED

Theorem tuple_target_writes_memory_only:
  r with vs_memory := (tuple_target_writes p r).vs_memory =
    tuple_target_writes p r
Proof
  simp[venom_state_component_equality] >>
  rewrite_tac[tuple_target_writes_def] >> rpt conj_tac >>
  ntac 4 (simp[Once mstore_with_memory])
QED

Theorem tuple_target_original_frame:
  stmt_state_rel ctx fn ce cx es r /\ local_ptrs_reserved ce sa /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n (p:bytes32),128) /\
  w2n p + 128 < dimword (:256) /\ r.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
  (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
     FLOOKUP r.vs_allocas aid = SOME e) /\
  (!name b len. local_region ce es.scopes r name b len ==>
     regions_disjoint (w2n p) 128 b len) ==>
  wb_frame ce es es sa s (tuple_target_writes p r)
Proof
  strip_tac >>
  `!name b len. local_region ce es.scopes r name b len <=>
      local_region ce es.scopes s name b len` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `sa` >> simp[]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      simp[tuple_target_writes_def, lookup_var_def] >>
      metis_tac[lookup_var_def])
  >- simp[tuple_target_writes_def]
  >- (rpt strip_tac >>
      `FLOOKUP r.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `regions_disjoint (w2n p) 128 off sz` by
        (`sa.cs_next_id <> aid` by decide_tac >>
         metis_tac[exprSimPrecompilesTheory.state_allocations_disjoint]) >>
      simp[tuple_target_writes_region_frame])
  >> irule exprSimPropsTheory.locals_kept_regions >> rpt strip_tac >>
     `regions_disjoint (w2n p) 128 b sz` by metis_tac[] >>
     `mem_bytes_at b sz (tuple_target_writes p r).vs_memory =
      mem_bytes_at b sz r.vs_memory` by
       (irule tuple_target_writes_region_frame >> simp[]) >> simp[]
QED

Theorem tuple_target_allocated_posts:
  compile_alloc_buffer 128 sa = (buf,sm) /\
  emit_void INVOKE [Label name; buf.buf_operand] sm = ((),sb) /\
  stmt_state_rel (tuple_target_context name ctx) fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F (tuple_target_context name ctx) fn s 0 (OK t) /\
    stmt_state_rel (tuple_target_context name ctx) fn ce cx es t /\
    wb_frame ce es es sa s t /\
    expr_val_rel cx tuple_narrow
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    expr_val_at ce cx tuple_narrow sa sb es
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    expr_val_own ce cx tuple_narrow sa sb es
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all tuple_target_allocated_path >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel (tuple_target_context name ctx) fn ce cx es
    (tuple_target_writes p r)` by
    (irule tuple_target_writes_state_rel >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w 128)]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
  `wb_frame ce es es sa s (tuple_target_writes p r)` by
    (irule tuple_target_original_frame >> metis_tac[]) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
         comp_return_def, emit_def, fresh_id_def] >> decide_tac) >>
  drule_all tuple_target_return_value >> strip_tac >>
  qexists_tac `tuple_target_writes p r with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (qpat_x_assum `gas_marked_path _ _ _ _ _ _` mp_tac >>
      pure_once_rewrite_tac[GSYM venom_state_fupdcanon] >>
      rewrite_tac[tuple_target_writes_memory_only]) >>
  first_x_assum (qspec_then `cx` strip_assume_tac) >>
  gvs[stmt_state_rel_inst_idx, wb_frame_def, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, local_region_def, lookup_var_def,
       locals_kept_def, popped_kept_def] >>
  gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
      comp_return_def, emit_def, fresh_id_def] >>
  gvs[tuple_target_writes_def] >>
  reverse conj_tac
  >- ntac 4 (simp[Once mstore_with_memory]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem tuple_target_post_interfaces:
  ce.ce_func_return_type (nsid_to_string (NONE,"f")) = tuple_narrow /\
  stmt_state_rel ctx fn ce cx es t /\
  wb_frame ce es es sa s t /\
  expr_val_rel cx tuple_narrow
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
  expr_val_at ce cx tuple_narrow sa sb es
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
  expr_val_own ce cx tuple_narrow sa sb es
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t ==>
  expr_post ctx fn ce cx tuple_call es sa sb s es
    (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
  vv_post ctx fn ce cx tuple_call es sa sb s es
    (Value (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])))
    (LocatedValue tuple_narrow (base_ptr buf)) t
Proof
  strip_tac >>
  drule exprSimAbiEncodeArgsTupleContractsTheory.tuple_post_value_type >> strip_tac >>
  gvs[expr_post_def, vv_post_def, wb_frame_def, vv_holds_def,
      vv_at_def, vv_own_def, contextTheory.base_ptr_def, expr_val_rel_def,
      expr_val_at_def, expr_val_own_def, tuple_call_def,
      vyperStateTheory.read_result_def, vyperStateTheory.return_def, tuple_narrow_def,
      is_word_type_def] >> metis_tac[]
QED

Theorem tuple_target_allocated_posts_in_context:
  lookup_function name ctx.ctx_functions = SOME (tuple_target_function name) /\
  compile_alloc_buffer 128 sa = (buf,sm) /\
  emit_void INVOKE [Label name; buf.buf_operand] sm = ((),sb) /\
  stmt_state_rel ctx fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx fn s 0 (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\
    wb_frame ce es es sa s t /\
    expr_val_rel cx tuple_narrow
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    expr_val_at ce cx tuple_narrow sa sb es
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    expr_val_own ce cx tuple_narrow sa sb es
      (ArrayV (TupleV [BytesV [170w]; BytesV [187w]])) buf.buf_operand t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all tuple_target_allocated_path_in_context >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
        comp_return_def, emit_def, fresh_id_def, cs_extends_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx fn ce cx es (tuple_target_writes p r)` by
    (irule tuple_target_writes_state_rel >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w 128)]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
  `wb_frame ce es es sa s (tuple_target_writes p r)` by
    (irule tuple_target_original_frame >> metis_tac[]) >>
  `sa.cs_next_id < sb.cs_next_id` by
    (gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
         comp_return_def, emit_def, fresh_id_def] >> decide_tac) >>
  drule_all tuple_target_return_value >> strip_tac >>
  qexists_tac `tuple_target_writes p r with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (qpat_x_assum `gas_marked_path _ _ _ _ _ _` mp_tac >>
      pure_once_rewrite_tac[GSYM venom_state_fupdcanon] >>
      rewrite_tac[tuple_target_writes_memory_only]) >>
  first_x_assum (qspec_then `cx` strip_assume_tac) >>
  gvs[stmt_state_rel_inst_idx, wb_frame_def, expr_val_rel_def,
       expr_val_at_def, expr_val_own_def, local_region_def, lookup_var_def,
       locals_kept_def, popped_kept_def] >>
  gvs[emit_void_def, emit_inst_def, comp_ignore_bind_def, comp_bind_def,
      comp_return_def, emit_def, fresh_id_def] >>
  gvs[tuple_target_writes_def] >>
  reverse conj_tac >- ntac 4 (simp[Once mstore_with_memory]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theory exprSimIfExpWidenedAggregate
Ancestors
  exprSimIfExpWidenedPosts exprSimIfExpWidenedEndpoints
  exprSimIfExpWidenedAdapter exprSimProps exprBopSimProps freshWrites
  exprSimHypsDefs exprLoweringProps compileEnv valueEncodingTyping
  valueEncodingProps fragExec context emitHelper emitHelperProps
  loweringPosts exprSimDefs exprOperandVar exprSimHyps

Theorem changed_aggregate_post_frag:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand (expr_type e) src
    (post_value_type ce e) sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < dimword (:256)) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) ==>
  frag_exec ctx sa sb
    (\s. expr_post ctx func ce cx e es origin sa s0 ee v src s)
    (\q. expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v buf.buf_operand q) R
Proof
  strip_tac >> irule frag_exec_pointwise >> qx_gen_tac `s` >> simp[] >> strip_tac >>
  drule_all ifexp_changed_aggregate_source >> strip_tac >>
  `type_memory_bytes ce (expr_type e) = type_memory_size dtv /\
   type_memory_size dtv < dimword (:256)` by metis_tac[] >>
  drule_all normalize_owned_value_framed_frag >>
  disch_then (qspec_then `R` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >>
  qx_gen_tac `q` >> strip_tac >>
  suspend "post"
QED

Resume changed_aggregate_post_frag[post]:
  markerLib.RESUME_TAC >>
  `val_wf dtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `val_footprint dtv v <= type_memory_size dtv` by
    metis_tac[val_footprint_le] >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `buf.buf_operand`, `expr_type e`, `src`,
       `post_value_type ce e`, `sm`] mp_tac) >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  `sm.cs_next_id = sa.cs_next_id + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `sa.cs_next_id < sb.cs_next_id` by decide_tac >>
  `local_ptrs_rel func ce ee.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!n b sz. local_region ce ee.scopes q n b sz ==>
    local_region ce ee.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> asm_rewrite_tac[]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `q`] >> simp[] >> metis_tac[]) >>
  `expr_val_at ce cx (expr_type e) origin sb ee v buf.buf_operand q` by
    (simp[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
     disj1_tac >>
     qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size dtv`] >>
     simp[] >> rpt strip_tac >>
     `local_region ce ee.scopes s n lb lsz` by metis_tac[] >>
     qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def]) >>
  drule normalized_expr_post_frame >> disch_then irule >>
  simp[vyperASTTheory.expr_type_def, expr_val_rel_def] >>
  suspend "frames"
QED

Resume changed_aggregate_post_frag[frames]:
  markerLib.RESUME_TAC >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
      `aid < sa.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[regions_disjoint_def] >> strip_tac >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ q.vs_memory = _`
        (qspecl_then [`off`, `len`] mp_tac) >> simp[]) >>
  irule locals_kept_regions_tail >>
  goal_assum (drule_at (Pat `locals_kept _ _ _ _`)) >>
  rpt strip_tac >>
  `local_region ce ee.scopes s n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`, `origin`, `es.scopes`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
  simp[regions_disjoint_def] >> strip_tac >>
  qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ q.vs_memory = _`
    (qspecl_then [`b`, `sz`] mp_tac) >> simp[]
QED

Finalise changed_aggregate_post_frag

Theorem compile_changed_aggregate_post_frag:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  post_value_type ce e <> expr_type e /\
  ~is_word_type (post_value_type ce e) /\
  ~is_bytestring_type (post_value_type ce e) /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  acyclic_struct_metadata ce.ce_struct_fields ==>
  ?src. unwrap_value ce vv sa = (src,sa) /\
    frag_exec ctx sa sb
      (\s. expr_post ctx func ce cx e es origin sa s0 ee v src s)
      (\q. expr_post ctx func ce cx (IfExp (expr_type e) c a b)
        es origin sb s0 ee v op q) R
Proof
  strip_tac >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rpt IF_CASES_TAC >> gvs[]) >>
  gvs[] >> drule_all compile_changed_ifexp_copy_endpoints >> strip_tac >> gvs[] >>

  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!x. src = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl_tac [`ce`, `src`, `sa`, `vv`] >>
     simp[] >> Cases_on `vv` >> gvs[vv_operand_def]) >>
  irule changed_aggregate_post_frag >>
  simp[] >> gvs[compile_store_memory_def] >>
  conj_tac
  >- fs[expr_body_pre_def, expr_sim_inv_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >>
      simp[wordsTheory.dimword_def] >> decide_tac) >>
  conj_tac >- fs[expr_body_pre_def, expr_sim_inv_def] >>
  metis_tac[]
QED

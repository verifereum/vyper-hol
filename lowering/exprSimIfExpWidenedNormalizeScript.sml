Theory exprSimIfExpWidenedNormalize
Ancestors
  exprBopSimProps exprSimIfExpWidenedAggregate exprSimIfExpWidenedAdapter
  exprSimIfExpWidenedPosts exprSimAggregateChildren exprSimProps
  exprSimIfExpWidenedBytesFrag exprSimIfExpWidenedReattach
  exprSimHyps exprSimHypsDefs exprOperandVar freshWrites
  valueEncodingTyping valueEncodingProps placeMemoryProtectedFrame
  exprLoweringProps emitHelperProps fragExec vyperState exprSimIfExp
  exprSimAlloc loweringHalt exprSimUnwrap exprSimBufferStore context emitHelper compileEnv loweringStateRelDefs loweringPosts stmtSimDefs exprSimDefs venomState

Theorem compile_bytes_ifexp_post_frag:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  is_bytestring_type (expr_type e) /\ ~is_word_type (expr_type e) /\
  ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_rel func ce es.scopes s0 /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  frag_exec ctx sa sb
    (\s. vv_post ctx func ce cx e es origin sa s0 ee tvv vv s)
    (\q. expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q) R
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by simp[] >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[bind_def] >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
   type_memory_size tvt < 2 ** 64` by metis_tac[expr_body_pre_copy_ok] >>
  `type_memory_size tvt < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all compile_ifexp_copy_parts >> strip_tac >> gvs[] >>
  `compile_store_memory ce src buf.buf_operand (expr_type e) (expr_type e) sn = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
    (drule buffer_store_memory_shape >> strip_tac >>
     fs[cs_extends_def, same_blocks_def] >>
     metis_tac[compile_alloc_buffer_extends, unwrap_value_extends,
       cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id < sm.cs_next_id /\
   sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sb.cs_next_id` by
    (qspec_then `type_memory_size tvt` (qspec_then `sa` mp_tac) ci_mono_compile_alloc_buffer >>
     qspecl_then [`ce`, `vv`, `sm`] mp_tac ci_mono_unwrap_value >>
     qspecl_then [`ce`, `src`, `buf.buf_operand`, `expr_type e`, `expr_type e`, `sn`]
       mp_tac ci_mono_compile_store_memory >>
     asm_rewrite_tac[] >> simp[ci_mono_def] >> rpt strip_tac >>
     `sm.cs_next_id = sa.cs_next_id + 1` by
       (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
        simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
        strip_tac >> gvs[]) >> decide_tac) >>
  suspend "allocation"
QED

Resume compile_bytes_ifexp_post_frag[allocation]:
  markerLib.RESUME_TAC >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  irule frag_exec_pointwise >> qx_gen_tac `s` >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  drule_all (alloc_buffer_source_frag_labels |> SPEC_ALL |>
    Q.INST [`src` |-> `Lit 0w`, `a` |-> `0w`] |> SIMP_RULE (srw_ss()) [eval_operand_def]) >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  irule frag_exec_seq >> qexistsl [`(\z. z = u)`, `sm`] >> simp[] >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sa z` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sm z` by
    metis_tac[not_fresh_at_mono] >>
  `!z. src = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule compiler_unwrap_value_var >>
     qexistsl [`ce`, `src`, `sm`, `vv`] >> simp[] >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `local_ptrs_reserved ce sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `!n b k. local_region ce ee.scopes u n b k <=>
    local_region ce ee.scopes s n b k` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >>
         conj_tac >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `ee.scopes`, `u`] >> simp[] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `ee.scopes`] >> simp[] >> metis_tac[]) >>
  `vv_post ctx func ce cx e es origin sm s0 ee tvv vv u` by
    (irule vv_post_alloc_mono_frame >> simp[] >> qexistsl [`s`, `sa`] >> simp[] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     Cases_on `vv_operand vv` >> simp[eval_operand_def] >> metis_tac[]) >>
  `val_wf tvt v` by metis_tac[cj 1 value_has_type_val_wf] >>
  irule frag_exec_seq >>
  qexistsl [`\r. expr_post ctx func ce cx e ee
    (origin with cs_next_var := sm.cs_next_var) sn u ee v src r`, `sn`] >> simp[] >>
  conj_tac
  >- (irule unwrap_value_rebased_sim >> simp[] >> metis_tac[]) >>
  irule frag_exec_pointwise >> qx_gen_tac `r` >> simp[] >> strip_tac >>
  `expr_post ctx func ce cx e es origin sn s0 ee v src r` by
    (irule vv_post_reattach_expr_post >> simp[] >>
     qexistsl [`sm`, `tvv`, `u`, `vv`] >> simp[] >> decide_tac) >>
  `lookup_var x u = SOME w` by gvs[eval_operand_def] >>
  `lookup_var x r = SOME w` by metis_tac[expr_post_rebased_lookup] >>
  `!aid entry. FLOOKUP u.vs_allocas aid = SOME entry ==>
    FLOOKUP r.vs_allocas aid = SOME entry` by fs[expr_post_def] >>
  `stmt_state_rel ctx func ce cx ee r` by fs[expr_post_def] >>
  `!n b k. local_region ce ee.scopes r n b k ==>
    local_region ce ee.scopes u n b k` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`sm`, `ee.scopes`, `r`] >> simp[] >>
     metis_tac[expr_post_rebased_lookup]) >>
  `?sw. eval_operand src r = SOME sw /\ val_in_memory tvt v (w2n sw) r.vs_memory` by
    (fs[expr_post_def, expr_val_rel_def] >> gvs[]) >>
  `compile_store_bytestring src buf.buf_operand sn = ((),sb)` by
    gvs[compile_store_memory_def] >>
  gvs[] >>
  irule bytestring_store_allocated_frag_frame >>
  goal_assum (drule_at (Pat `compile_store_bytestring _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
  qexistsl [`type_memory_size tvt`, `sa.cs_next_id`, `w`, `v`, `sw`] >> simp[eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  conj_tac >- (rpt strip_tac >>
    `local_region ce ee.scopes s name b' sz` by metis_tac[] >>
    qpat_x_assum `!nm lb len. local_region ce ee.scopes s nm lb len ==> _` drule >>
    simp[regions_disjoint_def]) >>
  conj_tac >- suspend "post" >>
  rpt strip_tac >> simp[regions_disjoint_def] >>
  `off + type_memory_size itv <= w2n w \/ w2n w + type_memory_size tvt <= off`
    suffices_by decide_tac >>
  irule compile_alloc_buffer_immutable_disjoint >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  `immutable_alloca_sep func ce cx ee u` by fs[stmt_state_rel_def] >>
  goal_assum (drule_at (Pat `immutable_alloca_sep _ _ _ _ _`)) >>
  asm_rewrite_tac[] >> goal_assum (drule_at Any) >> asm_rewrite_tac[]
QED

Resume compile_bytes_ifexp_post_frag[post]:
  markerLib.RESUME_TAC >> qx_gen_tac `q` >> strip_tac >>
  `q.vs_allocas = r.vs_allocas` by fs[venom_state_component_equality] >>
  drule_all buffer_alloc_code >> strip_tac >>
  qpat_assum `expr_post _ _ _ _ _ es origin sn s0 _ _ _ r`
    (mp_then Any mp_tac allocated_result_expr_post_frame) >>
  disch_then irule >> simp[vyperASTTheory.expr_type_def, expr_val_rel_def] >>
  conj_tac
  >- (rpt strip_tac >> irule local_region_frame >>
      conj_tac >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl [`sn`, `ee.scopes`, `q`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule local_region_frame_fwd >>
      qexistsl [`s0`, `origin`, `es.scopes`] >>
      qpat_assum `expr_post _ _ _ _ _ es origin sn s0 _ _ _ r`
        (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  `eval_operand (Var p) q = SOME w` by
    (simp[eval_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  reverse conj_tac >- (qexists `w` >> simp[]) >>
  qexistsl [`type_memory_size tvt`, `w2n w`] >>
  qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
  qexists `w` >> simp[venomInstTheory.mk_inst_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes s n lb len` by metis_tac[] >>
      qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
      simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (rpt strip_tac >>
      `old < sa.cs_next_id` by decide_tac >>
      `FLOOKUP s.vs_allocas old = SOME (off,len)` by fs[vv_post_def] >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  conj_tac >- (rpt strip_tac >>
      qpat_x_assum `!a k. _ ==> mem_bytes_at _ _ q.vs_memory = _` irule >> decide_tac) >>
  `val_footprint tvt v <= type_memory_size tvt` by metis_tac[val_footprint_le] >>
  decide_tac
QED

Finalise compile_bytes_ifexp_post_frag

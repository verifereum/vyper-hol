Theory exprSimIfExpWidenedArmCounted
Ancestors
  exprSimIfExpWidenedCounted exprSimIfExpWidenedBytesCounted
  exprSimIfExpWidenedNoCopy exprSimIfExpWidenedAdapter
  exprSimIfExpWidenedPosts exprSimTypedAlloc exprSimAlloc loweringHalt
  typedMemoryCopy valueEncodingProps valueEncodingTyping freshWrites
  venomInst venomState fragExec emitHelperProps exprSimDefs exprSimLayoutTransport exprSimHyps
  exprSimHypsDefs exprSimProps exprOperandVar exprLowering context
  compileEnv loweringPosts vyperState vyperAST vyperTypeSystem exprLoweringProps fragGasPath fragGasMode

Theorem compile_nocopy_ifexp_post_path:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  (is_word_type (expr_type e) \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  vv_post ctx func ce cx e es origin sa s0 ee tvv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unwrap_value ce vv sa = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[compile_ifexp_arm_def]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[bind_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64` by
    (drule nocopy_ifexp_physical_bound >> simp[] >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\ ~is_word_type t))` by
    (strip_tac >> irule compile_changed_physical_unwrap_shape >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
     `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
       metis_tac[post_value_type_word, post_value_type_bytestring] >>
     `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
       (spose_not_then assume_tac >>
        `post_value_type ce e = expr_type e` by
          (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
     gvs[expr_type_def] >> drule_all ifexp_intcall_copy_source >> strip_tac >>
     fs[type_widens_to_def] >> metis_tac[compatible_word_type]) >>
  drule_all unwrap_value_physical_path >> strip_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule nocopy_ifexp_post_annotated >> metis_tac[]) >>
  fs[gas_marked_path_def] >> metis_tac[cj 1 gas_path_normal]
QED

Theorem changed_aggregate_post_path:
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
      sz = type_memory_size tv) fields) /\
  expr_post ctx func ce cx e es origin sa s0 ee v src s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v buf.buf_operand q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all ifexp_changed_aggregate_source >> strip_tac >>
  `type_memory_bytes ce (expr_type e) = type_memory_size dtv /\
   type_memory_size dtv < dimword (:256)` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[compile_alloc_buffer_extends, typed_return_store_mono, ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `type_memory_bytes ce (expr_type e) < dimword (:256)` by simp[] >>
  drule_all literal_alloc_buffer_counted >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`type_memory_bytes ce (expr_type e)`, `sa`]
      mp_tac ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. src = Var x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule_all expr_val_at_bound >> simp[]) >>
  `?aid base len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (base,len) /\
    base <= w2n sw /\ w2n sw + type_memory_size stv <= base + len` by
    (fs[expr_val_own_def] >>
     qpat_x_assum `!tv. evaluate_type _ (post_value_type ce e) = SOME tv /\ _ ==> _`
       (qspec_then `stv` mp_tac) >> simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!name lb len. local_region ce ee.scopes u name lb len ==>
    w2n w + type_memory_size dtv <= lb \/ lb + len <= w2n w` by
    (rpt strip_tac >>
     qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    typed_store_counted_semantic_frame >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[mk_inst_def] >>
  disch_then (qspecl_then [`get_tenv cx`, `func`, `dtv`] mp_tac) >>
  simp[] >> (impl_tac >- (conj_tac
    >- (qpat_x_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _` mp_tac >> simp[]) >>
    rpt strip_tac >>
    qpat_x_assum `!name lb len. _` drule >> simp[arithmeticTheory.ADD_COMM])) >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  qexists_tac `t` >> simp[] >> suspend "post"
QED

Resume changed_aggregate_post_path[post]:
  markerLib.RESUME_TAC >> (
  `val_wf dtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `val_footprint dtv v <= type_memory_size dtv` by metis_tac[val_footprint_le] >>
  `sa.cs_next_id < sb.cs_next_id` by
    (drule typed_return_store_mono >> simp[ci_mono_def] >> decide_tac) >>
  `local_ptrs_rel func ce ee.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `t.vs_allocas = u.vs_allocas` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (fs[typed_copy_state_frame_def] >> metis_tac[not_fresh_at_mono]) >>
  `!n b sz. local_region ce ee.scopes t n b sz ==> local_region ce ee.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> asm_rewrite_tac[]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `t`] >> simp[]) >>
  drule allocated_result_expr_post_frame >> disch_then irule >>
  simp[vyperASTTheory.expr_type_def, expr_val_rel_def] >>
  conj_tac
  >- (rpt strip_tac >> irule local_region_frame_fwd >>
      qexistsl_tac [`s0`, `origin`, `es.scopes`] >>
      qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE[expr_post_def]) >> asm_rewrite_tac[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  `eval_operand (Var p) t = SOME w` by
    (fs[typed_copy_state_frame_def, eval_operand_def] >> metis_tac[]) >>
  reverse conj_tac >- (qexists_tac `w` >> simp[]) >>
  qexistsl_tac [`type_memory_size dtv`, `sa.cs_next_id`, `w2n w`, `w`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region ce ee.scopes u n lb len'` by
        (irule local_region_frame_fwd >> qexistsl_tac [`s`, `sa`, `ee.scopes`] >>
         asm_rewrite_tac[] >> metis_tac[]) >>
      qpat_x_assum `!name b len. _ ==> regions_disjoint _ _ _ _` drule >>
      simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  conj_tac
  >- (rpt strip_tac >>
      `old < sa.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[regions_disjoint_def, arithmeticTheory.ADD_COMM]) >>
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
  rpt strip_tac >>
  qpat_x_assum `!a n. _ ==> mem_bytes_at _ _ t.vs_memory = _`
    (qspecl_then [`off`, `len'`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM])
QED

Finalise changed_aggregate_post_path

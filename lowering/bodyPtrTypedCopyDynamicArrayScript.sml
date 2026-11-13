(* Counted recursive copying of dynamic arrays with independent layouts. *)
Theory bodyPtrTypedCopyDynamicArray
Ancestors bodyPtrTypedCopyDynamicControl bodyPtrTypedCopyArrayIteration
  bodyPtrTypedCopyArrayFrame bodyPtrTypedCopyBoundary typedDynLoopStructure
  typedArrayLoopValues typedDynStoreProps vyperTypeValues vyperTypeSystem
  typedCopyStateFrame typedCopyLayoutPtr bodyPtrPopMemoryHeader
  dynCopyPrefixPath abiStaticLoopCode abiBytestringCode
  externalReturnCopyArrays normalizationPrefixPtr valueEncodingProps

Theorem typed_copy_dynamic_array_robust:
  !ce de se dc sc.
  (!dty sty. type_rank ce.ce_struct_fields dty <
      type_rank ce.ce_struct_fields (ArrayT de (Dynamic dc)) ==>
   !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    type_memory_bytes ce sty = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce sty) /\
    ptr_covers G tn dst s (type_memory_bytes ce dty) /\
    w2n a + type_memory_bytes ce sty < dimword(:256) /\
    w2n b + type_memory_bytes ce dty < dimword(:256) /\
    (type_memory_bytes ce sty <> 0 /\ type_memory_bytes ce dty <> 0 ==>
      w2n a + type_memory_bytes ce sty <= w2n b \/
      w2n b + type_memory_bytes ce dty <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce dty) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce dty) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)) ==>
   !tenv dtv stv v dst src sa sb ctx fn D PG G tn s a b.
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). sz = type_memory_bytes ce fty /\
        (!tv. evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv)) fields) /\
    type_widens_to tenv (ArrayT se (Dynamic sc)) (ArrayT de (Dynamic dc)) /\
    evaluate_type tenv (ArrayT se (Dynamic sc)) = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic dc)) = SOME dtv /\
    type_memory_bytes ce (ArrayT se (Dynamic sc)) = type_memory_size stv /\
    type_memory_bytes ce (ArrayT de (Dynamic dc)) = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    compile_store_memory_typed ce (Var dst) (ArrayT de (Dynamic dc))
      (Var src) (ArrayT se (Dynamic sc)) sa = ((),sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (type_memory_bytes ce (ArrayT se (Dynamic sc))) /\
    ptr_covers G tn dst s (type_memory_bytes ce (ArrayT de (Dynamic dc))) /\
    w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) < dimword(:256) /\
    w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) < dimword(:256) /\
    (type_memory_bytes ce (ArrayT se (Dynamic sc)) <> 0 /\
     type_memory_bytes ce (ArrayT de (Dynamic dc)) <> 0 ==>
      w2n a + type_memory_bytes ce (ArrayT se (Dynamic sc)) <= w2n b \/
      w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc)) <= w2n a) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    cs_extends sa sb /\
    ?H tf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
      sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
      typed_copy_state_frame sa (w2n b) (type_memory_bytes ce (ArrayT de (Dynamic dc))) s sf /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes ce (ArrayT de (Dynamic dc))) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `evaluate_type _ (ArrayT se _) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  qpat_assum `evaluate_type _ (ArrayT de _) = _`
    (mp_then Any strip_assume_tac evaluate_type_ArrayT_cases) >>
  gvs[] >>
  rename1 `value_has_type (ArrayTV dt (Dynamic dc)) v` >>
  rename1 `value_has_type (ArrayTV st (Dynamic sc)) v` >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `dc < dimword(:256) /\ sc < dimword(:256)` by
    metis_tac[evaluate_type_dynarray_count_bound] >>
  `LENGTH vs <= dc /\ LENGTH vs <= sc` by
    gvs[vyperTypingTheory.value_has_type_def] >>
  `compile_copy_dynarray_typed ce (Var dst) de dc (Var src) se sa = ((),sb)` by
    metis_tac[compile_typed_dynarray_dispatch] >>
  Cases_on `type_memory_bytes ce de = type_memory_bytes ce se /\ de = se`
  >- suspend "fast" >>
  drule_all compile_copy_dynarray_loop_contains >> strip_tac >>
  `!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem` by
    metis_tac[pop_robust_dynarray_header_clean] >>
  `mload (w2n a) s = n2w (LENGTH vs)` by
    (qpat_assum `!m. mem_agree_outside tn.t_mem _ _ ==> _`
      (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac std_ss [bodyPtrDefsTheory.mem_agree_outside_def] >>
     disch_then (mp_then Any mp_tac placeDynLayoutTheory.place_dyn_memory_header) >>
     rewrite_tac[mem_word_at_eq_mload]) >>
  qpat_assum `fn_has_code sa (dyn_copy_prefix_state _ _ _ _) fn`
    (strip_assume_tac o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
  gvs[typedDynLoopCodeTheory.dyn_copy_prefix_state_fields,
      rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_assum `bb.bb_instructions = _` (assume_tac o
    REWRITE_RULE [dynCopyCodeTheory.dyn_copy_prefix_insts_def,
      abiBytestringCodeTheory.compiler_var_names_EL]) >>
  `ALL_DISTINCT (compiler_var_names sa.cs_next_var 5)` by
    simp[compiler_var_names_distinct] >>
  `!p. MEM p (compiler_var_names sa.cs_next_var 5) ==> src <> p /\ dst <> p` by
    (simp[compiler_var_names_def, listTheory.MEM_GENLIST,
       loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  qpat_x_assum `bb.bb_instructions = _` kall_tac >>
  fs[bytesCopyCodeTheory.compiler_var_names_five,
     dynCopyCodeTheory.dyn_copy_prefix_insts_def] >>
  `ptr_covers G tn src s (32 + sc * type_memory_size st) /\
   ptr_covers G tn dst s (32 + dc * type_memory_size dt)` by
    gvs[valueEncodingTheory.type_memory_size_def] >>
  `w2n a + 32 + sc * type_memory_size st < dimword(:256) /\
   w2n b + 32 + dc * type_memory_size dt < dimword(:256)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  qspecl_then [`sa.cs_next_var`,`5`]
    (assume_tac o SRULE [bytesCopyCodeTheory.compiler_var_names_five])
    compiler_var_names_distinct >>
  drule_all (PURE_REWRITE_RULE [listTheory.MEM] typed_copy_dynamic_preamble_counted) >>
  FAIL_TAC "preamble endpoint"
QED

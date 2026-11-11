(* Storage assignment preserves every slice of an old allocation at its
   state-correct execution endpoint. Normalization may change fresh scratch. *)
Theory tuplePlaceValueStorageFrame
Ancestors
  tuplePlaceStorageFrame tuplePlaceStore tuplePlaceFramedStore placeStoreStorage
  stmtSimDefs exprSimHypsDefs loweringPosts venomState stmtLowering exprLowering
  compileEnv loweringStateRelDefs vyperInterpreter vyperState vyperValue vyperTypeSystem
  fragGasPath fragGasMode arithmetic exprLoweringProps stmtSimStoreCopy

Theorem tuple_place_value_storage_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (!et n. dty <> ArrayT et (Dynamic n)) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) dty = SOME dtv ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
       w2n sw + type_memory_size stv <= s.vs_alloca_next /\
       !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
         w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
       type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!aid b len a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        b <= a /\ a+n <= b+len ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  drule_all place_store_storage_compile >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `sc`
    (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty)`
  >- suspend "normalize" >>
  gvs[] >- suspend "equal" >> suspend "bytes"
QED

Resume tuple_place_value_storage_run_frame[word]:
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `sty = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[] >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by fs[expr_val_rel_def] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
       (n2w (w2n root+delta+i)) (typed_val_to_w256 dtv v) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. typed_val_to_w256 dtv v`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> drule_all place_store_word_live_copy >>
     disch_then (qspecl_then [`get_storage cx ee tr`, `root+n2w delta`, `b`] mp_tac) >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK t)` >>
  `t.vs_memory = s.vs_memory` by
    (unabbrev_all_tac >> Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  qexists_tac `t` >> simp[] >> reverse conj_tac
  >- (unabbrev_all_tac >> Cases_on `tr` >> simp[tstore_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> simp[] >> unabbrev_all_tac >>
  simp[stmt_state_rel_inst_idx, GSYM wordsTheory.word_add_n2w,
       wordsTheory.n2w_w2n, wordsTheory.WORD_ADD_COMM]
QED

Resume tuple_place_value_storage_run_frame[equal]:
  fs[expr_val_rel_def] >>
  `val_in_memory dtv v (w2n w) s.vs_memory` by metis_tac[] >>
  `type_memory_bytes cenv dty = type_memory_size dtv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size dtv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >> fs[] >> decide_tac) >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qsuff_tac `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory`
  >- (strip_tac >> qexists_tac `t` >> gvs[]) >>
  irule tuple_place_typed_memory_suffix_frame >>
  simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`dst_op`, `op`, `w`, `v`] >>
  simp[] >> gvs[] >> metis_tac[]
QED

Resume tuple_place_value_storage_run_frame[bytes]:
  `~is_word_type sty` by
    (Cases_on `sty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT (BytesT bound)` >> Cases_on `bound` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  fs[expr_val_rel_def] >>
  `val_in_memory stv v (w2n w) s.vs_memory` by metis_tac[] >>
  drule_all place_store_bytestring_representation >>
  disch_then (qx_choose_then `src_cap` (qx_choose_then `dst_cap`
    (map_every assume_tac o CONJUNCTS))) >>
  `type_memory_bytes cenv sty = type_memory_size stv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + 32 * (1 + word_size src_cap) < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >> fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `1 + word_size src_cap <= type_slot_size dtv` by
    (fs[type_slot_size_def] >> metis_tac[exprSimHypsTheory.word_size_monotone]) >>
  `!i b. i < type_slot_size dtv /\ b < 32 /\
    ~dead_bytes (apply_writes (root+n2w delta) writes (get_storage cx ee tr))
      (w2n (root+n2w delta)) dtv (w2n (root+n2w delta)+i) b ==>
    i < 1 + word_size src_cap /\
    EL b (word_to_bytes (lookup_storage (n2w (w2n (root+n2w delta)+i))
      (apply_writes (root+n2w delta) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mem_word_at (w2n w+32*i) s.vs_memory) T)` by
    (rpt gen_tac >> disch_tac >> irule place_store_bytestring_live_copy >>
     simp[] >> qexistsl_tac [`dst_cap`, `dtv`, `v`] >>
     qpat_x_assum `i < _ /\ b < _ /\ _` mp_tac >>
     simp[AC ADD_ASSOC ADD_COMM] >> metis_tac[]) >>
  Cases_on `1 + word_size src_cap <= 1`
  >- suspend "bytes_load" >> suspend "bytes_loop"
QED

Resume tuple_place_value_storage_run_frame[bytes_loop]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  `eval_operand dst_op s = SOME (n2w (w2n root+delta))` by simp[] >>
  `1 + word_size src_cap < dimword (:256)` by (fs[] >> decide_tac) >>
  `!x. op = Var x \/ dst_op = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  qsuff_tac `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- (strip_tac >> qexists_tac `t` >> gvs[]) >>
  irule place_store_memory_leaf_run >> simp[] >> conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `(if _ then _ else _) _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  simp[] >> qexists_tac `v` >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!i b. _` (qspecl_then [`i`, `b`] mp_tac) >>
    qpat_assum `w2n (root+n2w delta) = _` (fn th =>
      simp_tac bool_ss [th, AC ADD_ASSOC ADD_COMM,
        valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
    qpat_assum `n2w (w2n root+delta) = _` (fn th =>
      simp_tac bool_ss [SRULE [AC ADD_ASSOC ADD_COMM] th]) >> metis_tac[]) >>
  metis_tac[]
QED

Resume tuple_place_value_storage_run_frame[bytes_load]:
  markerLib.RESUME_TAC >>
  `1 + word_size src_cap = 1` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  `cs_extends sa sd /\ cs_extends sd sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sd func /\ fn_has_code sd sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `store_copy_normalize _ _ = _` (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def] >>
     Cases_on `tr` >> simp[sstore_def, tstore_def]) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (w2n root+delta+i)) (mload (w2n w) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n (w:bytes32)) s`]
      (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexists_tac `v` >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!i b. _` (qspecl_then [`i`, `b`] mp_tac) >>
     qpat_assum `w2n (root+n2w delta) = _` (fn th =>
      simp_tac bool_ss [th, AC ADD_ASSOC ADD_COMM,
        valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
    qpat_assum `n2w (w2n root+delta) = _` (fn th =>
      simp_tac bool_ss [SRULE [AC ADD_ASSOC ADD_COMM] th]) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> `i = 0` by decide_tac >> gvs[]) >>
  qexists_tac `t` >> simp[] >> irule place_store_normalized_stmt_state >>
  goal_assum (drule_at Any) >> simp[] >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >> simp[] >>
  qpat_assum `n2w (w2n root+delta) = _` (fn th =>
    simp_tac bool_ss [SRULE [AC ADD_ASSOC ADD_COMM] th])
QED

Resume tuple_place_value_storage_run_frame[normalize]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type sty` by
    (spose_not_then assume_tac >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     Cases_on `sty` >> Cases_on `dty` >>
     gvs[type_widens_to_def, is_word_type_def,
         arg_type_fits_def, is_bytestring_type_def] >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT bd)) (BaseT (BytesT bd'))` >>
     Cases_on `bd` >> Cases_on `bd'` >>
     gvs[arg_type_fits_def, is_word_type_def, is_bytestring_type_def]) >>
  gvs[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (qpat_x_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> decide_tac) >>
  `cs_extends sa sm` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sc` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sc sb` by
    (Cases_on `type_memory_size dtv <= 32`
     >- (qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
         `cs_extends sc sd /\ cs_extends sd sb` by
           metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
         metis_tac[cs_extends_trans]) >>
     qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
     Cases_on `tr` >> gvs[] >>
     mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_context_helpers) >>
     mp_tac (cj 2 stmtLoweringMonoTheory.ci_mono_context_helpers) >>
     disch_then (qspecl_then [`a.buf_operand`, `dst_op`, `type_memory_size dtv DIV 32`, `sc`] mp_tac) >>
     simp[ci_mono_def] >> disch_then kall_tac >>
     disch_then (qspecl_then [`a.buf_operand`, `dst_op`, `type_memory_size dtv DIV 32`, `sc`] mp_tac) >>
     simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)` by
    (qpat_assum `!sw. eval_operand op s = SOME sw ==> _` (qspec_then `sw` mp_tac) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) tuple_place_normalize_frame >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `func`, `ee`, `stv`, `v`, `sw`, `s`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` (qx_choose_then `dw`
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "normalize_suffix"
QED

Resume tuple_place_value_storage_run_frame[normalize_suffix]:
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sc.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv sc` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `!x. a.buf_operand = Var x \/ dst_op = Var x ==> not_fresh_at sc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand dst_op u = SOME (root+n2w delta)` by
    (Cases_on `dst_op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`) place_store_storage_write_inv >>
     disch_then drule >> simp[]) >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
        (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x u) /\
    t.vs_allocas = u.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = u.vs_memory` by
    (irule tuple_place_typed_memory_suffix_frame >>
     simp[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`dst_op`, `a.buf_operand`, `dw`, `v`] >>
     gvs[] >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       gas_marked_path_then)) >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qpat_x_assum `!x. not_fresh_at sc x ==> _` drule >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  metis_tac[]
QED
Finalise tuple_place_value_storage_run_frame

(* Static exit after the actual memory preparation and first slot write. *)
Theory placeStoreStaticExit
Ancestors
  placeStoreSlots placeStaticStoreExit storageStoreFrame
  placeStaticCopyExit bytestringCopyExecution
  stmtLoweringMono vyperTypeSystem
  placeStoreStorage stmtSimDefs exprSimDefs exprSimHyps exprSimHypsDefs
  loweringPosts exprLoweringProps compileEnv loweringStateRelDefs
  stmtLowering exprLowering venomState venomExecSemantics
  vyperState vyperTypeArgFits valueEncodingTyping fragGasMode
  valueEncodingDefs valueEncodingProps vyperTyping

Theorem place_store_value_static_exit:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sa = ((),sb) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type dty) /\
  (!x. dst = Var x \/ op = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
  (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
    (!tv. evaluate_type (get_tenv cx) sty = SOME tv ==>
      type_memory_size tv < dimword (:256)) /\
    (!tv sw. evaluate_type (get_tenv cx) sty = SOME tv /\
      eval_operand op s = SOME sw ==>
      w2n sw + type_memory_size tv <= s.vs_alloca_next /\
      (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
        w2n sw + type_memory_size tv <= b \/ b + sz <= w2n sw))) /\
  (dty = sty /\ ~is_word_type sty /\ ~is_bytestring_type sty ==>
    !tv sw. evaluate_type (get_tenv cx) sty = SOME tv /\
      eval_operand op s = SOME sw ==>
      w2n sw + type_memory_size tv < dimword (:256)) /\
  (is_bytestring_type dty /\ is_bytestring_type sty ==>
    !tv. evaluate_type (get_tenv cx) sty = SOME tv ==>
      type_memory_size tv < dimword (:256)) /\
  (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
  (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
    type_alloc_ok cenv dty) /\
  stmt_state_rel ctx func cenv cx ee s /\ cx.txn.is_static /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\
    expr_exit (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  `s.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `0 < type_slot_size dtv` by metis_tac[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  drule_all place_store_storage_compile >> simp[] >>
  disch_then (qx_choose_then `src` (qx_choose_then `sc`
    (map_every assume_tac o CONJUNCTS))) >>
  Cases_on `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty)`
  >- suspend "normalize" >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type sty`
  >- suspend "bytes" >>
  gvs[] >> suspend "equal"
QED


Resume place_store_value_static_exit[word]:
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `sty = dty` by metis_tac[compileEnvTheory.type_widens_to_word] >> gvs[] >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by fs[expr_val_rel_def] >>
  drule_all storage_emit_static_path >> strip_tac >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  simp[expr_exit_def]
QED

Resume place_store_value_static_exit[equal]:
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory dtv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `w2n sw + type_memory_size dtv < dimword (:256)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `!x. op = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `w2n (root + n2w delta) + type_slot_size dtv <= dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule_all place_store_slots_static_exit >>
  disch_then (qspecl_then [`ee`, `ctx`, `RetQ`] mp_tac) >>
  strip_tac >> qexists_tac `r` >> simp[] >>
  Cases_on `r` >> gvs[stmt_exit_def, expr_exit_def]
QED

Resume place_store_value_static_exit[normalize]:
  `~is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `~is_word_type sty` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  gvs[] >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next /\
   (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by decide_tac >>
  `cs_extends sa sm` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sc` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `cs_extends sc sb` by
    (mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dst`, `dty`, `tr`, `sc`]
       mp_tac) >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  suspend "normalize_run"
QED

Resume place_store_value_static_exit[normalize_run]:
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields)` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  gvs[] >>
  `!x. op = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by decide_tac >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by decide_tac >>
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all place_store_normalize_path >>
  disch_then (qx_choose_then `u` (qx_choose_then `bw`
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "normalize_suffix"
QED

Resume place_store_value_static_exit[normalize_suffix]:
  `!x. a.buf_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def, comp_ignore_bind_def] >> strip_tac >>
     gvs[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `sm.cs_next_var <= sc.cs_next_var` by
    (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `a.buf_operand`, `dty`, `op`, `sty`, `sm`] mp_tac) >>
     simp[ci_mono_def]) >>
  `sa.cs_next_var <= sc.cs_next_var` by decide_tac >>
  `!x. a.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sc x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand dst u = SOME (root + n2w delta)` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `u.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `w2n (root + n2w delta) + type_slot_size dtv <= dimword (:256)` by
    (simp[] >> decide_tac) >>
  drule_all place_store_slots_static_exit >>
  disch_then (qspecl_then [`ee`, `ctx`, `RetQ`] strip_assume_tac) >>
  qexists_tac `r` >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  Cases_on `r` >> gvs[stmt_exit_def, expr_exit_def]
QED

Resume place_store_value_static_exit[bytes]:
  gvs[] >>
  `~is_word_type sty` by
    (Cases_on `sty` >> fs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT (BytesT bound)` >> Cases_on `bound` >>
     fs[is_bytestring_type_def, is_word_type_def]) >>
  fs[expr_val_rel_def] >>
  `?sw. eval_operand op s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[] >>
  drule_all place_store_bytestring_representation >>
  disch_then (qx_choose_then `src_cap` (qx_choose_then `dst_cap`
    (map_every assume_tac o CONJUNCTS))) >>
  suspend "bytes_code"
QED

Resume place_store_value_static_exit[bytes_code]:
  `is_abi_dynamic cenv.ce_struct_fields dty` by
    (qpat_x_assum `is_bytestring_type dty` mp_tac >>
     Cases_on `dty` >> simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count op sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  suspend "bytes_count"
QED

Resume place_store_value_static_exit[bytes_count]:
  markerLib.RESUME_TAC >> (
  `?L. mload (w2n sw) s = n2w L /\ L <= src_cap` by
    (Cases_on `v` >>
     gvs[value_has_type_def, val_in_memory_def, mem_word_at_eq_mload] >> metis_tac[]) >>
  `L + 63 < dimword (:256) /\ 1 + word_size L < dimword (:256)` by
    (fs[vfmConstantsTheory.word_size_def, wordsTheory.dimword_def] >>
     qspec_then `src_cap + 31` mp_tac
       (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     qspec_then `L + 31` mp_tac
       (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     simp[wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  suspend "bytes_count_run")
QED

Resume place_store_value_static_exit[bytes_count_run]:
  markerLib.RESUME_TAC >> (
  `ci_mono sa sm /\ (!x. cnt = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[contextTheory.compile_bytestring_word_count_def, comp_bind_def] >>
     pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     conj_tac
     >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh]) >>
  `ci_mono sm cs'` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm cs' func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  drule_all bytestring_word_count_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "bytes_suffix")
QED

Resume place_store_value_static_exit[bytes_suffix]:
  markerLib.RESUME_TAC >> (
  `t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand op t = SOME sw /\ eval_operand dst t = SOME (root + n2w delta)` by
    (Cases_on `op` >> Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `t.vs_call_ctx.cc_static` by
    (qpat_x_assum `(t with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!x. op = Var x \/ dst = Var x \/ cnt = Var x ==> not_fresh_at sm x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  Q.SUBGOAL_THEN
    `(if tr then LocTransient else LocStorage) = LocStorage \/
     (if tr then LocTransient else LocStorage) = LocTransient` assume_tac
  >- (Cases_on `tr` >> simp[]) >>
  `0 < 1 + word_size L` by simp[] >>
  drule_all place_static_copy_op_exit >>
  disch_then (qspecl_then [`ee`, `ctx`, `RetQ`] strip_assume_tac) >>
  qexists_tac `r` >> conj_tac
  >- metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  Cases_on `r` >> gvs[stmt_exit_def, expr_exit_def])
QED

Finalise place_store_value_static_exit

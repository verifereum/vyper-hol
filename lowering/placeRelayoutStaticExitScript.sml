Theory placeRelayoutStaticExit
Ancestors
  placeRelayoutContinuation placeStaticDynExit placeStaticCopyExit
  placeStoreDynPrepare placeStoreStorage exprSimHyps
  placeDestinationBounds allocaSiteResource allocLimitsProps loweringPosts
  stmtSimDefs exprSimProps venomMemDefs exprLoweringProps fragExec loweringHalt
  emitHelperProps venomInst venomState venomExecSemantics

Theorem same_layout_storage_static_exit:
  compile_assign_value cenv dst loc src F sl dty dty msz sa = ((),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\ ~is_bytestring_type dty /\
  fn_has_code sa sb func /\ msz < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  (!ew ems. info = SOME (ew,ems) ==> ew < dimword (:256) /\
     (ew = 1 ==> ems = 32) /\
     ?n. mload (w2n b) s = n2w n /\ n < dimword (:256)) /\
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `info` >- suspend "fixed" >>
  PairCases_on `x` >>
  `x0 < dimword (:256) /\ (x0 = 1 ==> x1 = 32) /\
    ?n. mload (w2n b) s = n2w n /\ n < dimword (:256)` by metis_tac[] >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `loc = LocStorage` >>
  gvs[stmtLoweringTheory.compile_assign_value_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  strip_tac >> irule place_static_dyn_storage_exit >> simp[] >>
  goal_assum (drule_at (Pat `compile_dynarray_to_storage _ _ _ _ _ _ = _`)) >>
  metis_tac[]
QED

Resume same_layout_storage_static_exit[fixed]:
  Cases_on `msz <= 32` >- suspend "word" >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `loc = LocStorage` >>
  gvs[stmtLoweringTheory.compile_assign_value_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def, contextTheory.compile_memory_to_storage_def,
    contextTheory.compile_memory_to_transient_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  irule place_static_copy_exit >> simp[] >>
  `0 < msz DIV 32 /\ msz DIV 32 < dimword (:256)` by
    (conj_tac >- simp[arithmeticTheory.X_LT_DIV] >>
     irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists_tac `msz` >> simp[arithmeticTheory.DIV_LESS_EQ]) >>
  metis_tac[]
QED

Resume same_layout_storage_static_exit[word]:
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `loc = LocStorage` >>
  gvs[stmtLoweringTheory.compile_assign_value_def,
    compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
    compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `cs_extends sa cs' /\ cs_extends cs' sb` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa cs' func` by metis_tac[fn_has_code_split] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand loaded t = SOME (mload (w2n b) s) /\
       ~t.vs_halted /\ t.vs_current_bb = cs'.cs_current_bb /\
       t.vs_inst_idx = LENGTH cs'.cs_current_insts /\
       typedMemoryCopy$typed_copy_state_frame sa 0 0 s t` by
    (drule place_store_emit_op_path >>
     disch_then (qspecl_then [`mload (w2n b) s`, `s`, `func`, `ctx`] mp_tac) >>
     impl_tac >- (simp[is_terminator_def, GSYM mk_inst_def] >>
       rpt gen_tac >> irule step_MLOAD >> simp[]) >> metis_tac[]) >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_labels = s.vs_labels /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)` by
    (fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     qpat_assum `_ with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
        vs_current_bb := _; vs_inst_idx := _|> = _`
       (mp_tac o Q.AP_TERM `\u. (u.vs_call_ctx,u.vs_labels)`) >> simp[]) >>
  `eval_operand dst t = SOME k` by
    (Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `sb.cs_current_bb = cs'.cs_current_bb` by
    metis_tac[emit_void_extends, same_blocks_def] >>
  qpat_assum `fn_has_code sa sb func` (strip_assume_tac o REWRITE_RULE [fn_has_code_def]) >>
  `?tr. isPREFIX [mk_inst cs'.cs_next_id
       (if tr then TSTORE else SSTORE) [dst;loaded] []]
       (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     simp[listTheory.DROP_APPEND, listTheory.DROP_LENGTH_TOO_LONG] >> metis_tac[]) >>
  `?z. gas_marked_path F ctx func t 0 z /\ exit_result z /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) z` by
    (irule placeStaticStoreExitTheory.place_static_store_prefix_exit >> metis_tac[]) >>
  qexists_tac `z` >> simp[] >>
  metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise same_layout_storage_static_exit

Theorem owned_target_relayout_store_static_exit:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sb = ((),sf) /\
  compile_get_target_ptr cfn cenv bt sa = ((dst,SOME loc,SOME (ValPT dty)),sb) /\
  target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  expr_val_own cenv cx sty si sj es v op s0 /\
  sj.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s0.vs_memory /\ eval_operand op s0 = SOME sw /\
  (!x. op = Var x ==> not_fresh_at sa x /\ not_fresh_at sb x) /\
  (!l. op <> Label l) /\ 0 < type_memory_size stv /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  local_ptrs_reserved cenv sb /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  cx.txn.is_static /\ (loc = LocStorage \/ loc = LocTransient) ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[target_post_def] >>
  fs[stmt_state_rel_def, compileEnvTheory.state_rel_def]
QED

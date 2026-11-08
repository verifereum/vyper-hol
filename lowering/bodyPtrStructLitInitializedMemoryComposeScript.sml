Theory bodyPtrStructLitInitializedMemoryCompose
Ancestors bodyPtrStructLitInitializedMemoryEndpoint bodyPtrStructLitMemoryCaller
  bodyPtrStructLitProducerAddress bodyPtrStructLitAddContinuation
  bodyPtrStructLitMemoryIntegration bodyPtrStructLitMemoryUnwrap
  bodyPtrStructLitRawChild bodyPtrStructLitAllocationBridge
  bodyPtrStructLitUnwrapFrame bodyPtrStructLitUnwrapSeparation
  exprSafeOperand exprLowering compileEnv loweringPosts venomState
  venomExecSemantics finite_map words bodyPtrStructLitFirstStoreEndpoint
  bodyPtrStructLitSourceEndpoint bodyPtrStructLitCountedAdd
  bodyPtrStructLitMemoryRead bodyPtrStructLitAddConsumer
  exprLoweringProps fragExec freshWrites fragGasPathPtr fragGasSeqPtr
  gasSummaryComposePtr bodyPtrDefs venomInst ptrDiscipline

(* Retain the concrete witness at the first-field compiler specialization. *)
Theorem structlit_first_memory_word_concrete_continuation:
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  emit_op ADD [buf.buf_operand; Lit (n2w 0)] sc = (dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  fn_has_code sa sd fn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  q.ptr_location = LocMemory /\ is_word_type cty /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)) /\
  vv_post ctx fn ce cx e es sb sm t ee tv (LocatedValue cty q) s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  buf.buf_operand = Var root /\ not_fresh_at sb root /\
  ptr_covers G tn root s N /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v G1 tn1 s1. read_result cx tv ee = (INL v,ee) /\
    gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee G1 tn1 (OK s1) /\
    expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
    ptr_val_ok cx cty v (Var load) G1 tn1 s1 /\
    ghost_inv d ce cx ee G1 tn1 s1 /\
    ghost_kept ce es sb G0 tn0 t G1 tn1 /\
    s1.vs_current_bb = su.cs_current_bb /\
    s1.vs_inst_idx = LENGTH su.cs_current_insts /\
    ptr_covers G1 tn1 root s1 N /\
    (!r sz. r <> load /\ ptr_covers G tn r s sz ==>
      ptr_covers G1 tn1 r s1 sz) /\
    (?r. dst = Var r /\ r <> load) /\
    (!x. x <> load ==> lookup_var x s1 = lookup_var x s) /\
    (?a. eval_operand q.ptr_operand s = SOME a /\
      s1 = (update_var load (mload (w2n a) s) s with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `fn_has_code sm su fn` by (irule structlit_first_unwrap_code >> metis_tac[]) >>
  drule_all memory_word_unwrap_code >> strip_tac >>
  `?r. dst = Var r /\ r <> load` by
    (irule emitted_operand_fresh_separation >> metis_tac[]) >>
  drule_all raw_child_unwrap_compiler_frame >> strip_tac >>
  `cty = expr_type e` by
    (drule_all bodyPtrStructLitMemoryReadTheory.vv_post_memory_word_read >> simp[]) >>
  `ptr_vv_ok cx cty tv (LocatedValue cty q) ee G tn s` by metis_tac[] >>
  `!name entry r sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var r) sz) ==> r <> load` by
      metis_tac[] >>
  `root <> load` by metis_tac[] >>
  `not_local_ptr ce ee.scopes load` by simp[] >>
  gvs[] >> drule memory_word_unwrap_ptr_concrete_continuation >> simp[] >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`v`, `G1`, `tn1`, `s1`] >> simp[]
QED

Theorem structlit_first_memory_word_initialized_consumer:
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  is_word_type (expr_type e) /\ is_word_type cty /\ is_word_type fty /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  q.ptr_location = LocMemory /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce (Var load) (Var dst) fty (lowered_value_type ce e)
    su = ((),sv) /\ fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at sb root /\ ptr_covers G0 tn0 root t N /\
  eval_operand buf.buf_operand t = SOME addrw /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addrw,N) /\
  vv_post ctx fn ce cx e es sb sc t ee tv (LocatedValue cty q) s /\
  ghost_inv d ce cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
  ptr_buf_ok ce e q.ptr_operand G s /\
  ghost_kept ce es sb G0 tn0 t G tn /\
  (?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)) /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
  ?v Gf tnf sf w. read_result cx tv ee = (INL v,ee) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    ghost_kept ce es sb G0 tn0 t Gf tnf /\
    stmt_state_rel ctx fn ce cx ee sf /\ ghost_inv d ce cx ee Gf tnf sf /\
    sf.vs_current_bb = sv.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sv.cs_current_insts /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
      w = typed_val_to_w256 tvt v) /\
    sf.vs_memory = (mstore (w2n addrw) w s).vs_memory /\
    mload (w2n addrw) sf = w /\ sf.vs_allocas = s.vs_allocas /\
    (!x. x <> dst /\ x <> load ==> lookup_var x sf = lookup_var x s) /\
    ptr_covers Gf tnf root sf N /\
    (!i. w2n addrw <= i /\ i < w2n addrw + 32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> qpat_x_assum `N = _` SUBST_ALL_TAC >>
  drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  drule_all structlit_first_child_code >> strip_tac >>
  `fn_has_code sc sm fn` by (irule structlit_first_add_code >> metis_tac[]) >>
  `not_fresh_at sc root` by
    (drule (cj 1 compile_expr_grows) >> simp[cs_extends_def] >>
     metis_tac[not_fresh_at_mono]) >>
  `emit_op ADD [Var root; Lit 0w] sc = (Var dst,sm)` by metis_tac[] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    raw_child_emitted_add_continuation >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule structlit_first_memory_word_concrete_continuation >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (qspecl_then [`env`, `PG`, `D`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "store"
QED

Resume structlit_first_memory_word_initialized_consumer[store]:
  `ptr_covers G tn root s
     (SUM (MAP (SND o SND)
       (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))))` by
    (irule vv_post_ghost_kept_covers >> metis_tac[]) >>
  `root <> dst` by (drule_all emitted_add_instruction >> simp[]) >>
  `cty = expr_type e` by (drule_all vv_post_memory_word_read >> simp[]) >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) structlit_first_word_store_endpoint >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`sz`, `a`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  suspend "resources"
QED

Resume structlit_first_memory_word_initialized_consumer[resources]:
  `w = mload (w2n a') s1` by
    (qpat_x_assum `eval_operand (Var load) s1' = SOME w` mp_tac >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `s1' = (update_var load w s1 with vs_inst_idx := SUC s1.vs_inst_idx)` by
    metis_tac[] >>
  drule_all structlit_add_load_store_state_frame >> strip_tac >>
  `lookup_var root s = SOME addrw` by
    (irule (cj 2 structlit_child_zero_add_address) >> metis_tac[]) >>
  `a = addrw` by metis_tac[optionTheory.SOME_11] >>
  `dst <> load` by (qpat_x_assum `Var dst = Var r` mp_tac >> simp[]) >>
  `lookup_var dst s1' = SOME addrw` by
    simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, WORD_ADD_0] >>
  `op_taint tn1' (Var load) = {}` by fs[ptr_val_ok_def] >>
  drule_at (Pat `tnf = step_taint _ _ _ _`) structlit_clean_word_store_resources >>
  disch_then (drule_at (Pat `sf = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`s2`, `SUC s1'.vs_inst_idx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     w = typed_val_to_w256 tvt v` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, expr_val_rel_def] >> metis_tac[optionTheory.SOME_11]) >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[gas_marked_exec_ptr_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1' tn2 (OK s2)` by
    (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _` mp_tac >>
     qpat_x_assum `gas_path_ptr _ _ _ _ _ G1 tn1 s1 _ _ _ _` mp_tac >>
     qpat_x_assum `gas_path_ptr _ _ _ _ _ G1' tn1' s1' _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0]) >>
  qexistsl [`v`, `G1'`, `tn2`, `s2`, `w`] >> simp[]
QED

Finalise structlit_first_memory_word_initialized_consumer

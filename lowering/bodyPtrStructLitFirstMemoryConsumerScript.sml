Theory bodyPtrStructLitFirstMemoryConsumer
Ancestors bodyPtrStructLitFirstStoreEndpoint bodyPtrStructLitProducerAddress
  bodyPtrStructLitAddContinuation bodyPtrStructLitRawChild
  bodyPtrStructLitAllocationBridge bodyPtrStructLitSourceEndpoint
  bodyPtrStructLitCountedAdd bodyPtrStructLitMemoryRead bodyPtrStructLitAddConsumer
  exprLoweringProps exprLowering compileEnv fragExec freshWrites
  fragGasPathPtr fragGasSeqPtr gasSummaryComposePtr bodyPtrDefs
  loweringPosts venomState venomInst finite_map words

(* Nonhalting is the projection of the successful raw-child counted path,
   via gas_path_ptr_ok_not_halted, not a consequence of vv_post alone. *)
Theorem structlit_first_memory_word_consumer:
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
  ?v Gf tnf sf. read_result cx tv ee = (INL v,ee) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    ghost_kept ce es sb G0 tn0 t Gf tnf /\
    stmt_state_rel ctx fn ce cx ee sf /\ ghost_inv d ce cx ee Gf tnf sf /\
    sf.vs_current_bb = sv.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sv.cs_current_insts
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
  drule structlit_first_memory_word_register_continuation >>
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

Resume structlit_first_memory_word_consumer[store]:
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
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SRULE[gas_marked_exec_ptr_def]) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >> simp[] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0]
QED

Finalise structlit_first_memory_word_consumer

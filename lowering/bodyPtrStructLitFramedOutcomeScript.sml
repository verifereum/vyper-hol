Theory bodyPtrStructLitFramedOutcome
Ancestors bodyPtrStructLitInitializedOutcome bodyPtrStructLitEntryStoreFrame
  bodyPtrStructLitEndpointAllocation bodyPtrStructLitUnwrapFrame
  bodyPtrStructLitMemoryUnwrap bodyPtrStructLitWordCapacity
  bodyPtrStructLitProducerAddress bodyPtrStructLitAllocationBridge
  gasSummaryComposePtr exprSimAlloc
  localPtrsProps exprLoweringProps emitHelperProps freshWrites
  loweringPosts exprSimDefs compileEnv venomState venomInst finite_map words

(* Separation is at the actual child entry, not its returned source scopes. *)
Theorem structlit_alloc_entry_local_disjoint:
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  local_ptrs_reserved ce sa /\ fn_has_code sa sb fn /\
  fn_inst_ids_distinct fn /\ stmt_state_rel ctx fn ce cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,N) /\
  local_region ce es.scopes t name lo sz ==>
  regions_disjoint b N lo sz
Proof
  strip_tac >>
  `not_local_ptr ce es.scopes root` by
    (irule structlit_alloc_buffer_nonlocal >> metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    (irule buffer_alloc_code >> metis_tac[]) >>
  drule structlit_alloc_buffer_cursor >> strip_tac >>
  gvs[stmt_state_rel_def, state_rel_def] >>
  irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at Any) >> simp[mk_inst_def] >> metis_tac[]
QED

Theorem structlit_first_memory_word_output_fresh:
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  emit_op ADD [left; Lit 0w] sc = (Var dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  is_word_type cty /\ q.ptr_location = LocMemory ==>
  ~not_fresh_at sb dst /\ ~not_fresh_at sb load
Proof
  strip_tac >> drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule_all memory_word_unwrap_code >> strip_tac >>
  gvs[cs_extends_def] >>
  conj_tac >- (simp[not_fresh_at_def] >> decide_tac) >>
  `sb.cs_next_var <= sm.cs_next_var` by decide_tac >>
  metis_tac[not_fresh_at_mono]
QED

Theorem structlit_first_memory_word_framed_outcome:
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
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn ce cx es t /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at sb root /\ ptr_covers G0 tn0 root t N /\
  eval_operand buf.buf_operand t = SOME addrw /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addrw,N) /\
  ~ctx_has_dalloca ctx /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr cx e) (es,t,G0,tn0)
    (\res ee G tn s.
      (?tv. res = INL tv /\
        vv_post ctx fn ce cx e es sb sc t ee tv (LocatedValue cty q) s /\
        s.vs_current_bb = sc.cs_current_bb /\
        s.vs_inst_idx = LENGTH sc.cs_current_insts /\
        ghost_inv d ce cx ee G tn s /\
        ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
        (!ty' op. LocatedValue cty q = StackValue ty' op /\
          ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
        (!ty' q'. LocatedValue cty q = LocatedValue ty' q' /\
          q'.ptr_location = LocMemory ==> ptr_buf_ok ce e q'.ptr_operand G s) /\
        ghost_kept ce es sb G0 tn0 t G tn) /\
      (!tv. res = INL tv ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
          (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)))
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx)) (es,t,G0,tn0)
    (\res ee Gf tnf sf. ?tv s G tn v w.
      res = INL v /\ read_result cx tv ee = (INL v,ee) /\
      ((?tv'. INL tv = INL tv' /\
        vv_post ctx fn ce cx e es sb sc t ee tv' (LocatedValue cty q) s /\
        s.vs_current_bb = sc.cs_current_bb /\
        s.vs_inst_idx = LENGTH sc.cs_current_insts /\
        ghost_inv d ce cx ee G tn s /\
        ptr_vv_ok cx (expr_type e) tv' (LocatedValue cty q) ee G tn s /\
        (!ty' op. LocatedValue cty q = StackValue ty' op /\
          ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
        (!ty' q'. LocatedValue cty q = LocatedValue ty' q' /\
          q'.ptr_location = LocMemory ==> ptr_buf_ok ce e q'.ptr_operand G s) /\
        ghost_kept ce es sb G0 tn0 t G tn) /\
      (!tv'. INL tv = INL tv' ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,ee) tv' (Type (expr_type e)) /\
          (!v. read_result cx tv' ee = (INL v,ee) ==> value_has_type tvt v))) /\
      gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
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
      (!i. w2n addrw <= i /\ i < w2n addrw + 32 ==> i NOTIN tnf.t_mem) /\
      (!x v. not_fresh_at sb x /\ lookup_var x t = SOME v ==>
        lookup_var x sf = SOME v) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
        FLOOKUP sf.vs_allocas aid = SOME b) /\
      locals_kept ce es t sf /\
      (!aid b M p len.
        FLOOKUP t.vs_allocas aid = SOME (b,M) /\ aid < sb.cs_next_id /\
        (!name lo sz. local_region ce es.scopes t name lo sz ==>
          b+M <= lo \/ lo+sz <= b) /\
        b <= p /\ p+len <= b+M /\
        (p+len <= w2n addrw \/ w2n addrw+32 <= p) ==>
        mem_bytes_at p len sf.vs_memory = mem_bytes_at p len t.vs_memory))
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    structlit_first_memory_word_initialized_outcome >>
  disch_then (drule_at (Pat `compile_expr _ _ (StructLit _ _ _) _ = _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspec_then `root` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qexistsl [`tv`, `s`, `G'`, `tn'`] >> simp[] >>
  `~not_fresh_at sb dst /\ ~not_fresh_at sb load` by
    (irule structlit_first_memory_word_output_fresh >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule structlit_entry_store_register_frame >>
    metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule structlit_entry_store_allocas_frame >>
    metis_tac[]) >>
  conj_tac >- suspend "locals" >>
  rpt strip_tac >> irule structlit_entry_store_slice_frame >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  qexistsl [`w2n addrw`, `typed_val_to_w256 tvt v`] >> simp[] >>
  metis_tac[]
QED

Resume structlit_first_memory_word_framed_outcome[locals]:
  `32 <= SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))` by
    (irule structlit_word_field_capacity >>
     goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     qexistsl [`e`, `fname`] >> simp[]) >>
  irule structlit_entry_store_locals_frame >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `_ .vs_memory = _`)) >>
  rpt strip_tac >>
  drule_all structlit_alloc_entry_local_disjoint >>
  simp[regions_disjoint_def] >> decide_tac
QED

Finalise structlit_first_memory_word_framed_outcome

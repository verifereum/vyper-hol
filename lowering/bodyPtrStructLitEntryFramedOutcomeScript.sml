Theory bodyPtrStructLitEntryFramedOutcome
Ancestors bodyPtrStructLitFramedOutcome bodyPtrStructLitRawChild
  bodyPtrStructLitAllocationBridge bodyPtrStructLitSourceEndpoint
  bodyPtrPreds bodyPtrDefs exprSimAggregateSource exprSimSource exprSimHypsDefs
  exprSimDefs exprLowering loweringPosts compileEnv venomState words
  fragGasPathPtr gasSummaryComposePtr fragGasSeqPtr

(* RawChild is not owned. This companion retains allocation witnesses which
   its earlier interface discards, on the same allocation/child execution. *)
Theorem structlit_alloc_first_child_retained_outcome:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  body_exprs_ptr_ok cx (MAP SND ((fname,e)::rest)) /\
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G0 tn0 s /\
  local_ptrs_reserved ce sa /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?u t G1 tn1 p w.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    t = u with vs_inst_idx := SUC s.vs_inst_idx /\
    buf.buf_operand = Var p /\ not_fresh_at sb p /\
    gas_path_ptr_edge D 0 ctx fn PG G0 tn0 s 0 G1 tn1 (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es G1 tn1 t /\
    ptr_covers G1 tn1 p t N /\ eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (eval_expr cx e) (es,t,G1,tn1)
      (\res ee G tn t'.
        (?tv. res = INL tv /\
          vv_post ctx fn ce cx e es sb sc t ee tv vv t' /\
          t'.vs_current_bb = sc.cs_current_bb /\
          t'.vs_inst_idx = LENGTH sc.cs_current_insts /\
          ghost_inv d ce cx ee G tn t' /\
          ptr_vv_ok cx (expr_type e) tv vv ee G tn t' /\
          (!ty' op. vv = StackValue ty' op /\ ~is_word_type (expr_type e) ==>
            ptr_buf_ok ce e op G t') /\
          (!ty' q. vv = LocatedValue ty' q /\ q.ptr_location = LocMemory ==>
            ptr_buf_ok ce e q.ptr_operand G t') /\
          ghost_kept ce es sb G1 tn1 t G tn) /\
        (!tv. res = INL tv ==>
          ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
            eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
            (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)))
      (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all structlit_first_child_judgment >>
  disch_then (qspecl_then [`fn`, `d`, `PG`] strip_assume_tac) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule structlit_first_child_code >> metis_tac[]) >>
  drule_all structlit_alloc_buffer_ptr_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all structlit_alloc_buffer_reserved >> strip_tac >>
  `~t.vs_halted` by (drule_all structlit_alloc_buffer_halted >> simp[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_ptr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre ce cx env e es` by
    (drule expr_body_pre_struct_field >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  drule_all gas_outcome_ptr_expr_runtime_typed >> strip_tac >>
  qexistsl [`G1`, `tn1`, `w`] >> gvs[]
QED

Theorem structlit_entry_first_memory_word_framed_outcome:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  body_exprs_ptr_ok cx (MAP SND ((fname,e)::rest)) /\
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G0 tn0 s /\
  local_ptrs_reserved ce sa /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  is_word_type (expr_type e) /\ is_word_type cty /\ is_word_type fty /\
  q.ptr_location = LocMemory /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce (Var load) (Var dst) fty (lowered_value_type ce e)
    su = ((),sv) ==>
  ?t G1 tn1 root addrw.
    buf.buf_operand = Var root /\ not_fresh_at sb root /\
    gas_path_ptr_edge (cx_dead cx) 0 ctx fn PG G0 tn0 s 0 G1 tn1 (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es G1 tn1 t /\
    ptr_covers G1 tn1 root t N /\ eval_operand buf.buf_operand t = SOME addrw /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addrw,N) /\
    w2n addrw+N < dimword (:256) /\
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
      (\res ee Gf tnf sf. ?tv s' G tn v w.
        res = INL v /\ read_result cx tv ee = (INL v,ee) /\
        ((?tv'. INL tv = INL tv' /\
          vv_post ctx fn ce cx e es sb sc t ee tv' (LocatedValue cty q) s' /\
          s'.vs_current_bb = sc.cs_current_bb /\
          s'.vs_inst_idx = LENGTH sc.cs_current_insts /\
          ghost_inv d ce cx ee G tn s' /\
          ptr_vv_ok cx (expr_type e) tv' (LocatedValue cty q) ee G tn s' /\
          (!ty' op. LocatedValue cty q = StackValue ty' op /\
            ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s') /\
          (!ty' q'. LocatedValue cty q = LocatedValue ty' q' /\
            q'.ptr_location = LocMemory ==> ptr_buf_ok ce e q'.ptr_operand G s') /\
          ghost_kept ce es sb G1 tn1 t G tn) /\
        (!tv'. INL tv = INL tv' ==>
          ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
            eval_result_typed (env,cx,ee) tv' (Type (expr_type e)) /\
            (!v. read_result cx tv' ee = (INL v,ee) ==> value_has_type tvt v))) /\
        gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s' 0 Gf tnf (OK sf) /\
        ghost_kept ce es sb G1 tn1 t Gf tnf /\
        stmt_state_rel ctx fn ce cx ee sf /\ ghost_inv d ce cx ee Gf tnf sf /\
        sf.vs_current_bb = sv.cs_current_bb /\
        sf.vs_inst_idx = LENGTH sv.cs_current_insts /\
        (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
          w = typed_val_to_w256 tvt v) /\
        sf.vs_memory = (mstore (w2n addrw) w s').vs_memory /\
        mload (w2n addrw) sf = w /\ sf.vs_allocas = s'.vs_allocas /\
        (!x. x <> dst /\ x <> load ==> lookup_var x sf = lookup_var x s') /\
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
  strip_tac >> drule_all structlit_alloc_first_child_retained_outcome >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn` by
    (irule structlit_first_child_code >> metis_tac[]) >>
  drule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)
    structlit_first_memory_word_framed_outcome >>
  disch_then (drule_at (Pat `compile_expr _ _ (StructLit _ _ _) _ = _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `~t.vs_halted` by
    (drule_all structlit_alloc_buffer_halted >> simp[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx fn PG G0 tn0 s 0 G1 tn1 (OK t)` by
    (irule (SRULE[] (Q.INST [`m` |-> `0`, `n` |-> `0`]
      (SPEC_ALL (cj 2 gas_path_ptr_rules)))) >>
     goal_assum (drule_at Any) >> simp[gas_path_ptr_rules]) >>
  drule_all gas_outcome_ptr_prefix >> strip_tac >>
  qexistsl [`t`, `G1`, `tn1`, `p`, `w`] >> simp[]
QED

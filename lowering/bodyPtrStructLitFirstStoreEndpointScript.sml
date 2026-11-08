Theory bodyPtrStructLitFirstStoreEndpoint
Ancestors bodyPtrStructLitProducerAddress bodyPtrStructLitFirstWordStore
  bodyPtrStructLitStoreLiveFrame bodyPtrStructLitWordCapacity
  bodyPtrDefs loweringPosts venomState venomInst ptrDiscipline
  exprLowering compileEnv finite_map words

(* All unwrap-frame premises below are simultaneous outputs of the actual
   memory/nonmemory register continuations, not arbitrary path invariants. *)
Theorem structlit_first_word_store_endpoint:
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  is_word_type (expr_type e) /\ is_word_type fty /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  compile_expr ce (expr_type e) e sb = (vv,sc) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  unwrap_value ce vv sm = (Var load,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce (Var load) (Var dst) fty (lowered_value_type ce e)
    su = ((),sv) /\ fn_has_code sa sd fn /\ fn_has_code sa sb fn /\
  local_ptrs_reserved ce sa /\ fn_inst_ids_distinct fn /\
  eval_operand buf.buf_operand t = SOME addrw /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addrw,N) /\
  vv_post ctx fn ce cx e es sb sc t ee tv vv s /\
  ptr_covers G tn root s N /\
  lookup_var root s = SOME a /\ root <> dst /\ dst <> load /\
  u = (update_var dst (a+0w) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  Ga = step_prov PG G (mk_inst sc.cs_next_id ADD [Var root; Lit 0w] [dst])
    (update_var dst (a+0w) s) /\
  tna = step_taint (mk_inst sc.cs_next_id ADD [Var root; Lit 0w] [dst]) s
    (update_var dst (a+0w) s) tn /\
  gas_marked_exec_ptr D (ctx,fn) PG (read_result cx tv)
    (ee,u,Ga,tna) [] (INL v) ee G1 tn1 (OK s1) /\
  expr_post ctx fn ce cx e es sb su t ee v (Var load) s1 /\
  ptr_val_ok cx (expr_type e) v (Var load) G1 tn1 s1 /\
  ghost_kept ce es sb G0 tn0 t G1 tn1 /\ ghost_inv d ce cx ee G1 tn1 s1 /\
  (!r n. r <> load /\ ptr_covers Ga tna r u n ==>
    ptr_covers G1 tn1 r s1 n) /\
  (!x. x <> load ==> lookup_var x s1 = lookup_var x u) /\
  s1.vs_current_bb = su.cs_current_bb /\
  s1.vs_inst_idx = LENGTH su.cs_current_insts /\ ~ctx_has_dalloca ctx ==>
  ?w tn2 s2.
    eval_operand (Var load) s1 = SOME w /\
    s2 = (mstore (w2n addrw) w s1 with vs_inst_idx := SUC s1.vs_inst_idx) /\
    tn2 = step_taint (mk_inst su.cs_next_id MSTORE [Var dst;Var load] []) s1
      (mstore (w2n addrw) w s1) tn1 /\
    gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G1 tn2 (OK s2) /\
    ghost_kept ce es sb G0 tn0 t G1 tn2 /\
    stmt_state_rel ctx fn ce cx ee s2 /\ ghost_inv d ce cx ee G1 tn2 s2 /\
    s2.vs_current_bb = sv.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sv.cs_current_insts
Proof
  strip_tac >>
  `lookup_var root s = SOME addrw` by
    (irule (cj 2 structlit_child_zero_add_address) >> metis_tac[]) >>
  `a = addrw` by metis_tac[optionTheory.SOME_11] >>
  `lookup_var dst s1 = SOME addrw` by
    (qpat_x_assum `!x. x <> load ==> _` (qspec_then `dst` mp_tac) >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, WORD_ADD_0]) >>
  `32 <= N` by
    (drule structlit_word_field_capacity >> simp[] >> metis_tac[]) >>
  qpat_x_assum `N = _` SUBST_ALL_TAC >>
  drule_all structlit_first_word_store_continuation >> strip_tac >>
  `b = addrw` by metis_tac[optionTheory.SOME_11] >> fs[] >>
  `op_taint tn1 (Var load) = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel ctx fn ce cx ee
      (mstore (w2n addrw) w s1 with vs_inst_idx := SUC s1.vs_inst_idx) /\
   ghost_inv d ce cx ee G1
      (step_taint (mk_inst su.cs_next_id MSTORE [Var dst;Var load] []) s1
        (mstore (w2n addrw) w s1) tn1)
      (mstore (w2n addrw) w s1 with vs_inst_idx := SUC s1.vs_inst_idx)` by
    (irule structlit_word_store_live_frame >> simp[] >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
     qexistsl [`dst`, `su.cs_next_id`, `tn1`] >> simp[]) >>
  qpat_x_assum `SUC s1.vs_inst_idx = _`
    (fn th => rule_assum_tac (REWRITE_RULE[th])) >> simp[]
QED

(* The outer frame is anchored before either Range endpoint is evaluated.
   The loop slot and counters are live at the header, not part of that
   original-entry frame. *)
Theory bodyForRangeHeaderMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods stmtSimForParts
  loweringPosts stmtSimProps vyperStorageTrace vyperStorageFootprint
  exprSimHypsDefs fragExec allocLimits integer_word list integer finite_map

Definition range_outer_frame_mods_def[nocompute]:
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t <=>
    alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
           lookup_var x t = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es0 sa s0 cenv ee t /\
    (!aid off z i.
       FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'. local_region cenv es0.scopes s0 nm b z' ==>
                  off + z <= b \/ b + z' <= off) /\
       off <= i /\ i < off + z /\ i IN tn.t_mem ==> i IN tn0.t_mem)
End

(* H has already been selected by the gas post. Source consistency and
   the qualified cells refer to ee (the popped, outer scope). *)
Definition range_header_mods_def[nocompute]:
  range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
      sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
      H rs ee G tn t <=>
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= bound /\
    value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
    (?k. k + LENGTH rs = Num (n2 - n1) /\
         rs = GENLIST (\j. Value (IntV (n1 + &(k + j)))) (LENGTH rs) /\
         lookup_var cv t = SOME (i2w (n1 + &k))) /\
    lookup_var ev t = SOME (i2w n2) /\
    lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
    ptr_covers G tn p t sz /\
    op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
    op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
    t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    body_const_cells_agree_mods mods cx env ee /\
    expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
    storage_trace_domain cx st0 ee.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ret_pc_ok cenv sa t /\ return_buf_frame d cenv sb0 t /\
    return_buf_sep d cenv ee t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
    range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t
End

(* Both the empty-range edge and the Break edge have this same normal
   post at the For exit. The compiler returns the outer cenv. *)
Definition range_done_mods_def[nocompute]:
  range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
      H ee G tn t <=>
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t
End

Theorem range_header_init_mods:
  n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\ Num (n2 - n1) <= bound /\
  value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
  lookup_var cv t = SOME (i2w n1) /\ lookup_var ev t = SOME (i2w n2) /\
  lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p t sz /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
  t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
  body_const_cells_agree_mods mods cx env ee /\
  expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
  storage_trace_domain cx st0 ee.storage_trace /\
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  ret_pc_ok cenv sa t /\ return_buf_frame d cenv sb0 t /\
  return_buf_sep d cenv ee t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t ==>
  range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
    sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
    H (GENLIST (\j. Value (IntV (n1 + &j))) (Num (n2 - n1))) ee G tn t
Proof
  strip_tac >> simp[range_header_mods_def] >> first_assum ACCEPT_TAC
QED

Theorem range_suffix_cons_mods:
  k + LENGTH (a::rs) = N /\
  a::rs = GENLIST (\j. Value (IntV (n1 + &(k + j)))) (LENGTH (a::rs)) ==>
  a = Value (IntV (n1 + &k)) /\ k < N /\
  (k + 1) + LENGTH rs = N /\
  rs = GENLIST (\j. Value (IntV (n1 + &((k + 1) + j)))) (LENGTH rs)
Proof
  simp[Once GENLIST_CONS, combinTheory.o_DEF,
       AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  `!j:num. k + SUC j = j + (k + 1)` by decide_tac >>
  asm_rewrite_tac[] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theorem range_header_test_mods:
  range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
    sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
    H rs ee G tn t ==>
  (lookup_var cv t = lookup_var ev t <=> rs = [])
Proof
  simp[range_header_mods_def] >> strip_tac >> simp[] >>
  Cases_on `rs` >> fs[]
  >- simp[i2w_counter_end] >>
  irule i2w_counter_ne >> simp[] >> decide_tac
QED

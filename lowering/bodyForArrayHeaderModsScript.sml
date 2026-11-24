(* Linked Array-loop header and outer exit. Compiler geometry is separate;
   Route records only the current evidence for the selected capture. *)
Theory bodyForArrayHeaderMods
Ancestors
  bodyForRangeHeaderMods bodyFullPredsMods bodyFullPostsMods
  loweringPosts stmtSimProps vyperStorageTrace vyperStorageFootprint
  exprSimHypsDefs fragExec allocLimits arithmetic list words finite_map

(* The outer frame is identical to the Range loop frame: both are anchored
   at the original For statement, before evaluating the iterator. *)
Definition for_array_outer_frame_mods_def[nocompute]:
  for_array_outer_frame_mods = range_outer_frame_mods
End

(* Expression-age rows anchor the memory and taint frame. Variables from
   before the length slice must survive as well; the live length operand
   itself is recorded in the header, regardless of when it was defined. *)
Definition for_array_capture_frame_mods_def[nocompute]:
  for_array_capture_frame_mods cenv (em,saExpr,saLen,u,tu) ee tn t <=>
    alloca_frame cenv em saExpr u cenv ee t /\
    u.vs_alloca_next <= t.vs_alloca_next /\
    (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==>
               FLOOKUP t.vs_allocas aid = SOME row) /\
    (!x w. not_fresh_at saLen x /\ lookup_var x u = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b sz i. FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
      aid < saExpr.cs_next_id /\
      (!nm lb lsz. local_region cenv em.scopes u nm lb lsz ==>
                   b + sz <= lb \/ lb + lsz <= b) /\
      b <= i /\ i < b + sz /\ i IN tn.t_mem ==> i IN tu.t_mem)
End

Definition for_array_item_mods_def[nocompute]:
  for_array_item_mods cenv sa saExpr (xd,dw,capacity,aidItem) ee G tn t <=>
    sa.cs_next_id <= aidItem /\ saExpr.cs_next_id <= aidItem /\
    w2n dw + capacity < dimword (:256) /\
    w2n dw + capacity <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas aidItem = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers G tn xd t capacity /\
    (!nm b sz. local_region cenv ee.scopes t nm b sz ==>
                w2n dw + capacity <= b \/ b + sz <= w2n dw)
End

Definition for_array_index_mods_def[nocompute]:
  for_array_index_mods vs idx rs t <=>
    ?k. k <= LENGTH vs /\ rs = DROP k vs /\ lookup_var idx t = SOME (n2w k)
End

(* The saved operand and item allocation are fixed across all rounds.
   Route can carry an observed storage root/path or a selected snapshot.
   Its evidence may vary with the current horizon and popped state. *)
Definition for_array_header_mods_def[nocompute]:
  for_array_header_mods mods DF lo d ctx func cenv cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) item
      vs (base_op,bw,len_op,idx) cond_lbl Route H rs ee G tn t <=>
    for_array_index_mods vs idx rs t /\ LENGTH vs < dimword (:256) /\
    eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
    op_prov G len_op = NONE /\ op_taint tn len_op = {} /\
    FLOOKUP G idx = NONE /\ op_taint tn (Var idx) = {} /\
    eval_operand base_op t = SOME bw /\ op_taint tn base_op = {} /\
    for_array_item_mods cenv sa saExpr item ee G tn t /\
    t.vs_current_bb = cond_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    body_const_cells_agree_mods mods cx env ee /\
    expr_sim_inv_mods mods cenv cx env ee /\ lookup_scopes id ee.scopes = NONE /\
    storage_trace_domain cx st0 ee.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    ret_pc_ok cenv sa t /\ return_buf_frame d cenv sa t /\
    return_buf_sep d cenv ee t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!fn inst q. frag_reachable ctx func t fn inst q ==> dalloca_fmp_headroom inst q) /\
    for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t /\
    for_array_capture_frame_mods cenv (em,saExpr,saLen,u,tu) ee tn t /\
    Route H rs ee G tn t
End

(* Both an exhausted loop and a Break land at the outer statement exit. *)
Definition for_array_done_mods_def[nocompute]:
  for_array_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
      H ee G tn t <=>
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
    cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t
End

(* Entry can ignore the bind's individual horizon and transport this
   existential certificate instead. The descriptor is chosen outside K. *)
Definition for_array_saved_entry_mods_def[nocompute]:
  for_array_saved_entry_mods cx st0 Header vs ee G tn t <=>
    ?saved. !K. valid_horizon cx st0 K ee.storage_trace ==>
               Header saved K vs ee G tn t
End

Theorem for_array_header_init_mods:
  lookup_var idx t = SOME 0w ==> for_array_index_mods vs idx vs t
Proof
  strip_tac >> simp[for_array_index_mods_def] >> qexists_tac `0` >> simp[]
QED

Theorem for_array_header_nil_mods:
  for_array_index_mods vs idx [] t ==>
  lookup_var idx t = SOME (n2w (LENGTH vs))
Proof
  simp[for_array_index_mods_def, Once EQ_SYM_EQ] >> strip_tac >>
  `k = LENGTH vs` by decide_tac >>
  qpat_x_assum `k = LENGTH vs` SUBST_ALL_TAC >>
  sym_tac >> first_assum ACCEPT_TAC
QED

Theorem for_array_header_cons_mods:
  for_array_index_mods vs idx (a::rs) t ==>
  ?k. k < LENGTH vs /\ a = EL k vs /\ rs = DROP (SUC k) vs /\
      lookup_var idx t = SOME (n2w k)
Proof
  simp[for_array_index_mods_def] >> strip_tac >>
  qpat_assum `a::rs = DROP k vs`
    (strip_assume_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
  qexists_tac `k` >> simp[]
QED

Theorem for_array_header_test_mods:
  for_array_header_mods mods DF lo d ctx func cenv cx env id st0
    (es0,sa,s0,G0,tn0) (em,saExpr,saLen,u,tu) item
    vs (base_op,bw,len_op,idx) cond_lbl Route H rs ee G tn t ==>
  (lookup_var idx t = eval_operand len_op t <=> rs = [])
Proof
  simp[for_array_header_mods_def, for_array_index_mods_def] >> strip_tac >>
  `k < dimword (:256)` by decide_tac >>
  qpat_assum `rs = DROP k vs` (once_rewrite_tac o single) >>
  simp[LESS_MOD] >> decide_tac
QED

Theorem for_array_saved_entry_extract_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       for_array_saved_entry_mods cx st0 Header vs ee G tn t) ==>
  ?saved. !K. valid_horizon cx st0 K ee.storage_trace ==>
             Header saved K vs ee G tn t
Proof
  strip_tac >>
  qpat_x_assum `!H. _ ==> for_array_saved_entry_mods _ _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  fs[storage_trace_domain_def, for_array_saved_entry_mods_def]
QED

Theorem for_array_done_outer_mods:
  for_array_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
    H ee G tn t ==>
  for_array_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G tn t
Proof
  simp[for_array_done_mods_def] >> strip_tac >> first_assum ACCEPT_TAC
QED

Theory bodyPtrPopIndexRepresentation
Ancestors bodyPtrPopTargetFactor bodyPtrDefs bodyPtrPreds fragGasPathPtr
  gasSummaryComposePtr

(* Specialization of the supplied index judgment, retaining the complete
   outcome (normal path, exceptional path, or certified exemption). *)
Theorem pop_index_counted_handoff:
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  eval_base_place cx bt source = (INL pv,es) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\
      (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all pop_target_index_ptr_premise >> strip_tac >>
  fs[body_expr_ptr_ok_def] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum (qspecl_then [`d`, `PG`, `func`, `ty`] strip_assume_tac) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_ptr_def] >> disch_then drule_all >> simp[]
QED

(* The live-root projection is available uniformly for every agreeing memory.
   A live subpath can then use a path-encoding lemma pointwise; this projection
   says nothing about entry.popped and is not a dead-path frame. *)
Theorem pop_index_live_root_representation:
  ghost_inv d cenv cx ee G tn s /\
  lookup_scopes id ee.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME a ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n a) mem
Proof
  strip_tac >> fs[ghost_inv_def] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* Quantified candidate interface, NOT an asserted theorem.
   Captured residual: tool_output TO_pop-20261107T052323Z_m5623_t001.
   The actual marked execution is retained, including its source read.
   Final ghost_inv supplies robust representation of entry.value only.
   Here evaluate_subscripts of that value fails; read_place uses history.
   expr_post/locals_kept exempts dynamic length words, as does ghost_kept's
   taint frame. Thus neither frame alone supplies this saved header's bytes
   or cleanliness. An execution-sensitive representation argument remains
   required; no endpoint-only model or theorem falsehood is asserted.

Candidate pop_index_dead_representation_probe:
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  eval_base_place cx bt source = (INL (PlaceR (MemoryPlace id path)),es) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_scopes id es.scopes = SOME initial_entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) sz) /\
  lookup_var root s0 = SOME root_addr /\
  mem_path_offset initial_entry.type path = SOME (offset,ArrayTV tv (Dynamic cap)) /\
  a = root_addr + n2w offset /\
  read_place cx (MemoryPlace id path) es = (INL (ArrayV (DynArrayV before)),es) /\
  not_fresh_at sa saved /\ lookup_var saved s0 = SOME a /\
  (!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV before)) (w2n a) mem) /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) ee G tn (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := []) v op s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ptr_val_ok cx (expr_type e) v op G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INR err /\
  read_place cx (MemoryPlace id path) (ee with gas_obs := []) =
    (INL (ArrayV (DynArrayV after)),ee with gas_obs := []) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV after)) (w2n a) mem
*)

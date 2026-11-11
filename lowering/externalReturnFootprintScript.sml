(* Producer boundary: actual readable footprint, never unused capacity. *)
Theory externalReturnFootprint
Ancestors
  loweringPosts valueEncoding compileEnv loweringStateRelDefs venomMemDefs arithmetic

Theorem return_expr_val_wf:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty ==>
  val_wf tv v
Proof
  simp[expr_val_at_def] >> metis_tac[]
QED

Theorem return_expr_window_bound:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> b + sz <= limit) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==> b + sz <= limit) ==>
  ?w. eval_operand op s = SOME w /\
      (val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= limit)
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem return_expr_nonempty_window_bound:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v <> 0 /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> b + sz <= limit) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==> b + sz <= limit) ==>
  ?w. eval_operand op s = SOME w /\
      w2n w + val_footprint tv v <= limit
Proof
  metis_tac[return_expr_window_bound]
QED

Theorem return_local_region_frontier:
  local_ptrs_rel func cenv scopes s /\ local_region cenv scopes s n b sz ==>
  b + sz <= s.vs_alloca_next
Proof
  simp[local_ptrs_rel_def, local_region_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem return_expr_window_frontier:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  alloca_inv s /\ local_ptrs_rel func cenv es.scopes s ==>
  ?w. eval_operand op s = SOME w /\
      (val_footprint tv v = 0 \/
       w2n w + val_footprint tv v <= s.vs_alloca_next)
Proof
  rpt strip_tac >> irule return_expr_window_bound >>
  conj_tac
  >- gvs[alloca_inv_def, alloca_next_valid_def] >>
  qexistsl_tac [`cenv`, `cx`, `es`, `sa`, `sb`, `ty`] >> simp[] >>
  metis_tac[return_local_region_frontier]
QED

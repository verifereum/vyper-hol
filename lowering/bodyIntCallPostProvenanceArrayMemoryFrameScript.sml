(* Recover live dynamic headers from the actual index endpoint, not from
   locals_kept's byte frame.  The root reconstruction is shared with callers. *)
Theory bodyIntCallPostProvenanceArrayMemoryFrame
Ancestors
  bodyIntCallLocalFrame exprLoweringProps loweringPosts loweringStateRelDefs
  bodyIntCallPathLayout

Theorem expr_post_local_sub_layout_value:
  expr_post ctx func cenv cx e es sm sn s0 ee raw op s /\
  ee.scopes = es.scopes /\
  lookup_scopes n es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) /\
  not_fresh_at sm p /\ lookup_var p s0 = SOME w /\
  value_has_type entry.type entry.value /\
  sub_layout entry.type entry.value k tv v ==>
  val_in_memory tv v (w2n w + k) s.vs_memory
Proof
  strip_tac >> irule local_ptrs_rel_sub_layout >>
  gvs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  metis_tac[]
QED

(* A live nested dynamic array, unlike an offset into inactive capacity,
   satisfies the semantic selection interface used by reconstruction. *)
Theorem nested_dynamic_live_selection:
  value_has_type (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])])) /\
  sub_layout (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    (ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])])) 32
    (ArrayTV (BaseTV BoolT) (Dynamic 1)) (ArrayV (DynArrayV [BoolV T]))
Proof
  simp_tac (srw_ss()) [LET_THM] >> conj_tac
  >- EVAL_TAC >>
  irule mem_path_selection_sub_layout >>
  reverse conj_tac >- EVAL_TAC >>
  qexists `[ValueSubscript (IntV 0)]` >> EVAL_TAC >> simp[]
QED

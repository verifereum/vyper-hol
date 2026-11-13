Theory bodyPtrIfExpMaterializedPost
Ancestors bodyPtrDefs exprSimProps ptrCoverage venomState finite_map

(* Materialization supplies annotation capacity, independently of the
   lowered-value representation used by no-copy callers. *)
Theorem ifexp_materialized_ptr_post:
  ptr_covers G tn out t capacity /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_store_size tv v <= capacity /\
  eval_operand (Var out) t = SOME w /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
    val_in_memory tv v (w2n w) m) ==>
  ptr_val_ok cx ty v (Var out) G tn t
Proof
  strip_tac >>
  gvs[ptr_covers_def, ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >> qexistsl_tac [`b`, `sz'`] >> simp[] >> decide_tac
QED

Theorem ifexp_materialized_capacity:
  ptr_covers G tn out t capacity /\ eval_operand (Var out) t = SOME w ==>
  ?b sz. FLOOKUP G out = SOME (b,sz) /\ b <= w2n w /\
    w2n w + capacity <= b+sz
Proof
  simp[ptr_covers_def, eval_operand_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_noop_annotation_capacity:
  ptr_buf_ok ce e op G s /\
  same_memory_layout ce (lowered_value_type ce e) (expr_type e) ==>
  !w. eval_operand op s = SOME w /\ type_memory_bytes ce (expr_type e) <> 0 ==>
  ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b,sz) /\ b <= w2n w /\
    w2n w + type_memory_bytes ce (expr_type e) <= b+sz
Proof
  simp[ptr_buf_ok_def, contextTheory.same_memory_layout_def] >> metis_tac[]
QED

(* A fully clean value window gives robustness without constraining dead bytes elsewhere. *)
Theory exprPtrCleanBufferPost
Ancestors
  exprPtrUnwrapStoragePost valueEncodingProps valueEncodingProofs bodyPtrDefs
  loweringPosts compileEnv context venomState pred_set list arithmetic words

Theorem clean_window_memory_agree:
  mem_agree_outside dirty mem mem' /\
  (!i. off <= i /\ i < off+nb ==> i NOTIN dirty) ==>
  mem_bytes_at off nb mem = mem_bytes_at off nb mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[LENGTH_mem_bytes_at] >>
  rpt strip_tac >>
  `off+x NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (off+x) 1 mem = mem_bytes_at (off+x) 1 mem'` by
    fs[mem_agree_outside_def] >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]
QED

Theorem clean_window_value_robust:
  val_in_memory ty v off mem /\ val_wf ty v /\ type_memory_size ty <= nb /\
  (!i. off <= i /\ i < off+nb ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==> val_in_memory ty v off mem'
Proof
  rpt strip_tac >> irule val_in_memory_mem_agree >> (conj_tac >- simp[]) >>
  qexistsl [`nb`, `mem`] >> simp[] >>
  irule clean_window_memory_agree >> goal_assum drule >> simp[]
QED

Theorem clean_buffer_pointer_posts:
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ty /\
  expr_post ctx func cenv cx e es sa sb s0 ee v (Var root) z /\
  eval_operand (Var root) z = SOME w /\ ptr_covers G tn root z nb /\
  val_wf ty v /\ type_memory_size ty <= nb /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
  (!i. w2n w <= i /\ i < w2n w+nb ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx (post_value_type cenv e) v (Var root) G tn z /\
  ptr_buf_ok cenv e (Var root) G z
Proof
  strip_tac >> irule unwrap_storage_pointer_posts >> (conj_tac >- simp[]) >>
  qexistsl [`nb`, `ty`, `w`] >> simp[] >>
  rpt strip_tac >> irule clean_window_value_robust >> (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >> qexists `nb` >>
  fs[expr_post_def, expr_val_rel_def] >> metis_tac[]
QED

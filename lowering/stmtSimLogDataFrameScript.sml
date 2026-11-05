Theory stmtSimLogDataFrame
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogData stmtSimLogArgs  exprSimMemoryTransport
  exprSimOps compileEnv venomState valueEncoding words

Definition log_write_frame_def:
  log_write_frame st b n s t <=>
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
    (!a k. a + k <= b \/ b + n <= a ==>
      mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory)
End

Definition log_source_apart_def:
  log_source_apart cx b n (op,ty) v s <=>
    !tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
      ~is_word_type ty /\ eval_operand op s = SOME w ==>
      val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= b \/
      b + n <= w2n w
End

Theorem log_write_frame_refl[simp]:
  log_write_frame st b n s s
Proof
  cheat
QED

Theorem log_write_frame_trans:
  log_write_frame st b n s t /\ log_write_frame st b n t u ==>
  log_write_frame st b n s u
Proof
  cheat
QED

Theorem log_write_frame_widen:
  log_write_frame st b n s t /\ a <= b /\ b + n <= a + k ==>
  log_write_frame st a k s t
Proof
  cheat
QED

Theorem log_write_frame_operand:
  log_write_frame st b n s t /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  eval_operand op t = eval_operand op s
Proof
  cheat
QED

Theorem log_source_apart_kept:
  log_source_apart cx b n (op,ty) v s /\ log_write_frame st a k s t /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  log_source_apart cx b n (op,ty) v t
Proof
  cheat
QED

Theorem log_source_value_kept:
  log_source_apart cx b n (op,ty) v s /\ log_write_frame st b n s t /\
  (!x. op = Var x ==> not_fresh_at st x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  expr_val_rel cx ty v op s ==>
  expr_val_rel cx ty v op t
Proof
  cheat
QED

Theorem log_placement_source_apart:
  expr_val_at cenv cx ty sa sm es v op s /\
  (!aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      sa.cs_next_id <= aid /\ aid < sm.cs_next_id ==>
      a + k <= b \/ b + n <= a) /\
  (!name a k. local_region cenv es.scopes s name a k ==>
      a + k <= b \/ b + n <= a) ==>
  log_source_apart cx b n (op,ty) v s
Proof
  cheat
QED

Theorem log_write_frame_local_region:
  log_write_frame st b n s t /\ local_ptrs_reserved cenv st ==>
  (local_region cenv scopes t name a k <=> local_region cenv scopes s name a k)
Proof
  cheat
QED

Theorem log_placement_kept:
  expr_val_at cenv cx ty sa sm es v op s /\
  log_write_frame st b n s t /\ local_ptrs_reserved cenv st /\
  (!x. op = Var x ==> not_fresh_at st x) ==>
  expr_val_at cenv cx ty sa sm es v op t
Proof
  cheat
QED

Theorem log_allocated_source_apart:
  expr_val_at cenv cx ty sa sm es v op s /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas dest = SOME (b,n) /\ sm.cs_next_id <= dest /\
  (!name a k. local_region cenv es.scopes s name a k ==>
     a + k <= b \/ b + n <= a) ==>
  log_source_apart cx b n (op,ty) v s
Proof
  cheat
QED

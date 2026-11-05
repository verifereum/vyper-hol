(* Physical ownership of the bytes read by a hash, independently of provenance. *)
Theory bodyPtrHashBuiltinsInputWindow
Ancestors
  arithmetic exprSimHash

Theorem hash_input_window_subwindow:
  (n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sc.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a /\ a+n <= b+k)) /\
  sc.cs_next_id <= sd.cs_next_id /\ a <= a' /\ a'+n' <= a+n ==>
  (n' = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sd.cs_next_id /\ b <= a' /\ a'+n' <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a' /\ a'+n' <= b+k))
Proof
  rpt strip_tac
  >- (`n' = 0` by decide_tac >> simp[])
  >- metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
  >> metis_tac[LESS_EQ_TRANS]
QED

Theorem hash_expr_val_at_input_window:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ sb.cs_next_id <= sc.cs_next_id /\
  w2n w <= a /\ a+n <= w2n w + val_footprint tv v ==>
  (n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sc.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a /\ a+n <= b+k))
Proof
  rpt strip_tac >> drule_all expr_val_at_footprint >> strip_tac
  >- metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
  >- metis_tac[LESS_EQ_TRANS]
  >> `n = 0` by decide_tac >> simp[]
QED

Theorem hash_scratch_input_window:
  FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < sc.cs_next_id /\
  b <= a /\ a+n <= b+k ==>
  (n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sc.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a /\ a+n <= b+k))
Proof
  metis_tac[]
QED

Theorem hash_dynamic_bytes_input_window:
  expr_val_at cenv cx ty sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
  ~is_word_type ty /\ eval_operand op s = SOME w /\
  sb.cs_next_id <= sc.cs_next_id ==>
  (LENGTH bs = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sc.cs_next_id /\ b <= w2n w + 32 /\
      w2n w + 32 + LENGTH bs <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= w2n w + 32 /\ w2n w + 32 + LENGTH bs <= b+k))
Proof
  rpt strip_tac >> drule_all expr_val_at_footprint >>
  simp[loweringPostsTheory.val_footprint_def] >> strip_tac >>
  `w2n w <= w2n w + 32` by decide_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

(* String source values retain their constructor across the hash memory window. *)
Theory bodyPtrHashBuiltinsShaStringInput
Ancestors bodyPtrHashBuiltinsInputWindow exprSimHash exprSimHashBoundary arithmetic

Theorem hash_string_input_window:
  expr_val_at cenv cx ty sa sb es (StringV str) op s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT cap)) /\
  ~is_word_type ty /\ eval_operand op s = SOME w /\
  sb.cs_next_id <= sc.cs_next_id ==>
  (LENGTH str = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sc.cs_next_id /\ b <= w2n w + 32 /\
      w2n w + 32 + LENGTH str <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= w2n w + 32 /\ w2n w + 32 + LENGTH str <= b+k))
Proof
  rpt strip_tac >> drule_all expr_val_at_footprint >>
  simp[loweringPostsTheory.val_footprint_def] >> strip_tac >>
  `w2n w <= w2n w + 32` by decide_tac >>
  metis_tac[LESS_EQ_TRANS, LESS_LESS_EQ_TRANS]
QED

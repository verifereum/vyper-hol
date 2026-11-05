Theory exprSimAbiDecodeFootprint
Ancestors
  exprSimHash loweringPosts exprLoweringProps valueEncoding vyperValue words

Theorem abi_decode_bytes_footprint:
  stmt_state_rel ctx fn ce cx es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type ty /\
  expr_val_rel cx ty (BytesV bs) op s /\
  expr_val_at ce cx ty sa sb es (BytesV bs) op s ==>
  ?p. eval_operand op s = SOME (n2w p) /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
      p + 32 + LENGTH bs < dimword (:256) /\
      ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
          sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          (!name lb lsz. local_region ce es.scopes s name lb lsz ==>
                        b + sz <= lb \/ lb + lsz <= b)) \/
       (?name b sz. local_region ce es.scopes s name b sz /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          local_val_at ce cx name (p-b) (BaseTV (BytesT (Dynamic n))) (BytesV bs)))
Proof
  strip_tac >>
  gvs[expr_val_rel_def] >>
  qexists `w2n w` >> simp[] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, val_footprint_def] >> strip_tac >>
  `w2n w + (32 + LENGTH bs) < dimword (:256)` by
    (irule hash_live_footprint_bound >>
     goal_assum (drule_at Any) >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  simp[] >> metis_tac[]
QED

Theorem abi_decode_bytes_post_footprint:
  expr_post ctx fn ce cx e es0 sa sb s0 es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
  ~is_word_type (expr_type e) ==>
  ?p. eval_operand op s = SOME (n2w p) /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
      p + 32 + LENGTH bs < dimword (:256) /\
      ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
          sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          (!name lb lsz. local_region ce es.scopes s name lb lsz ==>
                        b + sz <= lb \/ lb + lsz <= b)) \/
       (?name b sz. local_region ce es.scopes s name b sz /\
          b <= p /\ p + 32 + LENGTH bs <= b + sz /\
          local_val_at ce cx name (p-b) (BaseTV (BytesT (Dynamic n))) (BytesV bs)))
Proof
  strip_tac >> irule abi_decode_bytes_footprint >>
  gvs[expr_post_def] >> metis_tac[]
QED

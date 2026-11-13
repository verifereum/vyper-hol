Theory bodyPtrStructLitOldWordFrame
Ancestors exprSimAggregateChildren bodyPtrDefs loweringPosts
  valueEncodingProofs valueEncoding valueEncodingDefs venomState compileEnv finite_map

Theorem vv_post_old_buffer_mload:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s1 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+n <= lo \/ lo+sz <= b) /\
  b <= p /\ p+32 <= b+n ==>
  mload p s1 = mload p s0
Proof
  strip_tac >> drule_all vv_post_old_buffer >>
  strip_tac >> drule (cj 2 mem_bytes_at_agree_window) >>
  disch_then (qspec_then `p` mp_tac) >>
  simp[mload_def, mem_word_at_def]
QED

Theorem ghost_kept_old_buffer_clean_interval:
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+n <= lo \/ lo+sz <= b) /\
  b <= p /\ p+k <= b+n /\
  (!i. p <= i /\ i < p+k ==> i NOTIN tn0.t_mem) ==>
  !i. p <= i /\ i < p+k ==> i NOTIN tn1.t_mem
Proof
  simp[ghost_kept_def] >> rpt strip_tac >>
  `b <= i /\ i < b+n` by decide_tac >> metis_tac[]
QED

Theorem structlit_old_word_preserved:
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv s1 /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+n <= lo \/ lo+sz <= b) /\
  b <= p /\ p+32 <= b+n /\ mload p s0 = w /\
  (!i. p <= i /\ i < p+32 ==> i NOTIN tn0.t_mem) ==>
  mload p s1 = w /\ (!i. p <= i /\ i < p+32 ==> i NOTIN tn1.t_mem)
Proof
  strip_tac >> conj_tac
  >- (drule_all vv_post_old_buffer_mload >> simp[]) >>
  metis_tac[ghost_kept_old_buffer_clean_interval]
QED

(* Original allocation windows through Concat's three execution phases. *)
Theory bodyPtrBytestringBuiltinsConcatPostFrame
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix exprSimProps
  loweringPosts compileEnv finite_map arithmetic

Theorem concat_original_site_memory:
  FLOOKUP s0.vs_allocas aid = SOME (b,k) /\ aid < sa.cs_next_id /\
  sa.cs_next_id <= sm.cs_next_id /\ 32 <= bsz /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+k <= lo \/ lo+sz <= b) /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) /\
  (!aid lo sz. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (lo,sz) ==>
    regions_disjoint B bsz lo sz /\ regions_disjoint obase 64 lo sz) /\
  (!lo sz. lo+sz <= obase \/ obase+64 <= lo ==>
    mem_bytes_at lo sz s.vs_memory = mem_bytes_at lo sz s0.vs_memory) /\
  (!name lo sz. local_region ce es.scopes s name lo sz <=>
    local_region ce es.scopes s0 name lo sz) /\
  (!aid lo sz. FLOOKUP s.vs_allocas aid = SOME (lo,sz) /\ aid < sm.cs_next_id /\
    (lo+sz <= B \/ B+bsz <= lo) /\ (lo+sz <= obase \/ obase+64 <= lo) /\
    (!name lb lsz. local_region ce es.scopes s name lb lsz ==>
      lo+sz <= lb \/ lb+lsz <= lo) ==>
    mem_bytes_at lo sz u.vs_memory = mem_bytes_at lo sz s.vs_memory) /\
  (!lo sz. lo+sz <= B \/ B+32 <= lo ==>
    mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz u.vs_memory) ==>
  mem_bytes_at b k t.vs_memory = mem_bytes_at b k s0.vs_memory
Proof
  strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (b,k)` by metis_tac[] >>
  `regions_disjoint B bsz b k /\ regions_disjoint obase 64 b k` by metis_tac[] >>
  `b+k <= B \/ B+bsz <= b` by fs[regions_disjoint_def] >>
  `b+k <= obase \/ obase+64 <= b` by fs[regions_disjoint_def] >>
  `mem_bytes_at b k s.vs_memory = mem_bytes_at b k s0.vs_memory` by metis_tac[] >>
  `mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory` by
    (qpat_x_assum `!aid lo sz. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
      (qspecl_then [`aid`,`b`,`k`] irule) >> simp[] >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  `b+k <= B \/ B+32 <= b` by decide_tac >>
  metis_tac[]
QED

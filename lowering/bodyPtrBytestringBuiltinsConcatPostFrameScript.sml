(* Original allocation windows through Concat's three execution phases. *)
Theory bodyPtrBytestringBuiltinsConcatPostFrame
Ancestors
  bodyPtrBytestringBuiltinsConcatSuffix exprSimProps
  loweringPosts compileEnv loweringStateRelDefs finite_map arithmetic exprBopSimProps exprSimCopy wordArgsPtr

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

Theorem concat_original_locals_frame:
  local_ptrs_reserved ce sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w) /\
  (!name b k. local_region ce es.scopes s0 name b k <=>
    local_region ce es.scopes s name b k) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    (B+bsz <= b \/ b+k <= B) /\ (obase+64 <= b \/ b+k <= obase)) /\
  32 <= bsz /\
  (!b k. b+k <= obase \/ obase+64 <= b ==>
    mem_bytes_at b k s.vs_memory = mem_bytes_at b k s0.vs_memory) /\
  locals_kept ce es es' s u /\
  (!b k. b+k <= B \/ B+32 <= b ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k u.vs_memory) ==>
  locals_kept ce es es' s0 t
Proof
  strip_tac >>
  `locals_kept ce es es s0 s` by
    (irule locals_kept_regions >> rpt strip_tac >>
     qpat_x_assum `!b k. b+k <= obase \/ _ ==> _` irule >> metis_tac[]) >>
  `locals_kept ce es es' s0 u` by
    (irule exprBopSimPropsTheory.locals_kept_trans >>
     qexistsl_tac [`es`,`sa`,`s`] >> simp[]) >>
  irule exprSimCopyTheory.copy_buffer_locals_kept_frame >>
  qexistsl_tac [`B`,`u`,`32`] >>
  conj_tac >- (rpt strip_tac >>
    `B+bsz <= lb \/ lb+len <= B` by metis_tac[] >> decide_tac) >>
  conj_tac >- metis_tac[ADD_SYM] >> first_assum ACCEPT_TAC
QED

Theorem concat_original_wb_frame:
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s0) /\
  (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==> lookup_var x u = SOME w) /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u) /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\ t.vs_allocas = u.vs_allocas /\
  (!aid b k. FLOOKUP s0.vs_allocas aid = SOME (b,k) /\ aid < sa.cs_next_id /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==> b+k <= lo \/ lo+sz <= b) ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s0.vs_memory) /\
  (!name b k. local_region ce es.scopes s0 name b k <=>
    local_region ce es.scopes s name b k) /\
  (!name b k. local_region ce es.scopes s name b k ==>
    (B+bsz <= b \/ b+k <= B) /\ (obase+64 <= b \/ b+k <= obase)) /\
  32 <= bsz /\
  (!b k. b+k <= obase \/ obase+64 <= b ==>
    mem_bytes_at b k s.vs_memory = mem_bytes_at b k s0.vs_memory) /\
  locals_kept ce es es' s u /\
  (!b k. b+k <= B \/ B+32 <= b ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k u.vs_memory) ==>
  wb_frame ce es es' sa s0 t
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x s = SOME w` by metis_tac[] >>
  `locals_kept ce es es' s0 t` by (drule_all concat_original_locals_frame >> simp[]) >>
  simp[wb_frame_def] >> rpt conj_tac >> metis_tac[]
QED

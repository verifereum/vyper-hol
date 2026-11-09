(* Memory-frame composition for adjacent aggregate slices. *)
Theory bodyMemAggregateLoopFrames
Ancestors
  bodyMemAggregateLoopBoundary bodyMemAggregateBodyCons
  exprSimAggregateLoops exprSimAggregateChildren exprSimProps valueEncodingProofs
  loweringPosts exprLoweringProps compileEnv

Theorem aggregate_cons_slice_frame_mem:
  mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
  FLOOKUP t1.vs_allocas aid = SOME (b,asz) /\ aid < cutoff /\
  (!name lo sz. local_region ce scopes t1 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b) /\
  (!i lo sz a k.
    FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < cutoff /\
    (!name lb len. local_region ce scopes t1 name lb len ==>
      lo+sz <= lb \/ lb+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+hs <= a) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+(off+hs) \/ b+(off+hs)+ts <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) ==>
  !p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+off \/ b+off+(hs+ts) <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!p n. _ ==> mem_bytes_at p n r.vs_memory = _` irule >> decide_tac) >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n t1.vs_memory` by
    (qpat_x_assum `!i lo sz a k. _` irule >>
     reverse conj_tac >- decide_tac >>
     qexistsl_tac [`aid`, `b`, `asz`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce scopes t1 name lo sz ==> _`
       (drule_then mp_tac) >> decide_tac) >>
  `mem_bytes_at p n t1.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_assum `mem_bytes_at b asz t1.vs_memory = _`
       (mp_then Any mp_tac mem_bytes_at_agree_window) >> strip_tac >>
     sym_tac >> first_x_assum irule >> decide_tac) >> simp[]
QED

Theorem aggregate_cons_exterior_frame_mem:
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es1 t1 /\
  stmt_state_rel ctx func ce cx es1 q /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= ss.cs_next_id /\
  (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k.
    FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
    (!name lb len. local_region ce es1.scopes t1 name lb len ==>
      lo+sz <= lb \/ lb+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+hs <= a) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
  (!i p n. FLOOKUP q.vs_allocas i = SOME (p,n) /\ i < ss.cs_next_id /\
    (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es1.scopes q name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
  off+hs <= asz ==>
  !aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\ aid < sa.cs_next_id /\
    (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
    p+n <= lo \/ lo+sz <= p` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 name lo sz` by
       (irule aggregate_mem_tuple_local_region_backward >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >> metis_tac[]) >>
  `!name lo sz. local_region ce es1.scopes q name lo sz ==>
    p+n <= lo \/ lo+sz <= p` by
    (rpt strip_tac >>
     `local_region ce es1.scopes t1 name lo sz` by
       (irule local_region_frame >> conj_tac
        >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es1.scopes`, `q`] >> asm_rewrite_tac[]) >> metis_tac[]) >>
  `mem_bytes_at p n t1.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (irule vv_post_old_buffer >> goal_assum (drule_at Any) >>
     qexists `aid` >> simp[] >> metis_tac[]) >>
  `FLOOKUP t1.vs_allocas aid = SOME (p,n)` by (fs[vv_post_def] >> metis_tac[]) >>
  `FLOOKUP q.vs_allocas aid = SOME (p,n)` by metis_tac[] >>
  `mem_bytes_at p n q.vs_memory = mem_bytes_at p n t1.vs_memory` by
    (qpat_x_assum `!i lo sz a k. _` irule >>
     reverse conj_tac >- decide_tac >>
     qexistsl_tac [`aid`, `p`, `n`] >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!name lo sz. local_region ce es1.scopes t1 name lo sz ==> _`
       (drule_then mp_tac) >> decide_tac) >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory` by
    (qpat_x_assum `!i p n. _` irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- decide_tac >>
     qexists `aid` >> simp[] >> decide_tac) >> simp[]
QED

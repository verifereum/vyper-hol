(* Postcondition composition for adjacent aggregate elements. *)
Theory bodyMemAggregatePostJoin
Ancestors
  bodyMemAggregateLoopFrames bodyMemAggregateHeadContinuation
  valueEncoding valueEncodingProofs valueEncodingTyping exprBopSimProps exprSimProps
  loweringPosts exprLoweringProps compileEnv freshWrites

Theorem aggregate_cons_tuple_encoding_mem[local]:
  value_has_type htv v /\ val_in_memory htv v (b+off) q.vs_memory /\
  tuple_in_memory vs tvs (b+(off+type_memory_size htv)) r.vs_memory /\
  off+type_memory_size htv <= asz /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+(off+type_memory_size htv) \/
     b+(off+type_memory_size htv)+type_memory_size_list tvs <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) ==>
  tuple_in_memory (v::vs) (htv::tvs) (b+off) r.vs_memory
Proof
  strip_tac >> pure_once_rewrite_tac[val_in_memory_def] >>
  simp_tac std_ss [listTheory.list_case_def, LET_THM] >> conj_tac
  >- (irule (cj 1 val_in_memory_mem_agree_proof) >> simp[] >>
      conj_tac >- metis_tac[cj 1 value_has_type_val_wf] >>
      qexists `q.vs_memory` >> simp[]) >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem aggregate_cons_state_frames_mem[local]:
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  ci_mono sa sm /\ ci_mono sa ss /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
  (!z a. not_fresh_at ss z /\ lookup_var z q = SOME a ==> lookup_var z r = SOME a) /\
  (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i a. FLOOKUP q.vs_allocas i = SOME a ==> FLOOKUP r.vs_allocas i = SOME a) /\
  locals_kept ce es1 t1 q /\ locals_kept ce es1 q r ==>
  (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==> lookup_var z r = SOME a) /\
  (!i a. FLOOKUP s0.vs_allocas i = SOME a ==> FLOOKUP r.vs_allocas i = SOME a) /\
  locals_kept ce es s0 r
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm z /\ not_fresh_at ss z` by
        metis_tac[not_fresh_at_mono, ci_mono_def] >>
      qpat_x_assum `!z a. not_fresh_at ss z /\ _ ==> _` irule >> simp[] >>
      qpat_x_assum `!z a. not_fresh_at sm z /\ _ ==> _` irule >> simp[] >>
      fs[vv_post_def] >> metis_tac[]) >>
  conj_tac >- (fs[vv_post_def] >> metis_tac[]) >>
  `locals_kept ce es1 t1 r` by
    (irule locals_kept_trans >> qexistsl_tac [`es1`, `sm`, `q`] >> simp[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t1`] >> fs[vv_post_def]
QED

Theorem aggregate_cons_success_post_mem:
  vv_post ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  ci_mono sa sm /\ ci_mono sa ss /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  stmt_state_rel ctx func ce cx es s0 /\
  stmt_state_rel ctx func ce cx es1 t1 /\ stmt_state_rel ctx func ce cx es1 q /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  FLOOKUP t1.vs_allocas aid = SOME (b,asz) /\ aid < sa.cs_next_id /\
  (!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b) /\
  mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
  value_has_type htv v /\ val_in_memory htv v (b+off) q.vs_memory /\
  off+type_memory_size htv <= asz /\
  (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
  (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
  (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
    (!name lb len. local_region ce es1.scopes t1 name lb len ==>
      lo+sz <= lb \/ lb+len <= lo) /\
    lo <= a /\ a+k <= lo+sz /\
    (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
  locals_kept ce es1 t1 q /\ s0.vs_alloca_next <= t1.vs_alloca_next /\
  t1.vs_alloca_next <= q.vs_alloca_next /\
  r.vs_current_bb = sb.cs_current_bb /\ r.vs_inst_idx = LENGTH sb.cs_current_insts /\
  expr_sim_inv ce cx env es2 /\ stmt_state_rel ctx func ce cx es2 r /\
  tuple_in_memory vs tvs (b+(off+type_memory_size htv)) r.vs_memory /\
  (!z a. not_fresh_at ss z /\ lookup_var z q = SOME a ==> lookup_var z r = SOME a) /\
  (!i a. FLOOKUP q.vs_allocas i = SOME a ==> FLOOKUP r.vs_allocas i = SOME a) /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+(off+type_memory_size htv) \/
     b+(off+type_memory_size htv)+type_memory_size_list tvs <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
  (!i p n. FLOOKUP q.vs_allocas i = SOME (p,n) /\ i < ss.cs_next_id /\
    (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es1.scopes q name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
  locals_kept ce es1 q r /\ alloca_history func r /\ q.vs_alloca_next <= r.vs_alloca_next ==>
  r.vs_current_bb = sb.cs_current_bb /\ r.vs_inst_idx = LENGTH sb.cs_current_insts /\
  expr_sim_inv ce cx env es2 /\ stmt_state_rel ctx func ce cx es2 r /\
  tuple_in_memory (v::vs) (htv::tvs) (b+off) r.vs_memory /\
  (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==> lookup_var z r = SOME a) /\
  (!i a. FLOOKUP s0.vs_allocas i = SOME a ==> FLOOKUP r.vs_allocas i = SOME a) /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+off \/ b+off+type_memory_size_list (htv::tvs) <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!i p n. FLOOKUP s0.vs_allocas i = SOME (p,n) /\ i < sa.cs_next_id /\
    (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  locals_kept ce es s0 r /\ alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next
Proof
  strip_tac >> drule_all aggregate_cons_state_frames_mem >> strip_tac >>
  `sa.cs_next_id <= ss.cs_next_id` by fs[ci_mono_def] >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule aggregate_cons_tuple_encoding_mem >> goal_assum (drule_at Any) >>
      conj_tac >- first_assum ACCEPT_TAC >> qexistsl_tac [`asz`, `q`] >> simp[] >> gvs[]) >>
  conj_tac
  >- (pure_rewrite_tac[type_memory_size_def] >> rpt gen_tac >> disch_tac >>
      irule aggregate_cons_slice_frame_mem >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      qexists `aid` >> asm_rewrite_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> irule aggregate_cons_exterior_frame_mem >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      asm_rewrite_tac[] >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >>
      qexists `i` >> asm_rewrite_tac[]) >>
  decide_tac
QED

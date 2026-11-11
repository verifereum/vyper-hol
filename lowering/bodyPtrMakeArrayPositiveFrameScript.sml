(* Common exterior interface for actual positive-width store endpoints. *)
Theory bodyPtrMakeArrayPositiveFrame
Ancestors
  bodyPtrMakeArrayConsInvariant bodyPtrMakeArrayStoreFrame exprSimHash
  bodyPtrMakeArrayFlatStore wordArgsPtr freshWrites venomState
  bodyPtrMakeArrayMemoryFrame list pair valueEncodingProofs abiDecodeStaticProps loweringPosts
  compileEnv loweringStateRelDefs tupleMemoryFrame

Theorem literal_prefix_store_frame:
  literal_prefix_ok cells tn s /\
  EVERY (\(tv,v,p,k). p+k <= b) cells /\
  (!i. ~(b <= i /\ i < b+n) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  literal_prefix_ok cells tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule literal_prefix_transport >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `val_wf tv v /\ val_footprint tv v <= k` by metis_tac[literal_prefix_lookup] >>
  `p+k <= b` by (gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule robust_val_in_memory_shrinking_frame >> simp[] >>
  qexistsl [`tn.t_mem`, `tm.t_mem`, `s.vs_memory`, `z.vs_memory`, `k`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]) >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]
QED

Theorem literal_store_outer_wb:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  local_ptrs_reserved ce fr /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  z.vs_allocas = s.vs_allocas /\ off+n <= capacity /\
  (!i. ~(addr+off <= i /\ i < addr+off+n) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  wb_frame ce ees fr sf z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gvs[literal_loop_frame_def] >>
  `!p k. addr+capacity <= p \/ p+k <= addr ==>
     mem_bytes_at p k z.vs_memory = mem_bytes_at p k s.vs_memory` by
    (rpt strip_tac >> irule mem_bytes_at_bytewise >> rpt strip_tac >>
     `~(addr+off <= i /\ i < addr+(n+off))` by decide_tac >> metis_tac[]) >>
  `!x. not_fresh_at fr x ==> lookup_var x z = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  gvs[wb_frame_def, locals_kept_def] >> conj_tac
  >- (rpt strip_tac >>
      `addr+capacity <= off' \/ sz+off' <= addr` by metis_tac[] >>
      `mem_bytes_at off' sz z.vs_memory = mem_bytes_at off' sz s.vs_memory` by metis_tac[] >>
      metis_tac[]) >>
  rpt strip_tac >>
  `addr+capacity <= b \/ sz+b <= addr` by metis_tac[] >>
  `addr+capacity <= off' \/ len+off' <= addr` by decide_tac >>
  `mem_bytes_at off' len z.vs_memory = mem_bytes_at off' len s.vs_memory` by metis_tac[] >>
  metis_tac[]
QED

Theorem literal_loop_store_endpoint:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  local_ptrs_reserved ce fr /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  z.vs_allocas = s.vs_allocas /\ off+n <= capacity /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ~z.vs_halted /\ stmt_state_rel ctx func ce cx es z /\
  ghost_inv d ce cx es H tm z /\ ghost_kept ce es fr Gf tnf sf H tm /\
  FLOOKUP H root = SOME (addr,capacity) /\ ptr_covers H tm root z capacity /\
  (!i. ~(addr+off <= i /\ i < addr+off+n) ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory) ==>
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb H tm z cells off
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_store_outer_wb >> strip_tac >>
  `!name p k. local_region ce es.scopes z name p k <=>
              local_region ce es.scopes s name p k` by
    (simp[loweringStateRelDefsTheory.local_region_def] >>
     metis_tac[local_ptrs_reserved_def]) >>
  `ghost_kept ce ees fr Gf tnf sf H tm` by
    (gvs[literal_loop_frame_def, bodyPtrDefsTheory.ghost_kept_def] >>
     metis_tac[local_region_scopes_domain]) >>
  gvs[literal_loop_frame_def] >>
  `lookup_var root z = SOME (n2w addr)` by metis_tac[] >>
  `not_fresh_at sb root` by metis_tac[not_fresh_at_mono] >>
  `aid < sb.cs_next_id /\ fr.cs_next_var <= sb.cs_next_var` by decide_tac >>
  simp[] >> metis_tac[]
QED

Theorem literal_flat_loop_store:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  literal_prefix_ok cells tn s /\
  compile_store_memory ce (Var src) (Var dst) ty ty sa = ((),sb) /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  k = type_memory_bytes ce ty /\ 0 < k /\ k < dimword(:256) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ val_footprint tv v <= k /\
  ptr_mem_ok cx ty v (Var src) G tn s /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s k /\
  lookup_var dst s = SOME b /\ w2n b = addr+off /\ ptr_covers G tn dst s k /\
  off+k <= capacity /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce fr /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  ?z tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 G tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es sb G tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_loop_store_ghost >> strip_tac >>
  drule_all literal_loop_store_exterior >> strip_tac >>
  drule literal_loop_frame_runtime >> strip_tac >>
  drule_all literal_flat_store_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G tm (OK z)` >>
  `FLOOKUP G root = SOME (addr,capacity) /\ ptr_covers G tm root z capacity` by
    metis_tac[literal_loop_frame_allocation] >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb G tm z cells off` by
    (irule literal_loop_store_endpoint >> simp[] >>
     qexistsl [`G`, `k`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[]) >>
  `EVERY (\(tv,v,p,k). p+k <= addr+off) cells` by
    (gvs[literal_loop_frame_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `literal_prefix_ok cells tm z` by
    (irule literal_prefix_store_frame >> qexistsl [`addr+off`, `k`, `s`, `tn`] >>
     simp[] >> metis_tac[]) >>
  qexistsl [`z`, `tm`] >> simp[] >>
  conj_tac >- (irule literal_loop_frame_advance >> simp[]) >>
  simp[literal_prefix_cell] >> metis_tac[]
QED

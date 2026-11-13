(* Owned bytestring materialization, allowing distinct physical capacities. *)
Theory abiEncTuplePtrBytesStore
Ancestors
  abiEncTuplePtrMaterializeStore bodyPtrMakeArrayBytesStore
  bodyPtrDefs compileEnv context loweringStateRelDefs valueEncodingProps
  valueCopyBytes exprSimProps venomState pred_set words wordArgsPtr

Theorem materialize_bytestring_store_owned_ptr:
  compile_store_memory ce (Var src) (Var dst) dt ty sa = ((),sb) /\
  is_bytestring_type ty /\ is_bytestring_type dt /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) dt = SOME dtv /\
  value_has_type tv v /\ value_has_type dtv v /\
  val_wf dtv v /\ val_footprint dtv v <= n /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len+31) DIV 32) /\ n < dimword (:256) /\
  ptr_val_ok cx ty v (Var src) G tn s /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\
  (!p. not_fresh_at fr p ==> not_fresh_at sa p) /\
  (!p k. ce.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. ce.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!name base sz. local_region ce es.scopes s name base sz ==>
    regions_disjoint (w2n b) n base sz) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    aid < fr.cs_next_id ==> regions_disjoint (w2n b) n off sz) ==>
  ?H tf u.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    ghost_inv d ce cx es H tf u /\ ghost_kept ce es fr G tn s H tf /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers H tf p u k) /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x) /\
    (~ce.ce_is_ctor ==> stmt_state_rel ctx func ce cx es u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_val_ok cx dt v (Var src) G tn s` by
    metis_tac[materialize_bytestring_ptr_layout] >>
  `~is_word_type dt` by metis_tac[is_bytestring_word_type] >>
  `ptr_mem_ok cx dt v (Var src) G tn s` by gvs[ptr_val_ok_def] >>
  `ghost_kept ce es fr G tn s G tn` by simp[ghost_kept_refl] >>
  `!name p k i. local_region ce es.scopes s name p k /\
    p <= i /\ i < p+k ==> ~(w2n b <= i /\ i < w2n b+n)` by
    (rpt strip_tac >>
     qpat_x_assum `!name base sz. _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!aid p k i. FLOOKUP s.vs_allocas aid = SOME (p,k) /\
    aid < fr.cs_next_id /\ p <= i /\ i < p+k ==>
    ~(w2n b <= i /\ i < w2n b+n)` by
    (rpt strip_tac >>
     qpat_x_assum `!aid off sz. _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  drule_all literal_bytes_store_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`H`, `tf`, `sf`] >> simp[]
QED

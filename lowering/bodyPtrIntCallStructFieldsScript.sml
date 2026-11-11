(* Identical-layout struct copying reuses counted tuple execution. *)
Theory bodyPtrIntCallStructFields
Ancestors bodyPtrIntCallTupleFields typedNormalizeFields valueEncodingProofs
  vyperTyping context compileEnv fragGasPathPtr venomState words finite_map
  arithmetic list

Theorem intcall_struct_fields_conditional:
  !D ctx fn PG ce dst src fs table tvs vals sa sz G tn s b a.
    ALL_DISTINCT (MAP FST fs) /\ MAP FST fs = MAP FST tvs /\
    struct_has_type tvs vals /\
    (!nm ty n. MEM (nm,ty,n) fs ==>
      ALOOKUP table nm = SOME (ty,n) /\ n = type_memory_bytes ce ty) /\
    (!i. i < LENGTH tvs ==>
      type_memory_bytes ce (EL i (MAP (FST o SND) fs)) =
        type_memory_size (EL i (MAP SND tvs))) /\
    compile_struct_typed_copy ce (Var dst) (Var src) fs table 0 0 sa = ((),sz) /\
    fn_has_code sa sz fn /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s (type_memory_size (StructTV tvs)) /\
    ptr_covers G tn src s (type_memory_size (StructTV tvs)) /\
    w2n b + type_memory_size (StructTV tvs) < dimword (:256) /\
    w2n a + val_footprint (StructTV tvs) (StructV vals) < dimword (:256) /\
    (w2n b + type_memory_size (StructTV tvs) <= w2n a \/
     w2n a + type_memory_size (StructTV tvs) <= w2n b) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (StructTV tvs) (StructV vals) (w2n a) m) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    (!i c d dp sp bv av H t u.
      i < LENGTH tvs /\
      compile_store_memory_typed ce (Var dp) (EL i (MAP (FST o SND) fs))
        (Var sp) (EL i (MAP (FST o SND) fs)) c = ((),d) /\
      fn_has_code c d fn /\ not_fresh_at c dp /\ not_fresh_at c sp /\
      lookup_var dp u = SOME bv /\ lookup_var sp u = SOME av /\
      ptr_covers H t dp u (type_memory_size (EL i (MAP SND tvs))) /\
      ptr_covers H t sp u (type_memory_size (EL i (MAP SND tvs))) /\
      w2n bv + type_memory_size (EL i (MAP SND tvs)) < dimword (:256) /\
      w2n av + val_footprint (EL i (MAP SND tvs)) (EL i (MAP SND vals)) < dimword (:256) /\
      (w2n bv + type_memory_size (EL i (MAP SND tvs)) <= w2n av \/
       w2n av + type_memory_size (EL i (MAP SND tvs)) <= w2n bv) /\
      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
        val_in_memory (EL i (MAP SND tvs)) (EL i (MAP SND vals)) (w2n av) m) /\
      u.vs_current_bb = c.cs_current_bb /\
      u.vs_inst_idx = LENGTH c.cs_current_insts /\ ~u.vs_halted ==>
      ?K tf z. gas_path_ptr D 0 ctx fn PG H t u 0 K tf (OK z) /\
        z.vs_current_bb = d.cs_current_bb /\
        z.vs_inst_idx = LENGTH d.cs_current_insts /\ ~z.vs_halted /\
        (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
          val_in_memory (EL i (MAP SND tvs)) (EL i (MAP SND vals)) (w2n bv) m) /\
        tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\ tf.t_imm = t.t_imm /\
        z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
        z.vs_fmp = u.vs_fmp /\ z.vs_accounts = u.vs_accounts /\
        z.vs_transient = u.vs_transient /\ z.vs_call_ctx = u.vs_call_ctx /\
        (!x. not_fresh_at c x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tf (Var x) = op_taint t (Var x)) /\
        (!j. ~(w2n bv <= j /\ j < w2n bv + type_memory_size (EL i (MAP SND tvs))) ==>
          mem_bytes_at j 1 z.vs_memory = mem_bytes_at j 1 u.vs_memory /\
          (j IN tf.t_mem <=> j IN t.t_mem))) ==>
    ?K tf z. gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK z) /\
      z.vs_current_bb = sz.cs_current_bb /\
      z.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory (StructTV tvs) (StructV vals) (w2n b) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!j. ~(w2n b <= j /\ j < w2n b + type_memory_size (StructTV tvs)) ==>
        mem_bytes_at j 1 z.vs_memory = mem_bytes_at j 1 s.vs_memory /\
        (j IN tf.t_mem <=> j IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule normalize_struct_as_fields >>
  disch_then assume_tac >>
  drule struct_has_type_values_have_types >> strip_tac >>
  `LENGTH tvs = LENGTH vals` by
    (drule struct_has_type_map_fst >> metis_tac[listTheory.LENGTH_MAP]) >>
  `LENGTH fs = LENGTH vals` by
    (qpat_x_assum `MAP FST fs = _` mp_tac >> metis_tac[listTheory.LENGTH_MAP]) >>
  `type_memory_size (StructTV tvs) = SUM (MAP type_memory_size (MAP SND tvs))` by
    simp[valueEncodingTheory.type_memory_size_def, type_memory_size_fields_sum,
         listTheory.MAP_COMPOSE] >>
  `val_footprint (StructTV tvs) (StructV vals) =
   SUM (MAP type_memory_size (MAP SND tvs))` by
    simp[loweringPostsTheory.val_footprint_def] >>
  `!base m. val_in_memory (StructTV tvs) (StructV vals) base m =
            tuple_in_memory (MAP SND vals) (MAP SND tvs) base m` by
    simp[valueEncodingTheory.val_in_memory_def, fields_in_memory_tuple] >>
  qpat_x_assum `type_memory_size (StructTV tvs) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
  qpat_x_assum `val_footprint (StructTV tvs) (StructV vals) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
  qpat_x_assum `!base m. val_in_memory (StructTV tvs) _ base m = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac[th]) >>
  qpat_x_assum `!src dst doff soff. compile_struct_typed_copy _ _ _ _ _ _ _ = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum `LENGTH tvs = LENGTH vals`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  irule intcall_tuple_fields_conditional >>
  asm_rewrite_tac [listTheory.LENGTH_MAP] >>
  qexistsl_tac [`a`, `ce`, `dst`, `MAP (FST o SND) fs`, `src`,
               `MAP (FST o SND) fs`, `MAP SND tvs`] >>
  asm_rewrite_tac [listTheory.LENGTH_MAP]
QED

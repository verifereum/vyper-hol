(* Borrow the represented bytes across the read-only header and a
   nonmutating scalar suffix. The count and payload are observed at f. *)
Theory bodyCreateBlueprintRawBorrowMods
Ancestors
  abiEncodeArgsScopes bodyExtBorrowedFootprintMods wordArgsPtr
  assignTuplePtrCopyLen memoryReadProps exprLoweringProps
  loweringStateRelDefs loweringPosts bodyPtrDefs valueEncodingProps
  ptrDiscipline venomState venomInst words exprSimWordArgs compileEnv

Theorem blueprint_raw_borrowed_window_mods:
  ~exprs_can_mutate ce later /\
  (!tail. eval_exprs cx later (es with gas_obs := gs ++ tail) =
    (INL vs,ef with gas_obs := tail)) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx es s /\
  local_ptrs_reserved ce sh /\ su.cs_next_id <= sh.cs_next_id /\ ci_mono sh sb /\
  wb_frame ce es es sh s u /\ ghost_kept_at lo ce es sh G tn s Gu tu /\
  wb_frame ce es ef sb u f /\ ghost_kept_at lo ce es sb Gu tu u Gf tf /\
  s.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= f.vs_alloca_next /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_val_at ce cx (BaseT (BytesT (Dynamic cap))) sa su es (BytesV bs) bop s /\
  eval_operand bop s = SOME w /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 + LENGTH bs <= s.vs_alloca_next /\
  mem_bytes_at (w2n w + 32) (LENGTH bs) s.vs_memory = bs /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
  cnt = Var l /\ data = Var p /\ not_fresh_at sb l /\ not_fresh_at sb p /\
  eval_operand cnt u = SOME (n2w (LENGTH bs)) /\
  op_taint tu cnt = {} /\ op_prov Gu cnt = NONE /\
  lookup_var p u = SOME (n2w (w2n w + 32)) /\ ptr_covers Gu tu p u (LENGTH bs) ==>
  eval_operand cnt f = SOME (n2w (LENGTH bs)) /\
  op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
  (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
    ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
    (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
    read_memory (w2n a) (LENGTH bs) f = bs)
Proof
  strip_tac >> gvs[] >>
  `ef.scopes = es.scopes` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all eval_exprs_no_mutation_scopes >> simp[]) >>
  `sh.cs_next_var <= sb.cs_next_var /\ sh.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  `wb_frame ce es ef sh s f` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`es`,`sb`,`u`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `ghost_kept_at lo ce es sh G tn s Gf tf` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >> simp[] >>
     conj_tac >- goal_assum (drule_at Any) >>
     qpat_assum `ghost_kept_at lo ce es sb Gu tu u Gf tf` (irule_at Any) >>
     qexists `es` >> simp[]) >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  `mem_bytes_at (w2n w) (32 + LENGTH bs) f.vs_memory =
     mem_bytes_at (w2n w) (32 + LENGTH bs) s.vs_memory /\
   (!i. w2n w <= i /\ i < w2n w + (32 + LENGTH bs) /\ i IN tf.t_mem ==> i IN tn.t_mem)` by
    (drule_all ext_borrowed_footprint_frame >> simp[val_footprint_def]) >>
  `eval_operand (Var l) f = SOME (n2w (LENGTH bs)) /\
   lookup_var p f = SOME (n2w (w2n w + 32))` by
    (fs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  `FLOOKUP Gf l = FLOOKUP Gu l /\ op_taint tf (Var l) = op_taint tu (Var l) /\
   FLOOKUP Gf p = FLOOKUP Gu p /\ op_taint tf (Var p) = op_taint tu (Var p)` by
    fs[ghost_kept_at_def] >>
  `ptr_covers Gf tf p f (LENGTH bs)` by
    (irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers Gu tu p u (LENGTH bs)` (irule_at Any) >> simp[]) >>
  fs[op_prov_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  conj_tac
  >- (rpt strip_tac >> `w2n w <= i` by decide_tac >> metis_tac[]) >>
  simp[read_memory_eq_mem_bytes_at] >>
  drule mem_bytes_at_translated_window >>
  disch_then (qspecl_then [`32`,`LENGTH bs`] mp_tac) >> simp[]
QED

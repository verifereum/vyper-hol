(* The bytestring store copies the rounded runtime extent into the
   destination capacity, at one physical and ghost endpoint. *)
Theory bodyFullExtCallDefaultBytesStore
Ancestors
  bodyFullAllocGeneric bodyCopyMemoryBase immutableBytestringFootprint
  immutableMemoryFrame reasonCopySourcePtr representationCleanPtr
  valueCopyBytes valueCopy exprSimBufferStore robustCopyTransportPtr

val bytestring_store_inputs = ``
  compile_store_memory ce (Var src) (Var dst) rt sty sa = ((),sb) /\
  is_bytestring_type rt /\ is_bytestring_type sty /\
  evaluate_type (get_tenv cx) rt = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type tv v /\ value_has_type stv v /\ val_wf stv v /\
  type_memory_size tv + 64 < dimword (:256) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn src s (val_store_size stv v) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;

val bytestring_store_post = ``
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tm)) /\
    (!mem. mem_agree_outside tm.t_mem u.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem) /\
    lookup_var dst u = SOME dw /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!off k. off+k <= w2n dw \/ w2n dw+type_memory_size tv <= off ==>
      mem_bytes_at off k u.vs_memory = mem_bytes_at off k s.vs_memory) /\
    (!i. i < w2n dw \/ w2n dw+type_memory_size tv <= i ==>
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
              vs_inst_idx := s.vs_inst_idx|>) = s /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted``;

Theorem bytestring_store_extent_joint_exact:
  ^bytestring_store_inputs ==>
  ?u Gf tm.
    run_inst_seq (emitted_insts sa sb) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
    ^bytestring_store_post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    gvs[contextTheory.compile_store_memory_def,
        eventTopicValuePropsTheory.bytestring_type_not_word] >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `?len. mload (w2n sw) s = n2w len /\
         val_footprint stv v = 32 + len /\
         val_footprint tv v = 32 + len /\
         32 + len <= 32 * (1 + word_size len) /\
         32 * (1 + word_size len) <= type_memory_size stv /\
         32 * (1 + word_size len) <= type_memory_size tv` by
    (irule immutable_bytestring_runtime_extent >>
     simp[] >> qexistsl_tac [`rt`,`sty`,`get_tenv cx`] >> simp[]) >>
  rename1 `mload (w2n sw) s = n2w len` >>
  qabbrev_tac `n = 32 + 32 * word_size len` >>
  `val_store_size stv v = n` by
    (qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac bytestring_type_value >>
     asm_rewrite_tac[] >> strip_tac >> Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def, loweringPostsTheory.val_footprint_def,
         exprSimPropsTheory.val_store_size_def, Abbr `n`]) >>
  `32 <= n /\ n <= type_memory_size tv /\ n <= type_memory_size stv /\
   val_footprint stv v <= n /\ len + 31 < dimword (:256) /\
   n < dimword (:256)` by
    (fs[Abbr `n`] >> decide_tac) >>
  `(!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     mem_word_at (w2n sw) m = n2w len)` by
    suspend "header" >>
  drule robust_mem_word_at_clean >> strip_tac >>
  `ptr_covers G tn src s n /\ ptr_covers G tn dst s n` by
    metis_tac[ptr_covers_mono] >>
  `eval_operand (Var src) s = SOME sw /\ eval_operand (Var dst) s = SOME dw` by
    simp[venomStateTheory.eval_operand_def] >>
  `w2n sw+n <= s.vs_alloca_next /\ w2n dw+n <= s.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >>
     qexistsl_tac [`dw`, `Var dst`, `len`, `Var src`, `sw`] >>
     fs[Abbr `n`] >> metis_tac[]) >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    simp[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `!x. Var src = Var x ==> not_fresh_at sa x` by (rpt strip_tac >> gvs[]) >>
  `!x. Var dst = Var x ==> not_fresh_at sa x` by (rpt strip_tac >> gvs[]) >>
  `32 + 32 * word_size len < dimword (:256)` by fs[Abbr `n`] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fragExecTheory.fn_has_code_def, exprLoweringPropsTheory.same_blocks_def,
         rich_listTheory.IS_PREFIX_APPEND] >> simp[listTheory.DROP_APPEND]) >>
  pop_assum strip_assume_tac >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[Abbr `n`, vfmConstantsTheory.word_size_def] >>
  drule_all compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `sf = t` by fs[] >> qpat_x_assum `sf = t` SUBST_ALL_TAC >>
  `(!i. i < n ==> (w2n dw+i IN tnf.t_mem <=> w2n sw+i IN tn.t_mem)) /\
   (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem))` by
    (drule_all bodyPtrIfExpBytesPostTheory.bytestring_copy_effects >>
     strip_tac >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`,
                `Gf`, `tnf`] >>
  suspend "exit"
QED

Resume bytestring_store_extent_joint_exact[header]:
  `(?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)` by
    (qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac bytestring_type_value >>
     asm_rewrite_tac[] >> strip_tac >> Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def, loweringPostsTheory.val_footprint_def]) >>
  rpt strip_tac >>
  qpat_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` (qspec_then `m` mp_tac) >>
  qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac bytestring_type_value >>
  asm_rewrite_tac[] >> strip_tac >> gvs[valueEncodingDefsTheory.val_in_memory_def]
QED

Resume bytestring_store_extent_joint_exact[exit]:
  conj_tac >-
    (`t.vs_inst_idx = s.vs_inst_idx` by
       (qpat_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
        simp[venomStateTheory.venom_state_component_equality]) >>
     qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK t` (pure_rewrite_tac o single) >>
     gvs[venomStateTheory.venom_state_fupdfupds, venomStateTheory.venom_state_component_equality]) >>
  conj_tac >- asm_rewrite_tac[] >>
  `(?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)` suffices_by
    (disch_tac >> rewrite_tac[venomStateTheory.venom_state_accfupds] >>
     conj_tac
     >- (rpt strip_tac >> irule bodyPtrIfExpBytesPostTheory.bytestring_copy_robust_destination >>
         metis_tac[]) >>
     conj_tac
     >- (qpat_assum `!p. not_fresh_at sa p ==> _ /\ _ /\ _`
           (qspec_then `dst` mp_tac) >> fs[venomStateTheory.lookup_var_def]) >>
     conj_tac
     >- (qx_gen_tac `x` >> qpat_assum `!p. not_fresh_at sa p ==> _ /\ _ /\ _`
           (qspec_then `x` mp_tac) >>
         rewrite_tac[venomStateTheory.lookup_var_def,
                     venomStateTheory.venom_state_accfupds]) >>
     conj_tac
     >- (rpt strip_tac >> asm_rewrite_tac[] >> irule buffer_mcopy_exterior >>
         decide_tac) >>
     conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_assum `!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> _` irule >>
         decide_tac) >>
     conj_tac
     >- asm_rewrite_tac[placeMemoryTypedPrimitiveTheory.mcopy_memory_length] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     fs[venomStateTheory.venom_state_component_equality,
        exprLoweringPropsTheory.same_blocks_def]) >>
  qspecl_then [`get_tenv cx`,`sty`,`stv`] mp_tac bytestring_type_value >>
  asm_rewrite_tac[] >> strip_tac >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, loweringPostsTheory.val_footprint_def]
QED
Finalise bytestring_store_extent_joint_exact

Theorem bytestring_store_extent_joint:
  ^bytestring_store_inputs ==> ?u Gf tm. ^bytestring_store_post
Proof
  disch_tac >> mp_tac (SPEC_ALL bytestring_store_extent_joint_exact) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tm`] (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> first_assum ACCEPT_TAC
QED

val bytestring_capacity_inputs = ``
  compile_store_memory ce (Var src) (Var dst) rt sty sa = ((),sb) /\
  is_bytestring_type rt /\ is_bytestring_type sty /\
  evaluate_type (get_tenv cx) rt = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type tv v /\ value_has_type stv v /\ val_wf stv v /\
  type_memory_size tv + 64 < dimword (:256) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;

Theorem extcall_default_bytes_store_capacity_joint_exact:
  ^bytestring_capacity_inputs ==>
  ?u Gf tm.
    run_inst_seq (emitted_insts sa sb) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
    ^bytestring_store_post
Proof
  strip_tac >>
  `val_store_size stv v <= type_memory_size stv` by simp[exprSimPropsTheory.val_store_size_le] >>
  irule bytestring_store_extent_joint_exact >> asm_rewrite_tac[] >>
  qexistsl_tac [`ce`,`cx`,`rt`,`src`,`stv`,`sty`,`sw`] >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  irule ptr_covers_mono >> qexists_tac `type_memory_size stv` >> asm_rewrite_tac[]
QED

Theorem extcall_default_bytes_store_capacity_joint:
  ^bytestring_capacity_inputs ==> ?u Gf tm. ^bytestring_store_post
Proof
  disch_tac >> mp_tac (SPEC_ALL extcall_default_bytes_store_capacity_joint_exact) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tm`] (assume_tac o CONJUNCT2)) >>
  qexistsl_tac [`u`,`Gf`,`tm`] >> first_assum ACCEPT_TAC
QED

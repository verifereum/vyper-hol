Theory bodyFullStructLitBytes
Ancestors
  bodyFullAllocGeneric typedCopyOriginPtrBytes gasOutcomeFullCompose
  typedMemoryCopy exprLowering bodyPtrDefs valueCopy representationCleanPtr
  ptrSafeRun contextCodegenRel emitHelper compileEnv context
  bodyCopyMemoryBase fragExec rich_list list

Theorem structlit_bytes_store_origin_ptr_path:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u G2 tn2.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,G2,tn2)) /\
    val_in_memory dtv v (w2n dw) u.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn2.t_imm = tn.t_imm /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tn2.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP G2 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!ty tv. is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv ==>
     (?cap. tv = BaseTV (BytesT (Dynamic cap))) \/
     (?cap. tv = BaseTV (StringT cap))` by
    (Cases >> simp[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> rw[is_bytestring_type_def, vyperValueTheory.evaluate_type_def]) >>
     rw[vyperValueTheory.evaluate_type_def]) >>
  `(?cap. stv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. stv = BaseTV (StringT cap))` by metis_tac[] >>
  `(?cap. dtv = BaseTV (BytesT (Dynamic cap))) \/
   (?cap. dtv = BaseTV (StringT cap))` by metis_tac[] >>
  gvs[] >> Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  gvs[valueEncodingTheory.type_memory_size_def] >>
  qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_def, Once compile_store_memory_typed_def] >> strip_tac >>
  FIRST [rename1 `BytesV bs` >> qabbrev_tac `len = LENGTH bs`,
         rename1 `StringV str` >> qabbrev_tac `len = STRLEN str`] >>
  rename1 `ptr_covers G tn xs s (32 * word_size source_capacity + 32)` >>
  rename1 `ptr_covers G tn xd s (32 * word_size destination_capacity + 32)` >>
  suspend "runtime"
QED

Resume structlit_bytes_store_origin_ptr_path[runtime]:
  markerLib.RESUME_TAC >>
  `word_size len <= word_size source_capacity /\
   word_size len <= word_size destination_capacity` by
    (conj_tac >> irule exprSimPropsTheory.word_size_monotone >> simp[Abbr `len`]) >>
  `32 + 32 * word_size len < dimword (:256)` by decide_tac >>
  `mem_word_at (w2n sw) s.vs_memory = n2w len` by
    (qpat_x_assum `!mem. _` (qspec_then `s.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at (w2n sw) mem = n2w len` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
     simp[valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
  drule representationCleanPtrTheory.robust_mem_word_at_clean >> strip_tac >>
  `mload (w2n sw) s = n2w len` by
    gvs[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `ptr_covers G tn xs s (32 + 32 * word_size len) /\
   ptr_covers G tn xd s (32 + 32 * word_size len)` by
    (gvs[ptr_covers_def] >> conj_tac >> goal_assum (drule_at Any) >> decide_tac) >>
  `len + 31 < dimword (:256)` by
    (`len + 31 < ((len + 31) DIV 32 + 1) * 32` by
       simp[GSYM arithmeticTheory.DIV_LE_X] >>
     qpat_x_assum `32 + 32 * word_size len < _` mp_tac >>
     pure_rewrite_tac[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  drule store_bytestring_run_exact >>
  disch_then (qspecl_then [`s`, `sw`, `dw`, `len`] mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule compile_store_bytestring_body_mem_ok >>
     goal_assum (drule_at Any) >> qexistsl_tac [`dw`, `Var xd`, `Var xs`] >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, exprLoweringPropsTheory.same_blocks_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  suspend "path"
QED

Resume structlit_bytes_store_origin_ptr_path[path]:
  markerLib.RESUME_TAC >>
  `?Gf tnf sf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)),Gf,tnf)) /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + (32 + 32 * word_size len)}) UNION
      {w2n dw+i | i < 32 + 32 * word_size len /\ w2n sw+i IN tn.t_mem} /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p))` by
    (mp_tac (Q.SPECL [`lo`, `explicit`, `ctx`, `func`, `PG`] compile_store_bytestring_origin_ptr_path) >>
     simp[GSYM vfmConstantsTheory.word_size_def] >>
     disch_then (qspecl_then [`sa`, `sb`, `xs`, `xd`, `G`, `tn`, `s`, `sw`, `dw`, `len`, `bb`] mp_tac) >>
     simp[] >>
     (impl_tac >- (conj_tac >> once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)) >>
     strip_tac >>
     qexistsl_tac [`Gf`, `tnf`] >> simp[]) >>
  gvs[] >>
  qexistsl_tac [`sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`, `Gf`, `tnf`] >>
  simp[] >>
  (conj_tac
  >- (irule valueCopyTheory.mcopy_val_in_memory >>
      simp[loweringPostsTheory.val_footprint_def, Abbr `len`, exprSimPropsTheory.le_word_size_mul] >>
      qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` (qspec_then `s.vs_memory` mp_tac) >>
      simp[mem_agree_outside_def, valueEncodingDefsTheory.val_in_memory_def]) >>
  conj_tac
  >- (simp[typed_copy_state_frame_def] >> conj_tac
      >- gvs[venomStateTheory.venom_state_component_equality] >>
      conj_tac >- gvs[venomStateTheory.lookup_var_def] >>
      simp[typed_copy_frame_def] >> conj_tac
      >- (rpt gen_tac >> strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> decide_tac) >>
      simp[venomExecSemanticsTheory.mcopy_def,
           immutableMemoryFrameTheory.immutable_write_memory_capacity, arithmeticTheory.MAX_DEF]) >>
  conj_tac >- gvs[venomStateTheory.venom_state_component_equality] >>
  conj_tac >- gvs[venomStateTheory.venom_state_component_equality, exprLoweringPropsTheory.same_blocks_def] >>
  conj_tac >- (rpt strip_tac >> eq_tac >> simp[] >> rpt strip_tac >> decide_tac) >>
  rpt strip_tac >>
  irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `32 + 32 * word_size len`, `w2n sw`, `tn.t_mem`] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ _` drule >>
      simp[valueEncodingDefsTheory.val_in_memory_def, Abbr `len`]) >>
  conj_tac >- (rpt strip_tac >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM, arithmeticTheory.EQ_ADD_LCANCEL]) >>
  conj_tac >- simp[loweringPostsTheory.val_footprint_def, Abbr `len`, exprSimPropsTheory.le_word_size_mul] >>
  POP_ASSUM_LIST (K all_tac) >>
  `32 + 32 * word_size len = 32 * word_size len + 32` by decide_tac >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[valueEncodingDefsTheory.mem_bytes_at_def, venomMemPropsTheory.mcopy_padded_read] >> REFL_TAC)
QED

Finalise structlit_bytes_store_origin_ptr_path

Theorem structlit_bytes_store_full_suffix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> Q H res ee G1 tn1 t) ==>
    ?v sw dw.
      compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
      ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty /\
      type_memory_bytes cenv dty = type_memory_size dtv /\
      acyclic_struct_metadata cenv.ce_struct_fields /\
      sfields_tenv_consistent cenv.ce_struct_fields tenv /\
      (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
         ALL_DISTINCT (MAP FST fields) /\
         EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
           sz = type_memory_size tv) fields) /\
      type_widens_to tenv sty dty /\
      evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
      value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
      not_fresh_at sa xs /\ not_fresh_at sa xd /\
      lookup_var xs t = SOME sw /\ lookup_var xd t = SOME dw /\
      (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
             val_in_memory stv v (w2n sw) mem) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= t.vs_alloca_next) /\
      (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= t.vs_alloca_next) /\
      ptr_covers G1 tn1 xs t (type_memory_size stv) /\
      ptr_covers G1 tn1 xd t (type_memory_size dtv) /\
      allocas_from lo t /\ lo <= t.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
      t.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!u G2 tn2.
        val_in_memory dtv v (w2n dw) u.vs_memory /\
        typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) t u /\
        ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        tn2.t_imm = tn1.t_imm /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
             (i IN tn2.t_mem <=> i IN tn1.t_mem)) /\
        (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
               val_in_memory dtv v (w2n dw) mem) /\
        (!p. not_fresh_at sa p ==>
           FLOOKUP G2 p = FLOOKUP G1 p /\ op_taint tn2 (Var p) = op_taint tn1 (Var p)) ==>
        !H. valid_horizon cx st0 H ee.storage_trace ==> Q' H res ee G2 tn2 u)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >> irule gas_outcome_full_zero_suffix >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all structlit_bytes_store_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `u` (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac)))) >>
  qexistsl_tac [`u`, `G2`, `tn2`] >>
  gen_tac >> disch_tac >> conj_tac >- simp[] >>
  first_x_assum irule >> simp[]
QED

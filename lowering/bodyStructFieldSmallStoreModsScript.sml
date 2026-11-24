(* Fixed-cursor stores for words and empty physical layouts. *)
Theory bodyStructFieldSmallStoreMods
Ancestors
  bodyStructFieldCutsMods logStoreDataOriginPtr bodyFullPathHistory
  wideningZeroLayout valueCopyBytes contextProps valueEncodingProofs
  exprSimProps typedMemoryCopy exprSimFullBundleProps fragGasOriginPtr
  context venomMemDefs venomState words

Theorem struct_field_small_store_mods:
  compile_store_memory ce op (Var dst) dty sty sa = ((),sb) /\
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,addr) (sa,G,tn,s) /\
  (is_word_type dty \/ type_memory_size stv = 0) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    struct_store_effects func (sa,G,tn,s) (sb,G',tn',t) (addr,dtv,v)
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >>
  Cases_on `is_word_type dty` >> fs[struct_operand_mods_def]
  >- (drule_all word_tv_memory_size >> strip_tac >>
      `addr < dimword (:256)` by decide_tac >>
      gvs[] >>
      drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
        compile_store_memory_word_origin_ptr_path >>
      disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (qspecl_then [`explicit`, `ctx`, `PG`] mp_tac) >>
      simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> strip_tac >>
      `alloca_history func t` by
        (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
           (qspec_then `ARB` assume_tac) >>
         drule_all body_full_path_alloca_history >> simp[]) >>
      `t.vs_alloca_next = s.vs_alloca_next` by
        (qpat_assum `typed_copy_state_frame _ _ _ _ _`
           (mp_tac o cj 1 o PURE_REWRITE_RULE [typed_copy_state_frame_def]) >>
         simp[Once venom_state_component_equality]) >>
      qexistsl_tac [`t`, `Gf`, `tnf`] >>
      simp[struct_store_effects_def, expr_sim_full_endpoint_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sty = dty` by (drule_all type_widens_to_zero_layout >> simp[]) >> gvs[] >>
  `~is_bytestring_type dty` by
    (strip_tac >> drule bytestring_memory_bytes_positive >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  `sb = sa` by
    fs[compile_store_memory_def, compile_copy_memory_zero] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[struct_store_effects_def, gas_origin_ptr_path_rules,
       expr_sim_full_endpoint_def, typed_copy_state_frame_refl,
       return_zero_wf_memory]
QED

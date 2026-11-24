(* Positive non-bytes field stores at the actual StructLit write cursor. *)
Theory bodyStructFieldAggregateStoreMods
Ancestors
  bodyStructFieldCutsMods logStoreDataOriginPtr bodyFullPathHistory
  exprSimAggregateChildren typedMemoryCopy exprSimFullBundleProps
  fragGasOriginPtr context venomMemDefs venomState finite_map list words

Theorem struct_field_aggregate_store_mods:
  compile_store_memory ce op (Var dst) dty sty sa = ((),sb) /\
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,addr) (sa,G,tn,s) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ 0 < type_memory_size stv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
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
  fs[struct_operand_mods_def] >>
  `~is_bytestring_type sty` by metis_tac[type_widens_from_bytestring] >>
  `val_footprint stv v = type_memory_size stv` by
    (irule evaluated_nonbytes_footprint >> qexistsl_tac [`tenv`,`sty`] >> simp[]) >>
  `addr < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    compile_store_memory_origin_ptr_path >>
  disch_then (drule_at (Pat `type_widens_to _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `!mem. mem_agree_outside _ _ mem ==> val_in_memory _ _ _ mem`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
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
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

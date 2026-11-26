(* The bytestring store copies the reached payload, not the whole destination capacity. *)
Theory bodyStructFieldBytesStoreMods
Ancestors
  bodyStructFieldCutsMods bodyFullStructLitBytes bodyFullPathHistory
  exprSimConvert exprSimFullBundleProps typedMemoryCopy exprLowering
  fragGasOriginPtr loweringStateRelDefs ptrDiscipline allocaHistory
  venomMemDefs[qualified] venomState words list

Theorem struct_field_bytes_store_mods:
  struct_operand_mods (ce,tenv,sty,dty,stv,dtv) (op,v) (dst,addr) (sa,G,tn,s) /\
  is_bytestring_type dty /\ 0 < type_memory_size stv /\
  compile_store_memory ce op (Var dst) dty sty sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  alloca_history func s /\ venomMemDefs$alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    struct_store_effects func (sa,G,tn,s) (sb,G',tn',t) (addr,dtv,v)
Proof
  strip_tac >>
  `~is_word_type dty` by metis_tac[is_word_type_not_bytestring] >>
  fs[struct_operand_mods_def] >>
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  gvs[eval_operand_def] >>
  `w2n ((n2w addr):bytes32) = addr` by simp[] >>
  drule structlit_bytes_store_origin_ptr_path >>
  disch_then (drule_at (Pat `lookup_var src s = SOME sw`)) >>
  disch_then (fn step =>
    qpat_assum `lookup_var dst s = SOME _`
      (mp_then (Pat `lookup_var dst _ = SOME _`) mp_tac step)) >>
  disch_then (drule_at (Pat `ptr_covers G tn dst s _`)) >>
  disch_then (drule_at (Pat `allocas_from lo s`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s`)) >>
  disch_then (drule_at (Pat `fn_has_code sa sb func`)) >>
  disch_then (fn step =>
    qpat_assum `evaluate_type tenv dty = SOME dtv`
      (mp_then (Pat `evaluate_type _ dty = SOME _`) mp_tac step)) >>
  disch_then (fn step =>
    qpat_assum `value_has_type dtv v`
      (mp_then (Pat `value_has_type dtv _`) mp_tac step)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qexistsl_tac [`u`,`G2`,`tn2`] >>
  `alloca_history func u` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK u,_,_)`
       (qspec_then `ARB` assume_tac) >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def, venom_state_component_equality]) >>
     simp[]) >>
  qpat_x_assum `w2n ((n2w addr):bytes32) = addr`
    (fn eq => rule_assum_tac (PURE_REWRITE_RULE [eq])) >>
  simp[struct_store_effects_def, expr_sim_full_endpoint_def, arithmeticTheory.ADD_COMM]
QED

Theory exprSimAbiEncodeTranslatedResources
Ancestors
  exprSimAbiEncodeProducerExecution exprSimAbiEncodeTranslatedZero
  exprSimAbiEncodeSourceMetadata abiEncoderAdmissible
  exprSimHypsDefs exprSimDefs loweringPosts exprSimAbiEncodeSourceSupplier
  exprSimAbiEncodePrefixWindow abiEncoderOpenInput abiEncoderWindow
  exprSimAbiEncodeNonwordResources exprSimAbiEncodeCapacity
  abiBuiltinAllocation abiBuiltinEncodeCode context exprLoweringProps
  venomMemDefs venomState venomInst compileEnv finite_map words list arithmetic

Theorem abi_encode_translated_nonword_source_split:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  ?w ct rv. eval_operand op s = SOME w /\
    source_rep (get_tenv cx) (expr_type e) ei ct /\
    abi_encoder_admissible ei /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory /\
    ((val_footprint tv v = 0 /\ (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc ct rv = []) \/
     (0 < val_footprint tv v /\ w2n w + val_footprint tv v <= s.vs_alloca_next))
Proof
  strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `!t v. evaluate_type (get_tenv cx) t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v` by
    metis_tac[abi_encode_body_evaluated_metadata] >>
  `?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `?ct rv. source_rep (get_tenv cx) (expr_type e) ei ct /\
     enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
     abi_encoder_open_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory` by
    (qpat_assum `ei = _` SUBST1_TAC >>
     irule abi_encode_translated_source_footprint >> simp[] >>
     qexists `get_tenv cx` >> simp[]) >>
  `abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory` by
    metis_tac[abi_encoder_open_input_window] >>
  `abi_encoder_admissible ei` by metis_tac[abi_encoder_translation_admissible] >>
  drule_all abi_encode_nonword_expr_bound >> strip_tac
  >- (`ei = AbiCopy 0 \/ ei = AbiComplex []` by
        (qpat_assum `ei = _` SUBST1_TAC >>
         irule abi_encode_translated_zero_descriptor >>
         qexistsl [`get_tenv cx`, `get_tenv cx`, `av`, `tv`, `v`] >> simp[]) >>
      `enc ct rv = []` by metis_tac[abi_encode_translated_zero_open_bytes] >>
      qexistsl [`w`, `ct`, `rv`] >> metis_tac[]) >>
  qexistsl [`w`, `ct`, `rv`] >> simp[] >>
  Cases_on `val_footprint tv v = 0` >> simp[] >>
  `ei = AbiCopy 0 \/ ei = AbiComplex []` by
    (qpat_assum `ei = _` SUBST1_TAC >>
     irule abi_encode_translated_zero_descriptor >>
     qexistsl [`get_tenv cx`, `get_tenv cx`, `av`, `tv`, `v`] >> simp[]) >>
  metis_tac[abi_encode_translated_zero_open_bytes]
QED

Theorem abi_encode_translated_nonword_phase_resources:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  fn_has_code sa ready func /\ fn_has_code ready body_end obs /\
  fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce sa ==>
  ?w ct rv p.
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    let mw = case mid of NONE => 0 | SOME _ => 32 in
    let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (expr_type e)+m) in
    let a = abi_builtin_allocate_state sa.cs_next_id outsz s in
    eval_operand op s = SOME w /\ enc ct rv = bytes /\
    source_rep (get_tenv cx) (expr_type e) ei ct /\ abi_encoder_admissible ei /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory /\
    ((val_footprint tv v = 0 /\ (ei = AbiCopy 0 \/ ei = AbiComplex []) /\ enc ct rv = []) \/
     (0 < val_footprint tv v /\ w2n w+val_footprint tv v <= s.vs_alloca_next)) /\
    alloca_inv a /\ alloca_room ctx func a /\
    FLOOKUP a.vs_allocas sa.cs_next_id = SOME (p,outsz) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    p+32+m+LENGTH bytes <= a.vs_alloca_next /\
    (0 < val_footprint tv v ==>
      w2n w+val_footprint tv v <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (p+32+m,LENGTH bytes) /\
      (w2n w+val_footprint tv v <= p+32 \/ p+32+mw <= w2n w)) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+32+m,LENGTH bytes) /\
    (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\
      FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+m,LENGTH bytes) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,m) (b,sz))
Proof
  strip_tac >> drule_all abi_encode_translated_nonword_source_split >>
  disch_then (qx_choose_then `w` (qx_choose_then `ct`
    (qx_choose_then `rv` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `(case mid0 of NONE => 0 | SOME _ => 4) =
   (case mid of NONE => 0 | SOME _ => 4)` by
    (Cases_on `mid0` >> fs[]) >>
  `(case mid0 of NONE => 0 | SOME _ => 32) =
   (case mid of NONE => 0 | SOME _ => 32)` by
    (Cases_on `mid0` >> fs[]) >>
  qpat_assum `(case mid0 of NONE => 0 | SOME _ => 4) = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_assum `(case mid0 of NONE => 0 | SOME _ => 32) = _`
    (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `(case mid of NONE => 0 | SOME _ => 4) = _` kall_tac >>
  qpat_x_assum `(case mid of NONE => 0 | SOME _ => 32) = _` kall_tac >>
  `0 < val_footprint tv v ==> w2n w+val_footprint tv v <= s.vs_alloca_next` by
    (qpat_x_assum `(_ = 0 /\ _) \/ _` mp_tac >> rw[] >> fs[]) >>
  drule_all abi_encode_nonword_setup_output >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv (abi_builtin_allocate_state _ outsz _)` >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,outsz))` by
    (qpat_x_assum `FLOOKUP a.vs_allocas _ = _` mp_tac >>
     simp[Abbr `a`, abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]) >>
  (`s.vs_alloca_next <= a.vs_alloca_next` by
    (simp[Abbr `a`, abi_builtin_allocate_state_def] >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >> simp[]) >>
  `p < dimword (:256) /\ (mid <> NONE ==> p+32 < dimword (:256)) /\
   p+32+(case mid of NONE => 0 | SOME _ => 4)+
     LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <= a.vs_alloca_next` by
    (fs[Abbr `outsz`] >> decide_tac) >>
  `0 < val_footprint tv v ==>
    w2n w+val_footprint tv v <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv v)
      (p+32+(case mid of NONE => 0 | SOME _ => 4),
       LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)) /\
    (w2n w+val_footprint tv v <= p+32 \/
     p+32+(case mid of NONE => 0 | SOME _ => 32) <= w2n w)` by
    (strip_tac >> Cases_on `mid` >>
     fs[Abbr `outsz`, venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl [`w`, `ct`, `rv`, `p`] >> simp_tac bool_ss [LET_THM] >>
  unabbrev_all_tac >>
  qpat_assum `enc ct rv = _` (fn th =>
    qpat_assum `(_ = 0 /\ _) \/ _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  asm_rewrite_tac [] >>
  conj_tac >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`) abi_encode_nonword_scratch_row >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (b,sz)`)) >>
  disch_then (qspecl_then [`w`, `tv`, `obs`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac []) >> strip_tac >>
  drule_all abi_encode_setup_scratch_slices >>
  strip_tac >> asm_rewrite_tac [] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p+32,_) (b,sz)` mp_tac >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p+32+_,_) (b,sz)` mp_tac >>
  Cases_on `mid` >> simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)
QED

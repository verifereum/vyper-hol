Theory createCtorEncoderLengthMods
Ancestors
  createCtorEncoderLength createExprSizeExitDefsMods
  bodyFullExtCallDirectEncode bodyFullExtCallDirectRow bodyFullExtCallPosList
  bodyFullExtCallDirectState abiEncodeSnapshotOperandProps abiEncodeValuesMetadata abiEncodeValuesRun
  exprSimHyps assignPlaceOperandFacts exprSafeOperand abiBuiltinAllocation
  abiEncodeArgsCase entryDecodeStaticProps abiDecoderMembers vyperABIRoundtrip
  exprBodyPreProps context emitHelper loweringShapeRules aggregateEvaluatedLayout
  vyperTypeArgFits emitHelperProps exprLowering loweringPosts exprSimWordArgs
  compileEnv contractABI vyperABI vyperValue fragGasOriginPtr
  vyperStorageTrace venomState venomInst list rich_list pair arithmetic
  typedMemoryCopy exprSimIfExpCompat exprSimSource vyperTypeSystem
  exprSimHypsDefs allocLimits
  createCtorEncoderFoldMods createCtorEncoderPhaseMods createCtorEncoderWordRowMods
  createCtorEncoderDynamicRowMods createCtorEncoderStaticRowMods createCtorEncoderRestoreMods
  createCtorEncoderSavedAdvanceMods createCtorEncoderOperandMods
Libs pairLib horizonTypeLib

Theorem ctor_encoder_physical_size_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ann ==>
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2**64 /\
  (~is_word_type (lowered_value_type ce e) ==> ~is_word_type (expr_type e))
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by
    metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     EVERY (\(fname,fty,sz). !rt. evaluate_type (get_tenv cx) fty = SOME rt ==>
                                  sz = type_memory_size rt) fields)` by
    (fs[expr_sim_inv_mods_def] >>
     qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
       (fn th => metis_tac[th])) >>
  `!ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
           type_memory_bytes ce ty = type_memory_size rt` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists `get_tenv cx` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
     >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
         gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
         `!f sg. FLOOKUP env.fn_sigs f = SOME sg ==>
                 ce.ce_func_return_type (nsid_to_string f) = sg.ret_ty` by
           metis_tac[expr_sim_inv_mods_return_type] >>
         first_x_assum (drule_then SUBST1_TAC) >>
         fs[type_widens_to_def, ifexp_arg_type_fits_refl]) >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
             well_formed_type env.type_defs t` by
       metis_tac[env_consistent_var_type_evaluates, well_formed_type_def] >>
     `!f sg. FLOOKUP env.fn_sigs f = SOME sg ==>
             ce.ce_func_return_type (nsid_to_string f) = sg.ret_ty` by
       metis_tac[expr_sim_inv_mods_return_type] >>
     mp_tac (Q.SPECL [`ce`,`e`,`env`] ifexp_lowered_type_classify) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
     metis_tac[ifexp_arg_type_fits_refl]) >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by metis_tac[] >>
  `is_word_type (lowered_value_type ce e) = is_word_type (expr_type e)` by
    metis_tac[arg_type_fits_word_type] >>
  asm_rewrite_tac[] >> Cases_on `is_word_type (expr_type e)` >> gvs[]
  >- (`type_memory_bytes ce (lowered_value_type ce e) = 32` by
        metis_tac[word_type_dec_sizes] >>
      `type_memory_size tv = 32` by metis_tac[] >> simp[]) >>
  `type_alloc_ok ce (expr_type e)` by
    metis_tac[expr_body_pre_mods_def, alloc_limits_expr_type_alloc_ok] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size ann` by metis_tac[] >>
  drule (cj 1 abi_args_fits_memory_bytes) >>
  disch_then (qspec_then `ce` assume_tac) >>
  `type_memory_size tv <= type_memory_size ann` by metis_tac[] >>
  `type_memory_size ann < 2**64` by fs[type_alloc_ok_def] >>
  qpat_x_assum `type_memory_size ann < _` mp_tac >> simp[] >> decide_tac
QED

Theorem ctor_positional_row_at_mods[local]:
  extcall_positional_post_mods mods keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
    H (INL vs) ee G tn s ==>
  !i e sv v. i < LENGTH args /\ e = EL i args /\ sv = EL i svs /\ v = EL i vs ==>
  stmt_state_rel H ctx func ce cx ee s /\
  expr_sim_inv_mods mods ce cx env ee /\
  vv_storage_live H cx sv ee s /\
  ?si sm ss vv raw copy.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,ss) /\
    local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\
    sm.cs_next_id <= se.cs_next_id /\ ss.cs_next_var <= se.cs_next_var /\
    ss.cs_next_id <= se.cs_next_id /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
    ((?tag op. sv = StackValue tag op) \/
     (?p. sv = LocatedValue (lowered_value_type ce e) p /\
          ~is_word_type (lowered_value_type ce e) /\ p.ptr_location = LocMemory) \/
     (?p. sv = LocatedValue (lowered_value_type ce e) p /\
          ~is_word_type (lowered_value_type ce e) /\ p.ptr_location <> LocMemory /\
          lowered_value_type ce e = expr_type e /\ sv = vv)) /\
    read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods ce cx (lowered_value_type ce e) raw sv ee s /\
    vv_at ce cx (lowered_value_type ce e) si ss ee raw sv s /\
    ptr_vv_ok cx (lowered_value_type ce e) raw sv ee G tn s /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw sv s /\
    ((case sv of StackValue tag op => ~is_word_type (lowered_value_type ce e)
               | LocatedValue tag p => p.ptr_location = LocMemory) ==>
     ptr_buf_ok ce e (vv_operand sv) G s)
Proof
  simp_tac bool_ss [extcall_positional_post_mods_def, sumTheory.INL_11] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_assum `LIST_REL _ (ZIP (args,svs)) vs`
    (qspec_then `i` mp_tac o cj 2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  simp[LENGTH_ZIP, EL_ZIP] >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
       (MAP_EVERY assume_tac o CONJUNCTS))
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`si`,`sm`,`ss`,`vv`,`raw`,`copy`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  Cases_on `EL i svs` >> gvs[vv_operand_def]
QED

Theorem ctor_encoder_length_witness_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre_mods mods ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post_mods mods keep DF lo d ctx func ce cx env [] args svs sa se es s0 G0 tn0
      H (INL vs) ee G tn s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok_mods H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  rows = ZIP (svs,MAP (lowered_value_type ce) args) /\
  ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
  vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-dst_offset /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >>
     qhdtm_assum `valid_horizon` (fn hv =>
       qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
         (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_mods_def, sumTheory.INL_11]
          o C MATCH_MP hv)) >>
     first_assum ACCEPT_TAC) >>
  `!a c ids outs v Gv tv z Gz tz.
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a v Gv tv /\
    ci_mono a c /\ window_phase ctx func a c ids outs v z /\ abi_encode_exec_frame func v z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP Gz x = FLOOKUP Gv x /\ op_taint tz (Var x) = op_taint tv (Var x)) /\
    tz.t_stor = tv.t_stor /\ tz.t_trans = tv.t_trans /\ tz.t_imm = tv.t_imm /\
    shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
    EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
    (!aid. aid IN shared INSERT ids ==>
      ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
    (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
      (!aid p n. aid IN ids /\ FLOOKUP z.vs_allocas aid = SOME (p,n) ==>
        i < p \/ p+n <= i) /\ i IN tz.t_mem ==> i IN tv.t_mem) ==>
    (pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz` by suspend "phase" >>
  irule ctor_encoder_saved_fold_mods >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`ats`,`avs`,`head_lengths ats 0`,`rows`,`st`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  suspend "row_index"
QED

Resume ctor_encoder_length_witness_mods[phase]:
  qx_genl_tac [`a`,`c`,`ids`,`outs`,`v`,`Gv`,`tv`,`z`,`Gz`,`tz`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule ctor_encoder_saved_phase_mods >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `H0` assume_tac) >>
  qexistsl_tac [`tv`,`explicit`,`PG`,`H0`] >> qexists_tac `Gv` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume ctor_encoder_length_witness_mods[row_index]:
  qx_genl_tac [`ci`,`cr`] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qx_genl_tac [`i`,`a`,`c`,`r`,`Gr`,`tr`,`cursor`,`slot`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH svs = LENGTH args` by
    (qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
       (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. _ ==> extcall_positional_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_mods_def, sumTheory.INL_11])) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH rows = LENGTH args /\ LENGTH ats = LENGTH avs /\ LENGTH vs = LENGTH args` by
    (conj_tac >- simp[LENGTH_ZIP] >>
     drule vyper_to_abi_list_EL >> simp[] >> metis_tac[LIST_REL_LENGTH]) >>
  `i < LENGTH args /\ i < LENGTH ats /\ i < LENGTH vs` by
    metis_tac[LIST_REL_LENGTH] >>
  qabbrev_tac `e = EL i args` >>
  qabbrev_tac `sv = EL i svs` >>
  qabbrev_tac `v = EL i vs` >>
  qabbrev_tac `h = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows))` >>
  qabbrev_tac `off = head_lengths ats 0 + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
  `EL i rows = (sv,lowered_value_type ce e) /\
   EL i ats = vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)` by
    simp[Abbr `sv`, Abbr `e`, EL_ZIP, EL_MAP, vyper_to_abi_types_MAP] >>
  `vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME (EL i avs)` by
    (drule vyper_to_abi_list_EL >> simp[Abbr `v`, Abbr `e`, EL_MAP]) >>
  `h = LENGTH (FLAT (abi_tuple_heads (head_lengths ats 0) 0 (TAKE i ats) (TAKE i avs))) /\
   head_lengths ats 0 <= off /\ off <= LENGTH bytes /\
   h + abi_member_head_size (EL i ats) <= head_lengths ats 0 /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <= LENGTH bytes) /\
   (~is_dynamic (EL i ats) ==> LENGTH (enc (EL i ats) (EL i avs)) = abi_member_head_size (EL i ats)) /\
   abi_encoder_layout_valid (EL i ats) (EL i avs) /\
   LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
    (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
       abi_encode_values_index_bounds) >>
     simp_tac bool_ss [] >>
     conj_tac >- (qpat_assum `bytes = enc _ _` (rewrite_tac o single)) >>
     conj_tac >- simp_tac bool_ss [Abbr `off`] >>
     conj_tac >- qpat_assum `LIST_REL abi_encoder_layout_valid ats avs` ACCEPT_TAC >>
     qexistsl_tac [`rows`,`ce.ce_struct_fields`] >>
     conj_tac
     >- (qpat_assum `LENGTH rows = LENGTH args` (rewrite_tac o single) >>
         qpat_assum `i < LENGTH args` ACCEPT_TAC) >>
     conj_tac >- simp_tac bool_ss [Abbr `h`] >>
     qpat_assum `LIST_REL _ rows ats` ACCEPT_TAC) >>
  `off <= capacity-dst_offset /\
   (is_dynamic (EL i ats) ==> off + LENGTH (enc (EL i ats) (EL i avs)) <= capacity-dst_offset)` by
    (conj_tac >- decide_tac >> strip_tac >>
     qpat_assum `is_dynamic _ ==> off + _ <= LENGTH bytes` (drule_then assume_tac) >>
     decide_tac) >>
  `compile_abi_encode_value_rows ce (Var dst) cursor h [(sv,lowered_value_type ce e)] a = ((),c)` by
    (qpat_assum `EL i rows = _` (fn th => rewrite_tac [GSYM th]) >>
     simp_tac bool_ss [Abbr `h`] >> first_assum ACCEPT_TAC) >>
  suspend "row_inputs"
QED

Resume ctor_encoder_length_witness_mods[row_inputs]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx sv ee s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> extcall_positional_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_then (qspecl_then [`i`,`e`,`sv`,`v`] mp_tac) ctor_positional_row_at_mods >>
     (impl_tac >- simp[Abbr `e`, Abbr `sv`, Abbr `v`]) >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. _ ==> extcall_positional_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `H0` (drule_then assume_tac)) >>
  drule_then (qspecl_then [`i`,`e`,`sv`,`v`] mp_tac) ctor_positional_row_at_mods >>
  (impl_tac >- simp[Abbr `e`, Abbr `sv`, Abbr `v`]) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 kall_tac (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`raw`,`copy`]
      (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `MEM e args` by simp[Abbr `e`, EL_MEM] >>
  qpat_assum `!e. MEM e args ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!i. i < LENGTH args ==> ?tv ann. _`
    (qspec_then `i` (drule_then mp_tac)) >>
  qpat_assum `Abbrev (e = _)`
    (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (v = _)`
    (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (qx_choosel_then [`tv`,`ann`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_encoder_physical_size_mods >> strip_tac >>
  `!l. vv_operand sv <> Label l` by
    (`well_typed_expr env e` by metis_tac[expr_body_pre_mods_well_typed] >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
        ?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
       fs[expr_sim_inv_mods_def] >>
     drule_all_then assume_tac ctor_encoder_compile_not_label >>
     drule_all abi_snapshot_operand_not_label >> simp[]) >>
  `se.cs_next_id <= shared /\ shared < st.cs_next_id /\ dst_offset <= capacity` by
    (qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st _ _ _`
       (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `shared <> st.cs_next_id /\ se.cs_next_id <= st.cs_next_id` by decide_tac >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- suspend "word_row" >>
  suspend "aggregate_row"
QED

Resume ctor_encoder_length_witness_mods[word_row]:
  irule ctor_encoder_word_row_mods >>
  qpat_assum `compile_abi_encode_value_rows ce (Var dst) cursor h [(sv,lowered_value_type ce e)] a = _`
    (irule_at Any) >>
  qpat_assum `compile_expr ce (expr_type e) e si = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv ce copy _ sm = _` (irule_at Any) >>
  qpat_assum `read_result cx raw ee = _` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) (lowered_value_type ce e) = _` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >>
  qexistsl_tac [`off`,`inst`,`EL i avs`,`EL i ats`,`H0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
  >> simp_tac bool_ss [Abbr `off`]
QED

Resume ctor_encoder_length_witness_mods[aggregate_row]:
  qabbrev_tac `ty = lowered_value_type ce e` >>
  `!t rt. evaluate_type (get_tenv cx) t = SOME rt ==>
          type_memory_bytes ce t = type_memory_size rt` by
    (`!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
       EVERY (\(fname,fty,sz). !rty. evaluate_type (get_tenv cx) fty = SOME rty ==>
                                  sz = type_memory_size rty) fields` by
       (fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
        qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
          (drule_then (ACCEPT_TAC o cj 2))) >>
     rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `get_tenv cx` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!tag p. sv = LocatedValue tag p ==> tag = ty` by
    (qpat_assum `(?tag op. sv = StackValue tag op) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `sv` >> simp[] >> metis_tac[]) >>
  `(vv_location sv = SOME LocMemory ==> ~is_word_type ty)` by simp[] >>
  `pbase+dst_offset+h <= pbase+capacity /\ pbase+dst_offset+off <= pbase+capacity` by
    (conj_tac >- decide_tac >> decide_tac) >>
  `!su sb src ru Gru tru.
    unwrap_value ce sv su = (src,sb) /\ fn_has_code su sb func /\ ci_mono su sb /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix su ru Gru tru /\
    abi_encode_values_prefix_at ats avs (head_lengths ats 0) (pbase+dst_offset) cursor
      st.cs_next_id slot i su ru Gru tru ==>
    ?z Gz tz.
      (pure_frame ce func ee su ru z /\ wb_frame ce ee ee su ru z) /\
      abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix sb z Gz tz /\
      abi_encode_values_prefix_at ats avs (head_lengths ats 0) (pbase+dst_offset) cursor
        st.cs_next_id slot i sb z Gz tz /\
      expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
      expr_store_bound cx ty v src z /\ (!x. src = Var x ==> not_fresh_at sb x) /\
      (!x. not_fresh_at su x ==>
        lookup_var x z = lookup_var x ru /\ FLOOKUP Gz x = FLOOKUP Gru x /\
        op_taint tz (Var x) = op_taint tru (Var x)) /\
      (?first last. expr_val_at ce cx ty first last ee v src z /\
        last.cs_next_id <= sb.cs_next_id /\
        (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (ru,Gru,tru) [] (OK z,Gz,tz)` by
    suspend "restore" >>
  Cases_on `is_dynamic (EL i ats)`
  >- suspend "dynamic_row" >>
  suspend "static_row"
QED

Resume ctor_encoder_length_witness_mods[dynamic_row]:
  irule ctor_encoder_dynamic_row_mods >>
  qpat_assum `compile_abi_encode_value_rows ce (Var dst) cursor h [(sv,ty)] a = _`
    (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (irule_at Any) >>
  qpat_assum `vyper_to_abi (get_tenv cx) ty v = _` (irule_at Any) >>
  qexistsl_tac [`cr`,`off`,`inst`,`ci`,`EL i ats`,`H0`] >>
  `off + LENGTH (enc (EL i ats) (EL i avs)) <= capacity - dst_offset` by
    (qpat_assum `is_dynamic _ ==> off + _ <= capacity - dst_offset`
      (drule_then ACCEPT_TAC)) >>
  simp_tac bool_ss [Abbr `off`] >> asm_rewrite_tac[]
QED

Resume ctor_encoder_length_witness_mods[static_row]:
  irule ctor_encoder_static_row_mods >>
  qpat_assum `compile_abi_encode_value_rows ce (Var dst) cursor h [(sv,ty)] a = _`
    (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (irule_at Any) >>
  qpat_assum `vyper_to_abi (get_tenv cx) ty v = _` (irule_at Any) >>
  qexistsl_tac [`off`,`inst`,`EL i ats`,`H0`] >>
  qpat_x_assum `ats = vyper_to_abi_types _ _` kall_tac >>
  simp_tac bool_ss [Abbr `off`] >> asm_rewrite_tac[] >>
  qx_genl_tac [`su`,`sb`,`sop`,`ru`,`Gru`,`tru`] >> disch_tac >>
  qpat_assum `!su sb src ru Gru tru. unwrap_value ce sv su = _ /\ _ ==> _`
    (qspecl_then [`su`,`sb`,`sop`,`ru`,`Gru`,`tru`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`q`,`Gq`,`tq`] >> asm_rewrite_tac[] >>
  qpat_assum `?first last. expr_val_at ce cx ty first last ee v sop q /\ _`
    (qx_choosel_then [`first`,`last`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`first`,`last`] >> asm_rewrite_tac[]
QED

Resume ctor_encoder_length_witness_mods[restore]:
  qx_genl_tac [`su`,`sb`,`sop`,`ru`,`Gru`,`tru`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.INST [`saved` |-> `sv`, `u` |-> `ru`, `Gu` |-> `Gru`, `tu` |-> `tru`]
    ctor_encoder_saved_advance_current_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?z Gz tz.
      (pure_frame ce func ee su ru z /\ wb_frame ce ee ee su ru z) /\
      abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix sb z Gz tz /\
      abi_encode_values_prefix_at ats avs (head_lengths ats 0) (pbase+dst_offset) cursor
        st.cs_next_id slot i sb z Gz tz /\
      expr_val_rel cx ty v sop z /\ ptr_val_ok cx ty v sop Gz tz z /\
      expr_store_bound cx ty v sop z /\ (!x. sop = Var x ==> not_fresh_at sb x) /\
      (!x. not_fresh_at su x ==>
        lookup_var x z = lookup_var x ru /\ FLOOKUP Gz x = FLOOKUP Gru x /\
        op_taint tz (Var x) = op_taint tru (Var x)) /\ z.vs_labels = ru.vs_labels /\
      (?first last. expr_val_at ce cx ty first last ee v sop z /\
        last.cs_next_id <= sb.cs_next_id /\
        (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (ru,Gru,tru) [] (OK z,Gz,tz)` suffices_by
    (disch_then (qx_choosel_then [`z`,`Gz`,`tz`]
       (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
     qexistsl_tac [`z`,`Gz`,`tz`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule ctor_encoder_restore_row_from_advanced_mods >>
  qpat_assum `unwrap_value ce sv su = _` (irule_at Any) >>
  qpat_assum `compile_expr ce (expr_type e) e si = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv ce copy _ sm = _` (irule_at Any) >>
  qpat_assum `read_result cx raw ee = _` (irule_at Any) >>
  qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (irule_at Any) >>
  qexistsl_tac [`inst`,`cr`,`ci`,`H0`] >>
  `pbase + dst_offset + LENGTH (FLAT (abi_tuple_heads (head_lengths ats 0) 0
      (TAKE i ats) (TAKE i avs))) <= pbase + capacity` by
    (qpat_assum `h = LENGTH _` (pure_once_rewrite_tac o single o GSYM) >>
     qpat_assum `pbase + dst_offset + h <= _` ACCEPT_TAC) >>
  `pbase + dst_offset + head_lengths ats 0 + LENGTH (FLAT (abi_tuple_tails
      (TAKE i ats) (TAKE i avs))) <= pbase + capacity` by
    (pure_once_rewrite_tac [GSYM arithmeticTheory.ADD_ASSOC] >>
     qpat_assum `Abbrev (off = _)`
       (pure_once_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `pbase + dst_offset + off <= _` ACCEPT_TAC) >>
  `ty = lowered_value_type ce e` by simp_tac bool_ss [Abbr `ty`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ctor_encoder_length_witness_mods

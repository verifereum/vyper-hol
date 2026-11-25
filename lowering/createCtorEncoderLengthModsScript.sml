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
  cheat
QED

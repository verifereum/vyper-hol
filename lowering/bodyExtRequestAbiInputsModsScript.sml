(* ABI typing before the linked external request's selector store. *)
Theory bodyExtRequestAbiInputsMods
Ancestors
  exprBodyPreProps exprSimHypsDefs vyperTypeInvariants vyperTypeSystem
  allocLimits exprLowering abiTypeBoundProps vyperABI contractABI words
  exprSimAbiEncodePlanTranslation typedMemoryCopy structFieldsProps logDataPacking
  bodyCopyArgReadTypesMods bodyCopyReadPhysicalTypeMods vyperTypeArgFits
  vyperInterpreter vyperTypeExprSoundness placeRelayoutSemantic typedCopyCompatibility
  aggregateEvaluatedLayout entryDecodeStaticProps vyperArith finite_map list
  exprSimHyps[qualified] abiEncodeArgsCase[qualified]
  bodyExtPosSavedRowMods exprReasonOperand exprSafeOperand abiBuiltinAllocation
  loweringShapeRules compileEnv context exprSimExtCallCase bodyPtrDefs loweringPosts
  ptrDiscipline venomState venomMemDefs freshWrites assignBasePtrBoundary
  vyperTypeExtCallSoundness vyperTypeExtCallCore exprSimProps valueEncodingTyping
  abiEncodeMaterialize loweringHalt
Libs pairLib

Theorem ext_request_signature_mods[local]:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr) es /\
  xs = TAKE (LENGTH ats) tail ==>
  env.type_defs = get_tenv cx /\
  EVERY (assignable_type (get_tenv cx)) ats /\
  EVERY (abi_decode_bytes_widths (get_tenv cx)) ats /\
  EVERY (well_formed_type (get_tenv cx)) ats /\
  arg_types_fit (MAP expr_type xs) ats /\
  SUM (MAP (type_memory_bytes cenv) (MAP (lowered_value_type cenv) xs)) < 2**64 /\
  MAX (abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)))
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32 < 2**64 /\
  cenv.ce_method_id fname ats = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) ats)))
Proof
  strip_tac >> drule expr_body_pre_mods_inv >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >> strip_tac >>
  `alloc_limits_expr cenv (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr)` by
    fs[expr_body_pre_mods_def] >>
  pop_assum mp_tac >> simp[Once alloc_limits_expr_def, ext_call_alloc_ok_def] >> strip_tac >>
  simp[] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
  simp[expr_sim_inv_mods_def]
QED

Theorem ext_request_memory_layout[local]:
  expr_sim_inv_mods mods cenv cx env es ==>
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv)
Proof
  simp[expr_sim_inv_mods_def] >> strip_tac >> simp[] >> rpt strip_tac >>
  irule typed_copy_memory_size >> qexists `get_tenv cx` >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem ext_request_encoding_plans[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  EVERY (assignable_type (get_tenv cx)) tys /\
  SUM (MAP (type_memory_bytes cenv) tys) < 2**64 ==>
  abi_size_bound cenv.ce_struct_fields (TupleT tys) =
    vyper_abi_size_bound (get_tenv cx) (TupleT tys) /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!ty. MEM ty tys ==> abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty))
Proof
  strip_tac >> drule ext_request_memory_layout >> strip_tac >>
  `!ty. MEM ty tys ==> ?tv. evaluate_type (get_tenv cx) ty = SOME tv` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_assum drule >>
     disch_then (mp_tac o MATCH_MP assignable_type_well_formed) >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) tys)` by
    simp[IS_SOME_OPT_MMAP, EVERY_MAP, EVERY_MEM, optionTheory.IS_SOME_EXISTS] >>
  pop_assum (qx_choose_then `tvs` assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  `SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs` by
    (irule tuple_memory_bytes_size >> qexists `get_tenv cx` >> simp[]) >>
  `type_slot_size_list tvs < 2**64` by
    (fs[cj 4 log_memory_slot_sizes] >> decide_tac) >>
  `type_slot_size_list tvs < dimword (:256)` by
    (irule lt_dimword_256 >> qexists `64` >> simp[]) >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    simp[cj 2 vyperValueTheory.evaluate_type_def, vyperValueTheory.evaluate_types_OPT_MMAP,
         vyperValueTheory.type_slot_size_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  simp[] >> conj_tac
  >- (`abi_sfields_consistent_upto (type_value_size (TupleTV tvs))
         cenv.ce_struct_fields (get_tenv cx)` by simp[abi_sfields_consistent_upto_init] >>
      drule_all abi_props_vyper_upto >> simp[]) >>
  rpt strip_tac >> irule abi_encode_translated_plan >>
  fs[EVERY_MEM] >> qexists `get_tenv cx` >> simp[SUBMAP_REFL]
QED

Theorem ext_request_replay_lowered[local]:
  expr_sim_inv_mods mods cenv cx env pos /\
  (!e s. MEM e xs /\ expr_sim_inv_mods mods cenv cx env s ==>
    expr_body_pre_mods mods cenv cx env e s) /\
  eval_exprs cx xs pos = (INL vs,ee) ==>
  LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs
Proof
  strip_tac >> irule copy_arg_read_types_from_members_mods >>
  qexistsl [`cx`,`ee`,`mods`,`pos`] >> simp[] >> reverse conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >>
      first_assum (drule_all_then (mp_tac o REWRITE_RULE[expr_body_pre_mods_def])) >> simp[]) >>
  rpt strip_tac >>
  first_assum (drule_all_then (strip_assume_tac o REWRITE_RULE[expr_body_pre_mods_def])) >>
  drule_all copy_read_lowered_type_mods >> simp[]
QED

(* The source may be narrower than the formal; retain its own evaluated layout. *)
Theorem ext_request_row_type[local]:
  expr_body_pre_mods mods cenv cx env e pos /\
  env.type_defs = get_tenv cx /\
  value_runtime_typed env (lowered_value_type cenv e) v /\
  arg_type_fits (expr_type e) formal /\
  assignable_type (get_tenv cx) formal /\
  well_formed_type (get_tenv cx) formal ==>
  arg_type_fits (lowered_value_type cenv e) formal /\
  assignable_type (get_tenv cx) (lowered_value_type cenv e) /\
  (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
  ?tv param_tv.
    evaluate_type (get_tenv cx) formal = SOME param_tv /\ value_has_type param_tv v /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ value_has_type tv v
Proof
  strip_tac >> drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl [`cx`,`env`,`pos`,`mods`] >> simp[]) >>
  `arg_type_fits (lowered_value_type cenv e) formal` by
    metis_tac[cj 1 arg_type_fits_trans] >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[value_runtime_typed_def] >>
  disch_then (qx_choose_then `tv` strip_assume_tac) >>
  `?ptv. evaluate_type (get_tenv cx) formal = SOME ptv` by
    fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `assignable_type (get_tenv cx) (lowered_value_type cenv e)` by
    (qpat_assum `arg_type_fits (lowered_value_type cenv e) formal`
       (mp_tac o MATCH_MP (cj 1 arg_type_fits_source_assignable)) >>
     disch_then (qspec_then `get_tenv cx` irule) >>
     fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
    (drule ext_request_memory_layout >> simp[]) >>
  `value_has_type ptv v` by metis_tac[cj 1 arg_type_fits_value_has_type] >>
  `type_alloc_ok cenv (expr_type e)` by
    (irule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_mods_def]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv (expr_type e)` by
    metis_tac[cj 1 abiEncodeArgsCaseTheory.abi_args_fits_memory_bytes] >>
  `type_memory_size tv < 2**64` by
    (Cases_on `is_word_type (expr_type e)` >>
     fs[type_alloc_ok_def, cj 3 word_type_dec_sizes] >> decide_tac) >>
  fs[] >> metis_tac[arg_type_fits_word_type]
QED

Theorem request_compiled_operand_not_label[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) ==>
  !l. vv_operand vv <> Label l
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def] >> strip_tac >>
  drule_all compile_expr_reason_uniform >>
  disch_then (qspec_then `expr_type e` mp_tac) >>
  simp[reason_uniform_shape_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]
QED

Theorem request_saved_operand_not_label[local]:
  compile_snapshot_vv cenv copy (ext_call_arg_value ty vv) sm = (sv,ss) /\
  (!l. vv_operand vv <> Label l) ==>
  !l. vv_operand sv <> Label l
Proof
  strip_tac >>
  `vv_operand (ext_call_arg_value ty vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def,vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def,comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def,mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abi_builtin_alloc_buffer_shape >> simp[emit_op_eq]) >>
  strip_tac >> gvs[]
QED

Theorem ext_request_indexed_types[local]:
  expr_sim_inv_mods mods cenv cx env pos /\ env.type_defs = get_tenv cx /\
  (!e s. MEM e xs /\ expr_sim_inv_mods mods cenv cx env s ==>
    expr_body_pre_mods mods cenv cx env e s) /\
  LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  arg_types_fit (MAP expr_type xs) ats /\
  EVERY (assignable_type (get_tenv cx)) ats /\
  EVERY (well_formed_type (get_tenv cx)) ats ==>
  LENGTH xs = LENGTH ats /\ LENGTH vs = LENGTH xs /\
  (!i. i < LENGTH xs ==>
    let e = EL i xs; v = EL i vs; formal = EL i ats in
    expr_body_pre_mods mods cenv cx env e pos /\
    arg_type_fits (lowered_value_type cenv e) formal /\
    assignable_type (get_tenv cx) (lowered_value_type cenv e) /\
    (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
    ?tv param_tv.
      evaluate_type (get_tenv cx) formal = SOME param_tv /\ value_has_type param_tv v /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v)
Proof
  simp[arg_types_fit_LIST_REL, LIST_REL_EL_EQN, EL_MAP, EVERY_EL] >>
  strip_tac >> simp[] >> gen_tac >> disch_tac >>
  `expr_body_pre_mods mods cenv cx env (EL i xs) pos` by
    (first_x_assum irule >> simp[EL_MEM]) >>
  `i < LENGTH ats` by fs[] >>
  `i < LENGTH xs` by fs[] >>
  `value_runtime_typed env (lowered_value_type cenv (EL i xs)) (EL i vs)` by metis_tac[] >>
  `arg_type_fits (expr_type (EL i xs)) (EL i ats)` by metis_tac[] >>
  `assignable_type (get_tenv cx) (EL i ats)` by metis_tac[] >>
  `well_formed_type (get_tenv cx) (EL i ats)` by metis_tac[] >>
  drule_all ext_request_row_type >> simp[]
QED

Theorem ext_request_indexed_row_operand[local]:
  expr_body_pre_mods mods cenv cx env e pos /\
  ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G tn t ==>
  !l. vv_operand sv <> Label l
Proof
  simp[ext_pos_saved_row_mods_def] >> strip_tac >>
  drule_all request_compiled_operand_not_label >> strip_tac >>
  drule_all request_saved_operand_not_label >> simp[]
QED

(* Two preservation intervals, before and after the positional cut. *)
Theorem request_target_ready[local]:
  safe_operand s1 ao /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= s5.cs_next_var /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
  ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng /\
  (!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==>
     lookup_var x zg = SOME w) /\
  zg.vs_labels = u.vs_labels /\
  eval_operand ao u = SOME aw /\ w2w aw = target /\
  ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t ==>
  safe_operand s5 ao /\ op_taint tng ao = {} /\
  (?w. eval_operand ao zg = SOME w /\ w2w w = target)
Proof
  strip_tac >> conj_tac
  >- (irule safe_operand_mono >> qexists `s1` >> simp[] >> decide_tac) >>
  fs[safe_operand_def,ptr_val_ok_def,ghost_kept_at_def] >>
  Cases_on `ao` >> fs[op_taint_def,eval_operand_def] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem request_value_ready[local]:
  ext_call_opts_ok stat opts /\
  (case ext_call_kwarg EKValue opts kws of
     NONE => vo = NONE
   | SOME v => ?op w. vo = SOME op /\ eval_operand op z = SOME w /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       dest_NumV v = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
     op_taint tng (Var x) = op_taint tn3 (Var x)) /\
  zg.vs_labels = z.vs_labels ==>
  let value = option_CASE vo (Lit 0w) I;
      value_opt = if stat then NONE else
        option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV
  in (stat <=> value_opt = NONE) /\
     (?vw. eval_operand value zg = SOME vw /\
           w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
     op_taint tng value = {}
Proof
  simp[] >> strip_tac >> Cases_on `ext_call_kwarg EKValue opts kws`
  >- (Cases_on `stat` >> gvs[eval_operand_def,op_taint_def]) >>
  `~stat` by
    (strip_tac >> fs[ext_call_opts_ok_def] >> drule (INST_TYPE [``:'b`` |-> ``:value``] ext_call_kwarg_not_mem) >>
     simp[] >> qexists `kws` >> simp[]) >>
  gvs[] >> rename1 `eval_operand op z = SOME w` >>
  Cases_on `op` >> gvs[eval_operand_def,op_taint_def]
QED

Theorem request_default_cell[local]:
  (!x. op = Var x ==> not_fresh_at s3 x) /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
    FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
  zg.vs_labels = z.vs_labels /\ zg.vs_memory = z.vs_memory /\
  zg.vs_allocas = z.vs_allocas /\ tng.t_mem = tn3.t_mem /\
  s3.cs_next_id <= s5.cs_next_id /\
  ptr_mem_ok cx dt v op G3 tn3 z /\ ptr_buf_ok cenv e op G3 z /\
  eval_operand op z = SOME w /\
  FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s3.cs_next_id ==>
  eval_operand op zg = SOME w /\ ptr_mem_ok cx dt v op Gg tng zg /\
  ptr_buf_ok cenv e op Gg zg /\
  FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s5.cs_next_id
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `eval_operand op zg = eval_operand op z` by
    (Cases_on `op` >> fs[eval_operand_def]) >>
  `!x. op = Var x ==> FLOOKUP Gg x = FLOOKUP G3 x` by metis_tac[] >>
  simp[] >> rpt conj_tac
  >- (simp[ptr_mem_ok_def] >> gen_tac >> disch_tac >>
      qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
      disch_then drule >> simp[] >> metis_tac[])
  >- (simp[ptr_buf_ok_def] >> disch_tac >>
      qpat_assum `ptr_buf_ok _ _ _ _ _`
        (mp_tac o REWRITE_RULE [ptr_buf_ok_def]) >>
      disch_then drule >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem request_memory_default_ready[local]:
  type_widens_to (get_tenv cx) dt rt /\
  rt <> NoneT /\ evaluate_type (get_tenv cx) dt = SOME tv /\
  evaluate_type (get_tenv cx) rt = SOME rtv /\
  value_has_type tv v /\ value_has_type rtv v /\ ~is_word_type dt /\
  ptr_mem_ok cx dt v op G tn t /\ eval_operand op t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
  alloca_next_valid t ==>
  extcall_default_ready cx rt T op dt (SOME v) t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `val_wf tv v /\ val_wf rtv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  `w2n w + val_footprint tv v <= t.vs_alloca_next` by
    (fs[alloca_next_valid_def] >>
     `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
     `w2n w + type_memory_size tv <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  simp[extcall_default_ready_def,expr_val_rel_def] >>
  fs[ptr_mem_ok_def] >> metis_tac[mem_agree_outside_def]
QED

Theorem request_selected_default[local]:
  !ks xs vs.
    MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
    LIST_REL (\e v. value_runtime_typed env (expr_type e) v) xs vs /\
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
    ext_call_kwarg EKDefault ks vs = SOME v ==>
    ?e. ext_call_kwarg EKDefault ks xs = SOME e /\ MEM e xs /\ expr_type e = rt /\
        value_runtime_typed env rt v /\
        value_runtime_typed env (lowered_value_type cenv e) v
Proof
  Induct >- simp[ext_call_kwarg_def] >>
  Cases_on `xs` >> Cases_on `vs` >> simp[ext_call_kwarg_def,ext_call_kw_type_def] >>
  rpt strip_tac >> gvs[] >> rename1 `expr_type _ = ext_call_kw_type rt k` >>
  Cases_on `k = EKDefault` >> gvs[ext_call_kw_type_def] >> metis_tac[]
QED

Theorem request_default_packet[local]:
  env.type_defs = get_tenv cx /\ expr_sim_inv_mods mods cenv cx env kw_in /\
  (!e st. MEM e kw_es /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st) /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v) kw_es kws /\
  LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) kw_es kws /\
  MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts /\
  (rt = NoneT ==> ext_call_kwarg EKDefault opts kws = NONE) /\
  (case ext_call_kwarg EKDefault opts kws of
     NONE => def = NONE
   | SOME v => ?e op dt. def = SOME (op,dt) /\
       ext_call_kwarg EKDefault opts kw_es = SOME e /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       if is_word_type rt then
         dt = rt /\ expr_val_rel cx rt v op z /\ ptr_val_ok cx rt v op G3 tn3 z
       else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G3 tn3 z /\
            ptr_mem_ok cx dt v op G3 tn3 z /\ ptr_buf_ok cenv e op G3 z /\
            (!w. eval_operand op z = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
              w2n w + type_memory_bytes cenv dt <= z.vs_alloca_next) /\
            (?w aid tv. eval_operand op z = SOME w /\
              evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv v /\
              FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
              aid < s3.cs_next_id)) /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
    FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
  zg.vs_labels = z.vs_labels /\ zg.vs_memory = z.vs_memory /\
  zg.vs_allocas = z.vs_allocas /\ zg.vs_alloca_next = z.vs_alloca_next /\
  tng.t_mem = tn3.t_mem /\ s3.cs_next_id <= s5.cs_next_id /\ alloca_next_valid zg ==>
  let def_op = option_CASE def (Lit 0w) FST;
      def_ty = option_CASE def rt SND;
      dopt = ext_call_kwarg EKDefault opts kws in
    op_taint tng def_op = {} /\
    extcall_default_ready cx rt (IS_SOME def) def_op def_ty dopt zg /\
    (!dv. dopt = SOME dv /\ ~is_word_type def_ty ==>
      ptr_mem_ok cx def_ty dv def_op Gg tng zg /\
      (type_memory_bytes cenv def_ty <> 0 ==>
        (?p. def_op = Var p /\ ptr_covers Gg tng p zg (type_memory_bytes cenv def_ty)) /\
        (!w. eval_operand def_op zg = SOME w ==>
          w2n w + type_memory_bytes cenv def_ty <= zg.vs_alloca_next)) /\
      (?w aid tv. eval_operand def_op zg = SOME w /\
        evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
        FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s5.cs_next_id))
Proof
  simp[] >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `ext_call_kwarg EKDefault opts kws`
  >- gvs[extcall_default_ready_def,op_taint_def] >>
  drule_all request_selected_default >> strip_tac >> gvs[] >>
  rename1 `ext_call_kwarg EKDefault opts kws = SOME dv` >>
  `eval_operand op zg = eval_operand op z /\ op_taint tng op = op_taint tn3 op` by
    (Cases_on `op` >> fs[eval_operand_def,op_taint_def]) >>
  `op_taint tng op = {}` by
    (Cases_on `is_word_type (expr_type e)` >> fs[ptr_val_ok_def]) >>
  simp[] >> Cases_on `is_word_type (expr_type e)`
  >- (gvs[extcall_default_ready_def,value_runtime_typed_def] >>
      gvs[expr_val_rel_def] >>
      metis_tac[cj 1 value_has_type_val_wf,type_widens_to_refl]) >>
  gvs[] >>
  `expr_body_pre_mods mods cenv cx env e kw_in` by metis_tac[] >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl [`cx`,`env`,`kw_in`,`mods`] >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    (fs[type_widens_to_def,well_formed_type_def,optionTheory.IS_SOME_EXISTS,
        value_runtime_typed_def] >> metis_tac[]) >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[arg_type_fits_word_type] >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th =>
    rpt (qpat_x_assum `value_runtime_typed _ _ _`
      (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def,th]))) >>
  gvs[] >> drule_all request_default_cell >> strip_tac >>
  conj_tac >- (irule request_memory_default_ready >> simp[] >>
               conj_tac >- (qexists `aid` >> simp[]) >>
               qexistsl [`Gg`,`tng`] >> simp[]) >>
  simp[] >> conj_tac
  >- (strip_tac >> irule ptr_buf_ok_read_covers >>
      simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  qexists `aid` >> simp[]
QED

Theorem request_kwarg_not_label[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) ==>
  !l. op <> Label l
Proof
  strip_tac >> Cases_on `compile_expr cenv (expr_type e) e sa` >>
  drule_all request_compiled_operand_not_label >> strip_tac >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `k = EKDefault /\ ~is_word_type rt`
  >- (Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
      rename1 `compile_materialize_vv _ _ _ _ = (dst,sn)` >>
      `op = dst` by fs[compile_ext_call_kwarg_def,comp_bind_def,comp_return_def] >>
      drule_then strip_assume_tac materialize_compile_trace >>
      drule_then assume_tac (cj 1 compile_alloc_buffer_parts) >> simp[]) >>
  `expr_type e = (if k = EKDefault then rt else BaseT (UintT 256))` by
    (Cases_on `k` >> fs[ext_call_kw_type_def]) >>
  Cases_on `unwrap_value cenv vv sm` >>
  rename1 `unwrap_value _ _ _ = (dst,sn)` >>
  `op = dst` by gvs[compile_ext_call_kwarg_def,lower_value_def,comp_bind_def,
                    comp_return_def] >>
  drule_all unwrap_value_not_label >> simp[]
QED

Theorem request_kwargs_not_label[local]:
  !opts es sa vo go def sb.
    (!e. MEM e es ==> expr_body_pre_mods mods cenv cx env e pre) /\
    MAP expr_type es = MAP (ext_call_kw_type rt) opts /\
    compile_ext_call_kwargs compile_expr cenv rt opts es sa = ((vo,go,def),sb) ==>
    (!op l. vo = SOME op ==> op <> Label l) /\
    (!op l. go = SOME op ==> op <> Label l) /\
    (!op ty l. def = SOME (op,ty) ==> op <> Label l)
Proof
  Induct >- (Cases >> simp[compile_ext_call_kwargs_def,comp_return_def]) >>
  qx_gen_tac `k` >> Cases >- simp[compile_ext_call_kwargs_def,comp_return_def] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `compile_ext_call_kwargs _ _ rt (k::opts) (e::es) sa = _` >>
  Cases_on `compile_ext_call_kwarg compile_expr cenv rt k e sa` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ _ _ = (kw,sm)` >> PairCases_on `kw` >>
  Cases_on `compile_ext_call_kwargs compile_expr cenv rt opts es sm` >>
  rename1 `compile_ext_call_kwargs _ _ _ _ _ _ = (rest,sf)` >> PairCases_on `rest` >>
  `expr_body_pre_mods mods cenv cx env e pre` by simp[] >>
  drule_all request_kwarg_not_label >> strip_tac >>
  `!e. MEM e es ==> expr_body_pre_mods mods cenv cx env e pre` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `k` >> gvs[compile_ext_call_kwargs_def,comp_bind_def,comp_return_def]
QED

Theorem request_kw_operands_safe[local]:
  (!op l. vo = SOME op ==> op <> Label l) /\
  (!op l. go = SOME op ==> op <> Label l) /\
  (!op ty l. def = SOME (op,ty) ==> op <> Label l) /\
  (!x. vo = SOME (Var x) ==> not_fresh_at s3 x) /\
  (!x. go = SOME (Var x) ==> not_fresh_at s3 x) /\
  (!x ty. def = SOME (Var x,ty) ==> not_fresh_at s3 x) /\
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  s3.cs_next_var <= s5.cs_next_var ==>
  safe_operand s5 (option_CASE vo (Lit 0w) I) /\ safe_operand s5 gas /\
  safe_operand s5 (option_CASE def (Lit 0w) FST)
Proof
  strip_tac >> conj_tac
  >- (irule safe_operand_mono >> qexists `s3` >>
      Cases_on `vo` >> gvs[safe_operand_def]) >>
  conj_tac
  >- (Cases_on `go` >> gvs[]
      >- metis_tac[emit_op_safe_operand] >> simp[safe_operand_def]) >>
  irule safe_operand_mono >> qexists `s3` >>
  Cases_on `def` >> gvs[safe_operand_def] >> PairCases_on `x` >> gvs[]
QED

Theorem request_positional_packet[local]:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr) es /\
  xs = TAKE (LENGTH ats) tail /\ LENGTH av = LENGTH xs /\
  expr_sim_inv_mods mods cenv cx env pos /\
  (!e s. MEM e xs /\ expr_sim_inv_mods mods cenv cx env s ==>
    expr_body_pre_mods mods cenv cx env e s) /\
  eval_exprs cx xs pos = (INL vs,ee) /\
  (!i. i < LENGTH xs ==> ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H
    (EL i xs) (EL i av) (EL i vs) ke Gg tng zg) ==>
  let ptys = MAP (lowered_value_type cenv) xs;
      abi = abi_size_bound cenv.ce_struct_fields (TupleT ptys);
      cap = abi_size_bound cenv.ce_struct_fields
              (if needs_external_call_wrap rt then TupleT [rt] else rt) in
    env.type_defs = get_tenv cx /\
    LENGTH xs = LENGTH av /\ LENGTH av = LENGTH vs /\ LENGTH vs = LENGTH ats /\
    EVERY (assignable_type (get_tenv cx)) ats /\
    EVERY (abi_decode_bytes_widths (get_tenv cx)) ats /\
    EVERY (assignable_type (get_tenv cx)) ptys /\
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
    SUM (MAP (type_memory_bytes cenv) ptys) < 2**64 /\
    MAX abi cap + 32 < 2**64 /\ (if abi > cap then abi else cap) + 32 < dimword (:256) /\
    cenv.ce_method_id fname ats = w2n (calldata_method_id
      (function_selector fname (vyper_to_abi_types (get_tenv cx) ats))) /\
    abi = vyper_abi_size_bound (get_tenv cx) (TupleT ptys) /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!ty. MEM ty ptys ==> abi_enc_plan (get_tenv cx) ty
      (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)) /\
    (!i. i < LENGTH xs ==>
      let e = EL i xs; sv = EL i av; v = EL i vs; formal = EL i ats in
      ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H e sv v ke Gg tng zg /\
      (!l. vv_operand sv <> Label l) /\
      arg_type_fits (lowered_value_type cenv e) formal /\
      (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
      ?tv param_tv.
        evaluate_type (get_tenv cx) formal = SOME param_tv /\ value_has_type param_tv v /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
        type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
        type_memory_size tv < 2**64 /\ value_has_type tv v)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all ext_request_signature_mods >> strip_tac >>
  qpat_x_assum `xs = TAKE _ _` kall_tac >>
  drule_all ext_request_replay_lowered >> strip_tac >>
  drule_all ext_request_indexed_types >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "typed_at"))) >>
  `EVERY (assignable_type (get_tenv cx)) (MAP (lowered_value_type cenv) xs)` by
    (simp[EVERY_EL,EL_MAP] >> rpt strip_tac >>
     asm "typed_at" (qspec_then `n` mp_tac) >> simp[]) >>
  `!a b. MAX a b + 32 < 2**64 ==>
        (if a > b then a else b) + 32 < dimword (:256)` by
    (rpt gen_tac >> strip_tac >> irule lt_dimword_256 >> qexists `64` >>
     fs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
  pop_assum (fn th => drule th >> strip_tac) >>
  drule_all ext_request_encoding_plans >> strip_tac >>
  fs[] >>
  gen_tac >> disch_tac >>
  asm "typed_at" (qspec_then `i` mp_tac) >>
  simp[] >> strip_tac >>
  `ext_pos_saved_row_mods lo cenv cx kw_es sa s5 H (EL i xs) (EL i av) (EL i vs) ke Gg tng zg` by
    simp[] >>
  drule_all ext_request_indexed_row_operand >> simp[]
QED

Theorem request_keyword_packet[local]:
  expr_sim_inv_mods mods cenv cx env kw_in /\
  (!e st. MEM e kw_es /\ expr_sim_inv_mods mods cenv cx env st ==>
    expr_body_pre_mods mods cenv cx env e st) /\
  eval_exprs cx kw_es kw_in = (INL kws,ke) /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v) kw_es kws /\
  MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts /\ ext_call_opts_ok stat opts /\
  (rt = NoneT ==> ext_call_kwarg EKDefault opts kws = NONE) /\
  compile_ext_call_kwargs compile_expr cenv rt opts kw_es s2 = ((vo,go,def),s3) /\
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  (case ext_call_kwarg EKGas opts kws of NONE => go = NONE
   | SOME gv => ?op w. go = SOME op /\ eval_operand op z = SOME w /\
      (!x. op = Var x ==> not_fresh_at s3 x) /\
      dest_NumV gv = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (case ext_call_kwarg EKValue opts kws of NONE => vo = NONE
   | SOME vi => ?op w. vo = SOME op /\ eval_operand op z = SOME w /\
      (!x. op = Var x ==> not_fresh_at s3 x) /\
      dest_NumV vi = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (case ext_call_kwarg EKDefault opts kws of NONE => def = NONE
   | SOME v => ?e op dt. def = SOME (op,dt) /\
       ext_call_kwarg EKDefault opts kw_es = SOME e /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       if is_word_type rt then
         dt = rt /\ expr_val_rel cx rt v op z /\ ptr_val_ok cx rt v op G3 tn3 z
       else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G3 tn3 z /\
            ptr_mem_ok cx dt v op G3 tn3 z /\ ptr_buf_ok cenv e op G3 z /\
            (!w. eval_operand op z = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
              w2n w + type_memory_bytes cenv dt <= z.vs_alloca_next) /\
            (?w aid tv. eval_operand op z = SOME w /\
              evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv v /\
              FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
              aid < s3.cs_next_id)) /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
    FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) /\
  zg.vs_labels = z.vs_labels /\ zg.vs_memory = z.vs_memory /\
  zg.vs_allocas = z.vs_allocas /\ zg.vs_alloca_next = z.vs_alloca_next /\
  tng.t_mem = tn3.t_mem /\ s3.cs_next_var <= s5.cs_next_var /\
  s3.cs_next_id <= s5.cs_next_id /\ alloca_next_valid zg /\
  eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) ==>
  let value = option_CASE vo (Lit 0w) I;
      value_opt = if stat then NONE else
        option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV;
      def_op = option_CASE def (Lit 0w) FST;
      def_ty = option_CASE def rt SND;
      dopt = ext_call_kwarg EKDefault opts kws in
    EVERY (safe_operand s5) [value;gas;def_op] /\
    EVERY (\p. op_taint tng p = {}) [value;gas;def_op] /\
    (stat <=> value_opt = NONE) /\
    (?vw. eval_operand value zg = SOME vw /\
          w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
    eval_operand gas zg = SOME gw /\
    (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    extcall_default_ready cx rt (IS_SOME def) def_op def_ty dopt zg /\
    (!dv. dopt = SOME dv /\ ~is_word_type def_ty ==>
      ptr_mem_ok cx def_ty dv def_op Gg tng zg /\
      (type_memory_bytes cenv def_ty <> 0 ==>
        (?p. def_op = Var p /\ ptr_covers Gg tng p zg (type_memory_bytes cenv def_ty)) /\
        (!w. eval_operand def_op zg = SOME w ==>
          w2n w + type_memory_bytes cenv def_ty <= zg.vs_alloca_next)) /\
      (?w aid tv. eval_operand def_op zg = SOME w /\
        evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
        FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\ aid < s5.cs_next_id))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> simp[env_consistent_def,env_context_consistent_def]) >>
  drule_all ext_request_replay_lowered >> strip_tac >>
  drule_all request_default_packet >> simp[] >> strip_tac >>
  `!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
         op_taint tng (Var x) = op_taint tn3 (Var x)` by metis_tac[] >>
  drule_all request_value_ready >> simp[] >> strip_tac >>
  `!e. MEM e kw_es ==> expr_body_pre_mods mods cenv cx env e kw_in` by simp[] >>
  drule_all request_kwargs_not_label >> strip_tac >>
  `!x. vo = SOME (Var x) ==> not_fresh_at s3 x` by
    (Cases_on `ext_call_kwarg EKValue opts kws` >> fs[]) >>
  `!x. go = SOME (Var x) ==> not_fresh_at s3 x` by
    (Cases_on `ext_call_kwarg EKGas opts kws` >> fs[]) >>
  `!x ty. def = SOME (Var x,ty) ==> not_fresh_at s3 x` by
    (Cases_on `ext_call_kwarg EKDefault opts kws` >> fs[] >>
     Cases_on `is_word_type rt` >> gvs[]) >>
  `safe_operand s5 (option_CASE vo (Lit 0w) I) /\ safe_operand s5 gas /\
   safe_operand s5 (option_CASE def (Lit 0w) FST)` by
    (irule request_kw_operands_safe >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`go`,`s3`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* The two source lists and the address are rejoined at the same post-GAS
   compiler and machine cursor. Each packet is also a separate proof cut. *)
Theorem ext_request_abi_inputs_mods:
  ^(fst (dest_imp (concl request_positional_packet))) /\
  ^(fst (dest_imp (concl request_keyword_packet))) /\
  ^(fst (dest_imp (concl request_target_ready))) /\
  expr_sim_inv_mods mods cenv cx env ke ==>
  ^(snd (dest_imp (concl request_positional_packet))) /\
  ^(snd (dest_imp (concl request_keyword_packet))) /\
  ^(snd (dest_imp (concl request_target_ready))) /\
  outcomes_accounts_typed ke.outcomes /\ accounts_runtime_well_typed ke.accounts
Proof
  disch_then (CONJUNCTS_THEN2 (assume_tac o MATCH_MP request_positional_packet)
    (CONJUNCTS_THEN2 (assume_tac o MATCH_MP request_keyword_packet)
      (CONJUNCTS_THEN2 (assume_tac o MATCH_MP request_target_ready) assume_tac))) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ ke` mp_tac >>
  simp[expr_sim_inv_mods_def,accounts_runtime_well_typed_accounts_well_typed]
QED

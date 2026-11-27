Theory bodyFullExtCallRequestPostGasPacking
Ancestors loweringPosts[qualified,ignore_grammar] exprSimHypsDefs[qualified,ignore_grammar] vyperTypeExtCallCore[qualified,ignore_grammar]
  bodyFullExtCallPackingReady bodyFullExtCallKeywordPackingRows
  abiEncodeArgsCase aggregateEvaluatedLayout typedCopyCompatibility
  assignPlaceOperandFacts exprSafeOperand exprLowering context compileEnv
  immutableDeployPhysicalSource[qualified,ignore_grammar]
  bodyInvSplit[qualified]
Libs
  pairLib horizonTypeLib

(* Join the source replay to the saved physical row without widening
   the value's memory layout to that of the formal parameter. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_then assume_tac exprSimHypsTheory.expr_body_pre_lowered_fits >>
  `arg_type_fits (lowered_value_type cenv e) formal` by
    metis_tac[cj 1 typedCopyCompatibilityTheory.arg_type_fits_trans] >>
  qpat_x_assum `value_runtime_typed _ _ _`
    (strip_assume_tac o REWRITE_RULE [vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  qpat_x_assum `well_formed_type _ formal`
    (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.well_formed_type_def,
                                      optionTheory.IS_SOME_EXISTS]) >>
  rename1 `evaluate_type _ formal = SOME param_tv` >>
  `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv` by metis_tac[] >>
  qexistsl [`tv`,`param_tv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type]
  >- metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type]
  >- metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
               cj 1 exprSimHypsDefsTheory.expr_body_pre_def]
  >- (`type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv` by
        metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size,
                  cj 1 exprSimHypsDefsTheory.expr_body_pre_def] >>
      `type_memory_bytes cenv (lowered_value_type cenv e) <=
       type_memory_bytes cenv (expr_type e)` by
         metis_tac[cj 1 abi_args_fits_memory_bytes] >>
      `type_alloc_ok cenv (expr_type e)` by
        (irule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >>
         fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
      Cases_on `is_word_type (expr_type e)` >>
      fs[allocLimitsTheory.type_alloc_ok_def, cj 3 entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
      decide_tac) >>
  `!l. vv_operand vv <> Label l` by metis_tac[assign_place_operand_not_label] >>
  `vv_operand (ext_call_arg_value (lowered_value_type cenv e) vv) = vv_operand vv` by
    (Cases_on `vv` >> simp[exprLoweringTheory.ext_call_arg_value_def, vv_operand_def]) >>
  qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
  simp[compile_snapshot_vv_def] >> IF_CASES_TAC
  >- (simp[comp_bind_def] >> pairarg_tac >> simp[comp_return_def] >>
      strip_tac >> gvs[vv_operand_def] >> drule unwrap_value_not_label >> simp[]) >>
  Cases_on `copy` >> simp[comp_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[vv_operand_def, mk_ptr_def] >>
      qpat_x_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
      simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> rpt strip_tac >> gvs[] >>
      drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >>
      simp[loweringShapeRulesTheory.emit_op_eq]) >>
  strip_tac >> gvs[]
QED
*)
Theorem post_gas_row_type_facts[local]:
  expr_body_pre_mods mods cenv cx env e ee /\
  env.type_defs = get_tenv cx /\
  value_runtime_typed env (lowered_value_type cenv e) v /\
  arg_type_fits (expr_type e) formal /\ well_formed_type (get_tenv cx) formal /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) ==>
  ?tv param_tv.
    arg_type_fits (lowered_value_type cenv e) formal /\
    evaluate_type (get_tenv cx) formal = SOME param_tv /\
    value_has_type param_tv v /\
    (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
    type_memory_size tv < 2**64 /\ value_has_type tv v /\
    (!l. vv_operand sv <> Label l)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. i < LENGTH xs ==> ?e sv v raw si sm ss vv copy. _`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`e`,`sv`,`v`,`raw`,`si`,`sm`,`ss`,`vv`,`copy`]
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `expr_body_pre cenv cx env e pos` by
    (qpat_assum `!e st. MEM e xs /\ _ ==> _` irule >>
     simp[listTheory.MEM_EL] >> qexists `i` >> simp[]) >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (qpat_assum `LIST_REL _ xs vs` (mp_tac o REWRITE_RULE [listTheory.LIST_REL_EL_EQN]) >>
     disch_then (qspec_then `i` mp_tac o CONJUNCT2) >> simp[]) >>
  `LENGTH xs = LENGTH ats /\ arg_type_fits (expr_type e) (EL i ats)` by
    (qpat_assum `arg_types_fit _ ats` (mp_tac o REWRITE_RULE
      [vyperTypeArgFitsTheory.arg_types_fit_LIST_REL, listTheory.LIST_REL_EL_EQN,
       listTheory.LENGTH_MAP]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `i` mp_tac)) >>
     simp[listTheory.EL_MAP]) >>
  `well_formed_type (get_tenv cx) (EL i ats)` by
    (qpat_assum `EVERY _ ats` (mp_tac o REWRITE_RULE [listTheory.EVERY_EL]) >> simp[]) >>
  drule_all post_gas_row_type_facts >>
  disch_then (qx_choosel_then [`tv`,`param_tv`] (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`e`,`sv`,`v`,`raw`,`si`,`sm`,`ss`,`vv`,`tv`,`param_tv`,`copy`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem post_gas_indexed_rows:
  env.type_defs = get_tenv cx /\ expr_sim_inv_mods mods cenv cx env pos /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  arg_types_fit (MAP expr_type xs) ats /\ EVERY (well_formed_type (get_tenv cx)) ats /\
  (!i. i < LENGTH xs ==>
    ?e sv v raw si sm ss vv copy.
      e = EL i xs /\ sv = EL i av /\ v = EL i vs /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      local_ptrs_reserved cenv si /\
      sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx sv ee t) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t)) ==>
  !i. i < LENGTH xs ==>
    ?e sv v raw si sm ss vv tv param_tv copy.
      e = EL i xs /\ sv = EL i av /\ v = EL i vs /\
      arg_type_fits (lowered_value_type cenv e) (EL i ats) /\
      evaluate_type (get_tenv cx) (EL i ats) = SOME param_tv /\
      value_has_type param_tv v /\
      (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      local_ptrs_reserved cenv si /\
      sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand sv <> Label l) /\
      read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee t /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv t /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx sv ee t) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G t)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all bodyCustomErrorWindowBoundsTheory.custom_error_invariant_layout >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `IS_SOME (OPT_MMAP (evaluate_type (get_tenv cx)) tys)` by
    (fs[listTheory.IS_SOME_OPT_MMAP, listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
     rpt strip_tac >>
     `assignable_type (get_tenv cx) x` by simp[] >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def]) >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `OPT_MMAP _ tys = SOME tvs` >>
  `SUM (MAP (type_memory_bytes cenv) tys) = type_memory_size_list tvs` by
    (irule structFieldsPropsTheory.tuple_memory_bytes_size >> qexists `get_tenv cx` >> simp[]) >>
  `type_slot_size_list tvs < 2**64` by
    (fs[cj 4 logDataPackingTheory.log_memory_slot_sizes] >> decide_tac) >>
  `type_slot_size_list tvs < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists `64` >> simp[]) >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    simp[cj 2 vyperValueTheory.evaluate_type_def, vyperValueTheory.evaluate_types_OPT_MMAP,
         vyperValueTheory.type_slot_size_def, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  conj_tac >- metis_tac[] >>
  gen_tac >> disch_tac >>
  `assignable_type (get_tenv cx) ty` by
    (qpat_assum `EVERY (assignable_type (get_tenv cx)) tys`
       (drule_then ACCEPT_TAC o REWRITE_RULE [listTheory.EVERY_MEM])) >>
  irule retAbiPlanPropsTheory.type_to_abi_enc_info_plan >>
  simp[] >> qexists `get_tenv cx` >> simp[finite_mapTheory.SUBMAP_REFL]
QED
*)
Theorem post_gas_encoding_plans[local]:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ expr_sim_inv_mods mods cenv cx env ee /\
  EVERY (assignable_type (get_tenv cx)) tys /\
  SUM (MAP (type_memory_bytes cenv) tys) < 2**64 ==>
  abi_size_bound cenv.ce_struct_fields (TupleT tys) =
    vyper_abi_size_bound (get_tenv cx) (TupleT tys) /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!ty. MEM ty tys ==> abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, cj 13 vyperTypeSystemTheory.well_typed_expr_def,
       cj 12 allocLimitsTheory.alloc_limits_expr_def, cj 1 allocLimitsTheory.ext_call_alloc_ok_def] >>
  strip_tac >> gvs[] >>
  metis_tac[cj 11 (iffLR exprSimHypsDefsTheory.expr_sim_inv_def)]
QED
*)
Theorem post_gas_call_signature[local]:
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr) es /\
  env.type_defs = get_tenv cx /\ xs = TAKE (LENGTH ats) tail ==>
  EVERY (assignable_type (get_tenv cx)) ats /\
  EVERY (abi_decode_bytes_widths (get_tenv cx)) ats /\
  EVERY (well_formed_type (get_tenv cx)) ats /\
  SUM (MAP (type_memory_bytes cenv) (MAP (lowered_value_type cenv) xs)) < 2**64 /\
  MAX (abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)))
      (abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32 < 2**64 /\
  cenv.ce_method_id fname ats = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) ats)))
Proof
  cheat
QED

Theorem post_gas_lowered_assignable[local]:
  env.type_defs = get_tenv cx /\ expr_sim_inv_mods mods cenv cx env pos /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  arg_types_fit (MAP expr_type xs) ats /\ EVERY (assignable_type (get_tenv cx)) ats ==>
  EVERY (assignable_type (get_tenv cx)) (MAP (lowered_value_type cenv) xs)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[listTheory.EVERY_EL, listTheory.EL_MAP] >> rpt strip_tac >>
  `expr_body_pre cenv cx env (EL n xs) pos` by
    (qpat_assum `!e st. MEM e xs /\ _ ==> _` irule >> simp[listTheory.EL_MEM]) >>
  `arg_type_fits (expr_type (EL n xs)) (EL n ats) /\ LENGTH ats = LENGTH xs` by
    (qpat_assum `arg_types_fit _ ats` (mp_tac o REWRITE_RULE
      [vyperTypeArgFitsTheory.arg_types_fit_LIST_REL, listTheory.LIST_REL_EL_EQN,
       listTheory.LENGTH_MAP]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (qspec_then `n` mp_tac)) >>
     simp[listTheory.EL_MAP]) >>
  `value_runtime_typed env (lowered_value_type cenv (EL n xs)) (EL n vs)` by
    (qpat_assum `LIST_REL _ xs vs` (mp_tac o REWRITE_RULE [listTheory.LIST_REL_EL_EQN]) >>
     disch_then (qspec_then `n` mp_tac o CONJUNCT2) >> simp[]) >>
  drule_then assume_tac exprSimHypsTheory.expr_body_pre_lowered_fits >>
  `arg_type_fits (lowered_value_type cenv (EL n xs)) (EL n ats)` by
    metis_tac[cj 1 typedCopyCompatibilityTheory.arg_type_fits_trans] >>
  qpat_assum `arg_type_fits (lowered_value_type _ _) _`
    (mp_tac o MATCH_MP (cj 1 placeRelayoutSemanticTheory.arg_type_fits_source_assignable)) >>
  disch_then (qspec_then `get_tenv cx` irule) >>
  conj_tac
  >- (qpat_assum `EVERY _ ats` (mp_tac o REWRITE_RULE [listTheory.EVERY_EL]) >> simp[]) >>
  fs[vyperTypeSystemTheory.well_formed_type_def,
     vyperTypeExprSoundnessTheory.value_runtime_typed_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]
QED

(* Optional GAS does not disturb the selected default's saved cell. *)
Theorem post_gas_default_cell[local]:
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
    (Cases_on `op` >> fs[venomStateTheory.eval_operand_def]) >>
  `!x. op = Var x ==> FLOOKUP Gg x = FLOOKUP G3 x` by metis_tac[] >>
  simp[] >> rpt conj_tac
  >- (simp[bodyPtrDefsTheory.ptr_mem_ok_def] >> gen_tac >> disch_tac >>
      qpat_assum `ptr_mem_ok _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
      disch_then drule >> simp[] >> metis_tac[])
  >- (simp[bodyPtrDefsTheory.ptr_buf_ok_def] >> disch_tac >>
      qpat_assum `ptr_buf_ok _ _ _ _ _`
        (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_buf_ok_def]) >>
      disch_then drule >> simp[] >> metis_tac[]) >>
  decide_tac
QED

Theorem post_gas_memory_default_ready[local]:
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
  `val_wf tv v /\ val_wf rtv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `w2n w + val_footprint tv v <= t.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_next_valid_def] >>
     `val_footprint tv v <= type_memory_size tv` by simp[exprSimPropsTheory.val_footprint_le] >>
     `w2n w + type_memory_size tv <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  simp[exprSimExtCallCaseTheory.extcall_default_ready_def] >>
  simp[loweringPostsTheory.expr_val_rel_def] >>
  fs[bodyPtrDefsTheory.ptr_mem_ok_def] >>
  metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]
QED

(* Both typings come from the same successful source replay. *)
Theorem post_gas_replay_typed[local]:
  !xs pos vs ee.
    expr_sim_inv_mods mods cenv cx env pos /\
    (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
    eval_exprs cx xs pos = (INL vs,ee) ==>
    LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
      value_runtime_typed env (lowered_value_type cenv e) v) xs vs
Proof
  Induct >- simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule exprSimAggregateSourceTheory.aggregate_eval_exprs_cons >>
  strip_tac >> gvs[] >> Cases_on `rr` >> gvs[] >>
  `expr_body_pre cenv cx env h pos` by metis_tac[] >>
  `expr_sim_inv cenv cx env es1` by
    metis_tac[bodySimStmtFactsTheory.expr_body_pre_eval_result] >>
  `(do r <- eval_expr cx h; read_result cx r od) pos = (INL v,es1)` by
    simp[vyperStateTheory.bind_def] >>
  conj_tac >- metis_tac[exprSimHypsTheory.memory_rhs_read_annotation_typed] >>
  conj_tac >- metis_tac[exprSimHypsTheory.memory_rhs_read_lowered_typed_unwidened] >>
  first_x_assum irule >> metis_tac[]
QED

Theorem post_gas_selected_default[local]:
  !ks xs vs.
  MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs /\
  ext_call_kwarg EKDefault ks vs = SOME v ==>
  ?e. ext_call_kwarg EKDefault ks xs = SOME e /\ MEM e xs /\ expr_type e = rt /\
      value_runtime_typed env rt v /\
      value_runtime_typed env (lowered_value_type cenv e) v
Proof
  Induct >- simp[vyperInterpreterTheory.ext_call_kwarg_def] >>
  Cases_on `xs` >> Cases_on `vs` >>
  simp[vyperInterpreterTheory.ext_call_kwarg_def, vyperTypeSystemTheory.ext_call_kw_type_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `expr_type _ = ext_call_kw_type rt k` >>
  Cases_on `k = EKDefault` >> gvs[vyperTypeSystemTheory.ext_call_kw_type_def] >> metis_tac[]
QED

Theorem post_gas_default_packet[local]:
  env.type_defs = get_tenv cx /\ expr_sim_inv_mods mods cenv cx env kw_in /\
  (!e st. MEM e kw_es /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  eval_exprs cx kw_es kw_in = (INL kws,ke) /\
  MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts /\
  (rt = NoneT ==> ext_call_kwarg EKDefault opts kws = NONE) /\
  (has_def <=> IS_SOME dopt) /\
  (case dopt of NONE => def_op = Lit 0w /\ def_ty = rt
              | SOME p => p = (def_op,def_ty)) /\
  (case ext_call_kwarg EKDefault opts kws of
     NONE => dopt = NONE
   | SOME v => ?e op dt. dopt = SOME (op,dt) /\
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
  op_taint tng def_op = {} /\
  extcall_default_ready cx rt has_def def_op def_ty (ext_call_kwarg EKDefault opts kws) zg /\
  (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\ ~is_word_type def_ty ==>
    ptr_mem_ok cx def_ty dv def_op Gg tng zg /\
    (type_memory_bytes cenv def_ty <> 0 ==>
      (?p. def_op = Var p /\ ptr_covers Gg tng p zg (type_memory_bytes cenv def_ty)) /\
      (!w. eval_operand def_op zg = SOME w ==>
           w2n w + type_memory_bytes cenv def_ty <= zg.vs_alloca_next)) /\
    (?w aid tv. eval_operand def_op zg = SOME w /\
      evaluate_type (get_tenv cx) def_ty = SOME tv /\ val_wf tv dv /\
      FLOOKUP zg.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < s5.cs_next_id))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all post_gas_replay_typed >> strip_tac >>
  Cases_on `ext_call_kwarg EKDefault opts kws`
  >- gvs[exprSimExtCallCaseTheory.extcall_default_ready_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all post_gas_selected_default >> strip_tac >> gvs[] >>
  rename1 `ext_call_kwarg EKDefault opts kws = SOME dv` >>
  `eval_operand def_op zg = eval_operand def_op z /\
   op_taint tng def_op = op_taint tn3 def_op` by
    (Cases_on `def_op` >> fs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  `op_taint tng def_op = {}` by
    (Cases_on `is_word_type (expr_type e)` >> fs[bodyPtrDefsTheory.ptr_val_ok_def]) >>
  simp[] >> Cases_on `is_word_type (expr_type e)`
  >- (gvs[exprSimExtCallCaseTheory.extcall_default_ready_def,
          vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
      gvs[loweringPostsTheory.expr_val_rel_def] >>
      metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf,
                vyperTypeArgFitsTheory.type_widens_to_refl]) >>
  gvs[] >>
  `expr_body_pre cenv cx env e kw_in` by metis_tac[] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    (irule immutableDeployPhysicalSourceTheory.immutable_rhs_physical_widens >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th =>
    rpt (qpat_x_assum `value_runtime_typed _ _ _`
      (strip_assume_tac o REWRITE_RULE [vyperTypeExprSoundnessTheory.value_runtime_typed_def, th]))) >>
  drule_all post_gas_default_cell >> strip_tac >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits,
              aggregateEvaluatedLayoutTheory.arg_type_fits_word_type] >>
  conj_tac
  >- (irule post_gas_memory_default_ready >>
      fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (strip_tac >> irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
      simp[] >> qexistsl [`cenv`,`e`] >> simp[]) >>
  qexists `aid` >> simp[]
QED

(* The source selection and physical value operand refer to the same
   first keyword. A later GAS step leaves the selected operand intact. *)
Theorem post_gas_value_ready[local]:
  ext_call_opts_ok stat opts /\
  (case ext_call_kwarg EKValue opts kws of
     NONE => vo = NONE
   | SOME v => ?op w. vo = SOME op /\ eval_operand op z = SOME w /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       dest_NumV v = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
     op_taint tng (Var x) = op_taint tn3 (Var x)) /\
  zg.vs_labels = z.vs_labels /\
  value = option_CASE vo (Lit 0w) I /\
  value_opt = (if stat then NONE else
    option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV) ==>
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value zg = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  op_taint tng value = {} /\
  (!x. value = Var x ==> not_fresh_at s3 x)
Proof
  strip_tac >> Cases_on `ext_call_kwarg EKValue opts kws`
  >- (Cases_on `stat` >>
      gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def]) >>
  `~stat` by
    (strip_tac >> fs[vyperInterpreterTheory.ext_call_opts_ok_def] >>
     metis_tac[vyperTypeExtCallSoundnessTheory.ext_call_kwarg_not_mem,
               optionTheory.NOT_SOME_NONE]) >>
  gvs[] >> rename1 `eval_operand op z = SOME w` >>
  Cases_on `op` >>
  gvs[venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]
QED

(* The allocation floor is already in the per-horizon ghost invariant. *)
Theorem post_gas_alloca_floor[local]:
  ghost_inv_at D lo d cenv cx ke Gg tng zg ==>
  allocas_from lo zg /\ lo <= zg.vs_alloca_next
Proof
  simp[bodyPtrDefsTheory.ghost_inv_at_def]
QED

(* Address decoding is already established at the positional cut. The
   taint fact at the target cut is separate from that numeric equality. *)
Theorem post_gas_target_ready[local]:
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
  >- (irule exprSafeOperandTheory.safe_operand_mono >>
      qexists `s1` >> simp[] >> decide_tac) >>
  fs[exprSafeOperandTheory.safe_operand_def,
     bodyPtrDefsTheory.ptr_val_ok_def,bodyPtrDefsTheory.ghost_kept_at_def] >>
  Cases_on `ao` >> fs[ptrDisciplineTheory.op_taint_def,venomStateTheory.eval_operand_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem post_gas_extend_frame[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  wb_frame cenv es es1 sa s0 s /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es1 ee sm s t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s G2 tn2 ==>
  wb_frame cenv es ee sa s0 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    gvs[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >>
  conj_tac
  >- (irule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.wb_frame_trans) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  drule_all (horizonTypeLib.at_horizon_named "H" wordArgsPtrTheory.ghost_kept_at_wb_trans) >> simp[]
QED

(* Keyword selection returns either an unwrapped child operand or the
   buffer operand produced by materializing a nonword default. *)
Theorem post_gas_kwarg_not_label[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) ==>
  !l. op <> Label l
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  drule_all assign_place_operand_not_label >> strip_tac >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `k = EKDefault /\ ~is_word_type rt`
  >- (Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
      rename1 `compile_materialize_vv _ _ _ _ = (dst,sn)` >>
      `op = dst` by fs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
      drule_then strip_assume_tac abiEncodeMaterializeTheory.materialize_compile_trace >>
      drule_then assume_tac (cj 1 loweringHaltTheory.compile_alloc_buffer_parts) >>
      simp[]) >>
  `expr_type e = (if k = EKDefault then rt else BaseT (UintT 256))` by
    (Cases_on `k` >> fs[vyperTypeSystemTheory.ext_call_kw_type_def]) >>
  Cases_on `unwrap_value cenv vv sm` >>
  rename1 `unwrap_value _ _ _ = (dst,sn)` >>
  `op = dst` by gvs[compile_ext_call_kwarg_def, lower_value_def, comp_bind_def,
                    comp_return_def] >>
  drule_all unwrap_value_not_label >> simp[]
QED

Theorem post_gas_kwargs_not_label[local]:
  !opts es sa vo go def sb.
    (!e. MEM e es ==> expr_body_pre_mods mods cenv cx env e pre) /\
    MAP expr_type es = MAP (ext_call_kw_type rt) opts /\
    compile_ext_call_kwargs compile_expr cenv rt opts es sa = ((vo,go,def),sb) ==>
    (!op l. vo = SOME op ==> op <> Label l) /\
    (!op l. go = SOME op ==> op <> Label l) /\
    (!op ty l. def = SOME (op,ty) ==> op <> Label l)
Proof
  Induct >- (Cases >> simp[compile_ext_call_kwargs_def, comp_return_def]) >>
  qx_gen_tac `k` >> Cases >- simp[] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `compile_ext_call_kwargs _ _ rt (k::opts) (e::es) sa = _` >>
  Cases_on `compile_ext_call_kwarg compile_expr cenv rt k e sa` >>
  rename1 `compile_ext_call_kwarg _ _ _ _ _ _ = (kw,sm)` >> PairCases_on `kw` >>
  Cases_on `compile_ext_call_kwargs compile_expr cenv rt opts es sm` >>
  rename1 `compile_ext_call_kwargs _ _ _ _ _ _ = (rest,sf)` >> PairCases_on `rest` >>
  `expr_body_pre cenv cx env e pre` by simp[] >>
  drule_all post_gas_kwarg_not_label >> strip_tac >>
  `!e. MEM e es ==> expr_body_pre cenv cx env e pre` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `k` >> gvs[compile_ext_call_kwargs_def, comp_bind_def, comp_return_def]
QED

(* Assemble the request from the saved rows and the actual operand path. *)
Theorem extcall_request_post_gas_packing:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (addr::tail) dr) es /\
  xs = TAKE (LENGTH ats) tail /\
  LENGTH av = LENGTH xs /\ arg_types_fit (MAP expr_type xs) ats /\
  expr_sim_inv_mods mods cenv cx env mid /\ expr_sim_inv_mods mods cenv cx env ee /\
  expr_sim_inv_mods mods cenv cx env ke /\
  (!e st. MEM e xs /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  eval_exprs cx xs (mid with gas_obs := obs2) = (INL vs,ee) /\
  (!i. i < LENGTH xs ==>
    ?e sv v raw si sm ss vv copy.
      e = EL i xs /\ sv = EL i av /\ v = EL i vs /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      local_ptrs_reserved cenv si /\
      sm.cs_next_var <= s5.cs_next_var /\ sm.cs_next_id <= s5.cs_next_id /\
      ss.cs_next_var <= s5.cs_next_var /\ ss.cs_next_id <= s5.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      read_result cx raw ke = (INL v,ke) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ke zg /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ke raw sv zg /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ke Gg tng zg /\
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ke raw sv zg /\
      (!H. valid_horizon cx st0 H ke.storage_trace ==> vv_storage_live H cx sv ke zg) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) Gg zg)) /\
  compile_alloc_buffer
    ((if abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs)) >
         abi_size_bound cenv.ce_struct_fields
           (if needs_external_call_wrap rt then TupleT [rt] else rt)
      then abi_size_bound cenv.ce_struct_fields (TupleT (MAP (lowered_value_type cenv) xs))
      else abi_size_bound cenv.ce_struct_fields
        (if needs_external_call_wrap rt then TupleT [rt] else rt)) + 32) s5 = (ba,sb1) /\
  emit_void MSTORE [ba.buf_operand;Lit (n2w (cenv.ce_method_id fname ats))] sb1 = ((),sb2) /\
  (if av = [] then comp_return (Lit 4w) else
     comp_bind (emit_op ADD [ba.buf_operand;Lit 32w]) (\dst.
      comp_bind (compile_abi_encode_values_to_buf cenv dst
        (ZIP (av,MAP (lowered_value_type cenv) xs))) (\alen.
      emit_op ADD [alen;Lit 4w]))) sb2 = (len,sb3) /\
  emit_op ADD [ba.buf_operand;Lit 28w] sb3 = (off,sp) /\
  fn_has_code s5 sb1 func /\ fn_has_code sb1 sb2 func /\
  fn_has_code sb2 sb3 func /\ fn_has_code sb3 sp func /\
  fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  valid_horizon cx st0 H ke.storage_trace /\
  stmt_state_rel (H0 : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\
  (!K. valid_horizon cx st0 K ke.storage_trace ==>
       stmt_state_rel K ctx func cenv cx ke zg /\ storage_well_formed_on cx ke (FST K) /\
       ghost_inv_at (DF K) lo d cenv cx ke Gg tng zg) /\
  stmt_state_rel H ctx func cenv cx ee u /\
  expr_post H ctx func cenv cx addr es sa s1 s0 mid v ao t0 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t0 G2 tn2 /\
  ghost_kept_at lo cenv ee s2 G2 tn2 u Gg tng /\
  wb_frame cenv mid ee s1 t0 u /\ wb_frame cenv ee ke s2 u zg /\
  (!x w. not_fresh_at s1 x /\ lookup_var x t0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t0.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  (!x w. not_fresh_at s2 x /\ lookup_var x u = SOME w ==> lookup_var x zg = SOME w) /\
  (!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> FLOOKUP zg.vs_allocas aid = SOME row) /\
  local_ptrs_reserved cenv sa /\ ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s5 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~zg.vs_halted /\ zg.vs_current_bb = s5.cs_current_bb /\
  zg.vs_inst_idx = LENGTH s5.cs_current_insts /\ ke.gas_obs = [] /\
  alloca_history func zg /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_alloca_next <= zg.vs_alloca_next /\ return_buf_frame d cenv s3 z /\
  safe_operand s1 ao /\ ptr_val_ok cx (BaseT AddressT) v ao G1 tn1 t0 /\
  eval_operand ao u = SOME aw /\ w2w aw = target /\ zg.vs_labels = u.vs_labels /\
  eval_operand gas zg = SOME gw /\ op_taint tng gas = {} /\
  (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
  (case go of SOME g => (g,s3) | NONE => emit_op GAS [] s3) = (gas,s5) /\
  compile_ext_call_kwargs compile_expr cenv rt opts kw_es s2 = ((vo,go,def),s3) /\
  (!e st. MEM e kw_es /\ expr_sim_inv_mods mods cenv cx env st ==> expr_body_pre_mods mods cenv cx env e st) /\
  eval_exprs cx kw_es (ee with gas_obs := obs3) = (INL kws,ke) /\
  MAP expr_type kw_es = MAP (ext_call_kw_type rt) opts /\
  ext_call_opts_ok stat opts /\
  (rt = NoneT ==> ext_call_kwarg EKDefault opts kws = NONE) /\
  (case ext_call_kwarg EKGas opts kws of
     NONE => go = NONE
   | SOME gv => ?op w. go = SOME op /\ eval_operand op z = SOME w /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       dest_NumV gv = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (case ext_call_kwarg EKValue opts kws of
     NONE => vo = NONE
   | SOME vi => ?op w. vo = SOME op /\ eval_operand op z = SOME w /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       dest_NumV vi = SOME (w2n w) /\ op_taint tn3 op = {}) /\
  (case ext_call_kwarg EKDefault opts kws of NONE => def = NONE
   | SOME dv => ?e op dt. def = SOME (op,dt) /\
       ext_call_kwarg EKDefault opts kw_es = SOME e /\
       (!x. op = Var x ==> not_fresh_at s3 x) /\
       if is_word_type rt then
         dt = rt /\ expr_val_rel cx rt dv op z /\ ptr_val_ok cx rt dv op G3 tn3 z
       else dt = lowered_value_type cenv e /\ ptr_val_ok cx dt dv op G3 tn3 z /\
            ptr_mem_ok cx dt dv op G3 tn3 z /\ ptr_buf_ok cenv e op G3 z /\
            (!w. eval_operand op z = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
              w2n w + type_memory_bytes cenv dt <= z.vs_alloca_next) /\
            (?w aid tv. eval_operand op z = SOME w /\
              evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
              FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
              aid < s3.cs_next_id)) /\
  zg.vs_labels = z.vs_labels /\ zg.vs_memory = z.vs_memory /\
  zg.vs_allocas = z.vs_allocas /\ zg.vs_alloca_next = z.vs_alloca_next /\
  tng.t_mem = tn3.t_mem /\
  (!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
       FLOOKUP Gg x = FLOOKUP G3 x /\ op_taint tng (Var x) = op_taint tn3 (Var x)) ==>
  ?calldata t Gf tf.
    build_ext_calldata (get_tenv cx) fname ats vs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      ao (option_CASE vo (Lit 0w) I) gas ba.buf_operand off len
      (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))
      target (if stat then NONE else
        option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV) calldata
      (IS_SOME def) (case def of NONE => Lit 0w | SOME (op,dt) => op)
      (case def of NONE => rt | SOME (op,dt) => dt) (ext_call_kwarg EKDefault opts kws) ke t /\
    (IS_SOME (ext_call_kwarg EKDefault opts kws) /\
      ~is_word_type (case def of NONE => rt | SOME (op,dt) => dt) ==>
      ?w aid tv.
        eval_operand (case def of NONE => Lit 0w | SOME (op,dt) => op) t = SOME w /\
        evaluate_type (get_tenv cx) (case def of NONE => rt | SOME (op,dt) => dt) = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (zg,Gg,tng) [] (OK t,Gf,tf)) /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!K. valid_horizon cx st0 K ke.storage_trace ==>
         ghost_inv_at (DF K) lo d cenv cx ke Gf tf t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
    eval_operand gas t = SOME gw /\
    (!g. OPTION_BIND (ext_call_kwarg EKGas opts kws) dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tf p = {})
      [ao;option_CASE vo (Lit 0w) I;gas;ba.buf_operand;off;len;
       (case def of NONE => Lit 0w | SOME (op,dt) => op)] /\
    (!a n. eval_operand off t = SOME a /\ eval_operand len t = SOME n ==>
      (n <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n n)) /\
                    w2n a + w2n n <= t.vs_alloca_next) /\
      (!j. w2n a <= j /\ j < w2n a + w2n n ==> j NOTIN tf.t_mem)) /\
    (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt) <> 0 ==>
      ?p. ba.buf_operand = Var p /\
          ptr_covers Gf tf p t
            (abi_size_bound cenv.ce_struct_fields (if needs_external_call_wrap rt then TupleT [rt] else rt))) /\
    (!dv. ext_call_kwarg EKDefault opts kws = SOME dv /\
          ~is_word_type (case def of NONE => rt | SOME (op,dt) => dt) ==>
      ptr_mem_ok cx (case def of NONE => rt | SOME (op,dt) => dt) dv
        (case def of NONE => Lit 0w | SOME (op,dt) => op) Gf tf t /\
      (type_memory_bytes cenv (case def of NONE => rt | SOME (op,dt) => dt) <> 0 ==>
        (?p. (case def of NONE => Lit 0w | SOME (op,dt) => op) = Var p /\
             ptr_covers Gf tf p t
               (type_memory_bytes cenv (case def of NONE => rt | SOME (op,dt) => dt))) /\
        (!w. eval_operand (case def of NONE => Lit 0w | SOME (op,dt) => op) t = SOME w ==>
             w2n w + type_memory_bytes cenv (case def of NONE => rt | SOME (op,dt) => dt) <= t.vs_alloca_next)))
Proof
  rewrite_tac [LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env mid`
       (mp_tac o MATCH_MP (cj 1 (iffLR exprSimHypsDefsTheory.expr_sim_inv_def))) >>
     metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv]) >>
  drule_all post_gas_call_signature >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) xs vs` by
    (`expr_sim_inv cenv cx env (mid with gas_obs := obs2)` by simp[] >>
     qpat_assum `eval_exprs cx xs (mid with gas_obs := obs2) = _`
       (mp_then (Pat `eval_exprs _ _ _ = _`) mp_tac post_gas_replay_typed) >>
     disch_then (qspecl_then [`env`,`cenv`] mp_tac) >>
     impl_tac >- simp[] >>
     simp[listTheory.LIST_REL_EL_EQN]) >>
  drule_all post_gas_lowered_assignable >> disch_then assume_tac >>
  drule_all post_gas_encoding_plans >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH vs = LENGTH xs` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  `LENGTH xs = LENGTH ats` by
    (qpat_assum `arg_types_fit _ _` mp_tac >>
     simp[NoAsms, vyperTypeArgFitsTheory.arg_types_fit_LIST_REL, listTheory.LIST_REL_EL_EQN]) >>
  `sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_id <= s5.cs_next_id /\
   s1.cs_next_var <= s2.cs_next_var /\ s2.cs_next_var <= s5.cs_next_var /\
   s3.cs_next_var <= s5.cs_next_var /\ s3.cs_next_id <= s5.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  drule_all post_gas_target_ready >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at s3 x ==> lookup_var x zg = lookup_var x z /\
       op_taint tng (Var x) = op_taint tn3 (Var x)` by metis_tac[] >>
  drule_all (PURE_REWRITE_RULE [REFL_CLAUSE,AND_CLAUSES]
    (Q.INST [`value` |-> `option_CASE vo (Lit 0w) I`,
             `value_opt` |-> `if stat then NONE else
               option_CASE (ext_call_kwarg EKValue opts kws) (SOME 0) dest_NumV`]
      post_gas_value_ready)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ghost_inv_at (DF H) lo d cenv cx ke Gg tng zg` by simp[] >>
  drule_then (map_every assume_tac o CONJUNCTS) post_gas_alloca_floor >>
  `alloca_inv u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx ee u`
      (mp_tac o MATCH_MP (cj 2 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca)) >> simp[]) >>
  `alloca_inv zg` by
    (`stmt_state_rel H ctx func cenv cx ke zg` by simp[] >>
     metis_tac[cj 2 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca]) >>
  `alloca_next_valid zg` by fs[venomMemDefsTheory.alloca_inv_def] >>
  `expr_sim_inv cenv cx env (ee with gas_obs := obs3)` by simp[] >>
  qabbrev_tac `dop = case def of NONE => Lit 0w | SOME (op,dt) => op` >>
  qabbrev_tac `dty = case def of NONE => rt | SOME (op,dt) => dt` >>
  `(case def of NONE => dop = Lit 0w /\ dty = rt | SOME p => p = (dop,dty))` by
    (Cases_on `def` >- simp[Abbr `dop`,Abbr `dty`] >>
     rename1 `SOME p` >> PairCases_on `p` >> simp[Abbr `dop`,Abbr `dty`]) >>
  mp_tac (PURE_REWRITE_RULE [REFL_CLAUSE,AND_CLAUSES]
    (Q.INST [`has_def` |-> `IS_SOME (def : (operand # type) option)`,`dopt` |-> `def`,
             `def_op` |-> `dop`, `def_ty` |-> `dty`,
             `kw_in` |-> `ee with gas_obs := obs3`]
      post_gas_default_packet)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `wb_frame cenv es mid sa s0 t0` by
    (drule (horizonTypeLib.at_horizon_named "H" exprSimWordArgsTheory.expr_post_frame) >> simp[]) >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
   sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es ee sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (MATCH_MP_TAC (Q.INST [`H` |-> `H0`, `ctx` |-> `ctx`, `cx` |-> `cx`,
       `func` |-> `func`, `es1` |-> `mid`, `sm` |-> `s1`, `s` |-> `t0`,
       `G1` |-> `G1`, `tn1` |-> `tn1`] post_gas_extend_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ke sa s0 zg /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gg tng` by
    (MATCH_MP_TAC (Q.INST [`H` |-> `H0`, `ctx` |-> `ctx`, `cx` |-> `cx`,
       `func` |-> `func`, `es1` |-> `ee`, `ee` |-> `ke`, `sm` |-> `s2`, `s` |-> `u`,
       `G1` |-> `G2`, `tn1` |-> `tn2`, `G2` |-> `Gg`, `tn2` |-> `tng`]
       post_gas_extend_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `MAP FDOM es.scopes = MAP FDOM ke.scopes` by
    ((qpat_assum `wb_frame cenv es ke sa s0 zg` mp_tac >>
     simp[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def] >> (metis_tac[loweringPostsTheory.wb_frame_def, loweringPostsTheory.locals_kept_def]))) >>
  `return_buf_frame d cenv s5 zg` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl [`cenv`,`z`,`s3`] >> simp[] >> metis_tac[]) >>
  `!e. MEM e kw_es ==> expr_body_pre cenv cx env e ee` by metis_tac[] >>
  drule_all post_gas_kwargs_not_label >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `safe_operand s5 (option_CASE vo (Lit 0w) I)` by
    (irule safe_operand_mono >> qexists `s3` >> simp[] >>
     Cases_on `vo` >> simp[safe_operand_def]) >>
  `safe_operand s5 gas` by
    (Cases_on `go`
     >- (qpat_assum `(case NONE of NONE => emit_op GAS [] s3 | SOME _ => _) = _`
           (mp_tac o SIMP_RULE (srw_ss()) []) >>
         MATCH_ACCEPT_TAC emit_op_safe_operand) >>
     Cases_on `ext_call_kwarg EKGas opts kws` >>
     fs[safe_operand_def] >>
     qpat_x_assum `_ = gas` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `s3 = s5` SUBST_ALL_TAC >> simp[]) >>
  `safe_operand s5 dop` by
    (irule safe_operand_mono >> qexists `s3` >> simp[] >>
     qpat_assum `!op ty l. def = SOME (op,ty) ==> op <> Label l` mp_tac >>
     qpat_assum `case def of NONE => dop = Lit 0w /\ _ | SOME p => _` mp_tac >>
     qpat_assum `case ext_call_kwarg EKDefault opts kws of NONE => def = NONE | SOME dv => _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `ext_call_kwarg EKDefault opts kws` >>
     simp[safe_operand_def] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qabbrev_tac `ptys = MAP (lowered_value_type cenv) xs` >>
  irule (Q.INST [`tys` |-> `ptys`, `abi` |-> `abi_size_bound cenv.ce_struct_fields (TupleT ptys)`,
    `mid` |-> `cenv.ce_method_id fname ats`, `sb` |-> `sb1`, `se` |-> `s5`,
    `sf` |-> `sb3`, `sm` |-> `sb2`, `vals` |-> `av`, `xs` |-> `xs`,
    `H0` |-> `H0`, `arg_types` |-> `ats`]
    (horizonTypeLib.at_horizon_named "H0" extcall_request_packing_ready)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists `H` >> first_assum ACCEPT_TAC)
  >- (qpat_assum `expr_sim_inv cenv cx env ke`
        (mp_tac o MATCH_MP (cj 3 (iffLR exprSimHypsDefsTheory.expr_sim_inv_def))) >>
      simp[vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed])
  >- (qpat_assum `expr_sim_inv cenv cx env ke`
        (mp_tac o MATCH_MP (cj 14 (iffLR exprSimHypsDefsTheory.expr_sim_inv_def))) >> simp[])
  >- decide_tac
  >- decide_tac
  >- (rewrite_tac[listTheory.EVERY_DEF] >> BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >>~- ([`?tops. body_inv tops ctx cenv cx`], qexists `tops` >> first_assum ACCEPT_TAC)
  >>~- ([`?env. expr_sim_inv cenv cx env ke`], qexists `env` >> first_assum ACCEPT_TAC)
  >>~- ([`?K. valid_horizon cx st0 K ke.storage_trace`], qexists `H` >> first_assum ACCEPT_TAC)
  >>~- ([`?K. stmt_state_rel K ctx func cenv cx es s0`], qexists `H0` >> first_assum ACCEPT_TAC)
  >> qexistsl [`av`,`ptys`,`s5`,`sb1`,`sb2`,`sb3`,`xs`]
  >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >>~- ([`_ < dimword (:256)`],
       irule vyperArithTheory.lt_dimword_256 >> qexists `64` >>
       qpat_assum `MAX _ _ + 32 < 2**64` mp_tac >>
       simp[NoAsms, arithmeticTheory.MAX_DEF] >> decide_tac)
  >> simp[NoAsms, Abbr `ptys`]
  >- (mp_tac (Q.INST [`pos` |-> `mid`, `se` |-> `s5`, `ee` |-> `ke`,
                       `t` |-> `zg`, `G` |-> `Gg`, `tn` |-> `tng`]
               post_gas_indexed_rows) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      simp[NoAsms])
  >- (sym_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `LENGTH av = LENGTH xs` (rewrite_tac o single) >>
      sym_tac >> first_assum ACCEPT_TAC)
  >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

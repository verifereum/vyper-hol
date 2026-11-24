(* The materialization source is interpreted at the endpoint of the
   ordinary unwrap, not at the endpoint of a second execution. *)
Theory createCtorMaterializePhysicalMods
Ancestors
  createCtorMaterializePhysical createExprSizeExitDefsMods
  assignEffectfulIndexPhysical bodyMemSnapshotSourceLocation
  immutableDeployPhysicalSource aggregateEvaluatedLayout bodyFullStructLitInputs
  exprBodyPreProps exprSimHyps exprLowering context loweringPosts bodyPtrDefs
  assignTuplePtrCopyLen[qualified] loweringStateRelDefs vyperState
  vyperTypeExprSoundness valueCopyBytes finite_map pred_set
  exprSimConcatSource exprSimAbiEncodeArgsPhysicalCapacity
  exprSimAbiEncodeRuntimeInputs exprSimSource exprSimProps
  vyperTypeEvalSoundness vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  vyperTypeEvalCaseProofs vyperTypeArgFits vyperTypeDefaults vyperTypeInvariants
  vyperInterpreter vyperValueOperation vyperStatePreservation
  vyperTypeSystem vyperTyping vyperValue vyperAST allocLimits vyperContext
  exprSimHypsDefs list exprSafeOperand vyperTypeCallGraph
  bodyFullPostsMods valueTypingMemoryProps
Libs monadsyntax

(* A well-typed argument read keeps the linked invariant for the next read. *)
Theorem ctor_read_eval_preserves_mods[local]:
  expr_sim_inv_mods mods ce cx env st /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (rr,fin) ==>
  expr_sim_inv_mods mods ce cx env fin
Proof
  strip_tac >>
  `runtime_consistent env cx st /\ functions_well_typed cx` by
    fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  drule_all_then assume_tac eval_expr_preserves_runtime_consistent >>
  `outcomes_accounts_typed fin.outcomes` by
    (rw[outcomes_accounts_typed_def] >>
     drule_then assume_tac (cj 5 eval_outcome_suffix_mutual) >>
     drule_then irule outcome_suffix_EVERY >>
     fs[expr_sim_inv_mods_def, outcomes_accounts_typed_def]) >>
  `IS_SOME fin.outcomes` by
    (drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_outcomes_some >>
     fs[expr_sim_inv_mods_def]) >>
  `popped_keys_indexed fin.scopes` by
    (drule_at (Pat `eval_expr _ _ _ = _`) eval_expr_popped_keys_indexed >>
     fs[expr_sim_inv_mods_def]) >>
  fs[expr_sim_inv_mods_def, runtime_consistent_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ctor_read_args_cons[local]:
  eval_exprs cx (head::args) st = (INL vs,fin) ==>
  ?v mid tail raw.
    eval_expr cx head st = (INL raw,mid) /\
    read_result cx raw mid = (INL v,mid) /\
    eval_exprs cx args mid = (INL tail,fin) /\ vs = v::tail
Proof
  pure_once_rewrite_tac[evaluate_def] >>
  simp_tac std_ss [bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  drule_then SUBST_ALL_TAC read_result_state >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ctor_read_arg_types_mods[local]:
  !args st vs fin.
    expr_sim_inv_mods mods ce cx env st /\
    EVERY (\e. well_typed_expr env e /\ alloc_limits_expr ce e /\
               call_evaluation_safe cx (int_calls_expr e)) args /\
    eval_exprs cx args st = (INL vs,fin) /\
    (!e s v t. MEM e args /\ expr_sim_inv_mods mods ce cx env s /\
      bind (eval_expr cx e) (read_result cx) s = (INL v,t) ==>
      value_runtime_typed env (lowered_value_type ce e) v) ==>
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs
Proof
  Induct >- simp[Once evaluate_def, return_def] >>
  pure_rewrite_tac[EVERY_DEF] >> rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac ctor_read_args_cons >> gvs[] >>
  conj_tac
  >- (first_x_assum irule >> simp[] >>
      qexistsl_tac [`st`, `mid`] >> simp[bind_def]) >>
  `expr_sim_inv_mods mods ce cx env mid` by
    (drule_all ctor_read_eval_preserves_mods >> simp[]) >>
  qpat_x_assum `!st vs fin. _` irule >>
  reverse conj_tac
  >- (goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem ctor_read_arg_layouts_mods[local]:
  !args vs.
    env_consistent env cx st /\ EVERY (well_typed_expr env) args /\
    EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args /\
    LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs ==>
    arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
    ?ptvs stvs.
      LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
        (MAP (lowered_value_type ce) args) ptvs /\
      LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
        (MAP expr_type args) stvs /\
      values_have_types ptvs vs
Proof
  Induct >> Cases_on `vs` >>
  simp[arg_types_fit_LIST_REL, values_have_types_LIST_REL] >>
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
           well_formed_type env.type_defs ty` by
    (simp[well_formed_type_def] >> metis_tac[env_consistent_var_type_evaluates]) >>
  drule_all well_typed_expr_type_well_formed >>
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `stv` assume_tac) >>
  qpat_x_assum `value_runtime_typed _ _ _`
    (qx_choose_then `ptv` strip_assume_tac o REWRITE_RULE[value_runtime_typed_def]) >>
  first_x_assum drule_all >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`ptvs`, `stvs`] strip_assume_tac))
  >- fs[arg_types_fit_LIST_REL] >>
  qexistsl_tac [`ptv::ptvs`, `stv::stvs`] >>
  fs[values_have_types_LIST_REL] >> metis_tac[]
QED

Theorem ctor_read_intcall_cast[local]:
  get_module_code cx src = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,params,dflts,ret,bd) /\
  bind (eval_expr cx (Call ty (IntCall (src,fn)) args drv)) (read_result cx) es =
    (INL v,ee) ==>
  ?rtv. evaluate_type (get_tenv cx) ret = SOME rtv /\ value_has_type rtv v
Proof
  strip_tac >>
  qpat_x_assum `bind _ _ _ = _`
    (assume_tac o ONCE_REWRITE_RULE [evaluate_def]) >>
  fs[ignore_bind_def] >>
  rpt (dxrule bind_split >> strip_tac >> gvs[]) >>
  gvs[lift_option_type_def, return_def, raise_def, read_result_def] >>
  Cases_on `evaluate_type (get_tenv cx) ret` >> gvs[raise_def, return_def] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >> gvs[raise_def, return_def] >>
  metis_tac[safe_cast_result_well_typed]
QED

Theorem ctor_read_intcall_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\
  well_typed_expr env (Call ty (IntCall fid) args drv) /\
  bind (eval_expr cx (Call ty (IntCall fid) args drv)) (read_result cx) es =
    (INL v,ee) ==>
  value_runtime_typed env (lowered_value_type ce (Call ty (IntCall fid) args drv)) v
Proof
  strip_tac >> PairCases_on `fid` >>
  rename1 `well_typed_expr env (Call _ (IntCall (src,fn)) _ _)` >>
  `?sg. FLOOKUP env.fn_sigs (src,fn) = SOME sg` by
    fs[well_typed_expr_def] >>
  drule_all expr_sim_inv_mods_return_type >> strip_tac >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (drule expr_sim_inv_mods_env >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  drule_all ctor_read_intcall_cast >>
  simp[value_runtime_typed_def, lowered_value_type_def]
QED

Theorem ctor_read_annotation_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
  disch_then (qspec_then `env` mp_tac) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >>
  simp[]
QED

Theorem ctor_read_concat_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env (Builtin ty (Concat n) args) /\
  alloc_limits_expr ce (Builtin ty (Concat n) args) /\
  call_evaluation_safe cx (int_calls_expr (Builtin ty (Concat n) args)) /\
  bind (eval_expr cx (Builtin ty (Concat n) args)) (read_result cx) es = (INL v,ee) ==>
  value_runtime_typed env (lowered_value_type ce (Builtin ty (Concat n) args)) v
Proof
  strip_tac >>
  `well_typed_exprs env args /\ 2 <= LENGTH args /\
   SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   ((ty = BaseT (BytesT (Dynamic n)) /\ EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
    (ty = BaseT (StringT n) /\ EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args)))` by
    (qpat_x_assum `well_typed_expr _ _` mp_tac >>
     simp[Once well_typed_expr_def, well_typed_builtin_app_def] >> rpt strip_tac >> fs[]) >>
  `call_evaluation_safe cx (int_calls_exprs args)` by fs[int_calls_expr_def] >>
  `SUM (MAP (concat_payload_capacity o expr_type) args) < 2 ** 64` by
    (qspec_then `MAP expr_type args` strip_assume_tac concat_alloc_size_bounds >>
     fs[alloc_limits_expr_def, MAP_MAP_o]) >>
  `(SUM (MAP (concat_payload_capacity o expr_type) args) + 31) DIV 32 <=
   SUM (MAP (concat_payload_capacity o expr_type) args) + 31` by simp[arithmeticTheory.DIV_LESS_EQ] >>
  `MAP bytelike_type_bound (MAP expr_type args) = MAP concat_payload_capacity (MAP expr_type args)` by
    (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
  drule eval_expr_concat_bind >> disch_then (qspecl_then [`cx`, `ty`, `n`] SUBST_ALL_TAC) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_exprs cx args es` >> Cases_on `q` >> simp[] >>
  rename1 `eval_exprs cx args es = (INL vs, st)` >>
  `exprs_runtime_typed env args vs` by
    (irule abi_encode_eval_exprs_runtime_typed >> simp[] >>
     qexistsl_tac [`cx`,`es`,`st`] >>
     qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
     simp[expr_sim_inv_mods_def, runtime_consistent_def]) >>
  `LIST_REL (\t v. ?tv. evaluate_type env.type_defs t = SOME tv /\ value_has_type tv v)
     (MAP expr_type args) vs` by
    fs[exprs_runtime_typed_def, value_runtime_typed_def, LIST_REL_EL_EQN, EL_MAP] >>
  gvs[lowered_value_type_def]
  >- (drule_all typed_bytes_operands >> strip_tac >>
      mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
        evaluate_concat_typed_bytes) >>
      (impl_tac >- fs[]) >> strip_tac >>
      gvs[concat_map_ctor_11, read_result_def, return_def] >> strip_tac >>
      gvs[concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
          type_slot_size_def, value_has_type_def, MAP_MAP_o,
          vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]) >>
  drule_all typed_string_operands >> strip_tac >>
  mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
    evaluate_concat_typed_string) >>
  (impl_tac >- fs[]) >> strip_tac >>
  gvs[concat_map_ctor_11, read_result_def, return_def] >> strip_tac >>
  gvs[concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
      type_slot_size_def, value_has_type_def, MAP_MAP_o,
      vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]
QED

Theorem ctor_read_abi_bytes[local]:
  LENGTH (abi_encode_method_id_bytes mid ++ bs) <= cap + abi_encode_method_id_size mid /\
  (case mid of NONE => T | SOME sel => LENGTH sel = 4) /\
  32 + 32 * word_size (cap + (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64 ==>
  value_runtime_typed env (BaseT (BytesT (Dynamic (cap + if IS_SOME mid then 4 else 0))))
    (BytesV (abi_encode_method_id_bytes mid ++ bs))
Proof
  `!k. 32 + 32 * word_size k < 2 ** 64 ==>
       k < dimword(:256) /\ word_size k + 1 <= dimword(:256)` by
    (gen_tac >> qspec_then `k` assume_tac le_word_size_mul >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  Cases_on `mid` >>
  simp[abi_encode_method_id_size_def, vyperASTTheory.abi_encode_method_id_bytes_def] >>
  strip_tac >> fs[] >> res_tac >>
  fs[value_runtime_typed_def, evaluate_type_def, type_slot_size_def,
     value_has_type_def]
QED

Theorem ctor_read_abi_from_args_mods[local]:
  well_typed_type_builtin_args (AbiEncode ensure mid) target (MAP expr_type args) /\
  alloc_limits_expr ce (TypeBuiltin ann (AbiEncode ensure mid) target args) /\
  env.type_defs = get_tenv cx /\ sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
  LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
    (MAP (lowered_value_type ce) args) ptvs /\
  LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
    (MAP expr_type args) stvs /\
  values_have_types ptvs vs /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL v ==>
  value_runtime_typed env
    (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) v
Proof
  strip_tac >> drule alloc_limits_abi_encode_output >> strip_tac >>
  gvs[well_typed_type_builtin_args_def] >>
  Cases_on `LENGTH args = 1 /\ ~ensure`
  >- (Cases_on `args` >> gvs[arg_type_fits_def, values_have_types_LIST_REL] >>
      gvs[evaluate_type_builtin_def, vyperABITheory.needs_external_call_wrap_def,
          CaseEq "sum", lowered_value_type_def] >>
      drule_all abi_args_physical_singleton_capacity >>
      disch_then (qspec_then `mid` assume_tac) >>
      irule ctor_read_abi_bytes >> simp[]) >>
  `1 <= LENGTH args` by (Cases_on `args` >> fs[]) >>
  `~(~ensure /\ needs_external_call_wrap (TupleT (MAP expr_type args)))` by
    (simp[vyperABITheory.needs_external_call_wrap_def] >>
     metis_tac[arithmeticTheory.EQ_LESS_EQ]) >>
  gvs[evaluate_type_builtin_def, CaseEq "sum", lowered_value_type_def, SF ETA_ss] >>
  drule_all abi_args_physical_tuple_capacity >>
  disch_then (qspec_then `mid` assume_tac) >>
  irule ctor_read_abi_bytes >>
  simp[] >>
  Cases_on `LENGTH args = 1` >> gvs[]
QED

Theorem ctor_physical_read_ind_mods[local]:
  !ce e es v ee.
    (!u. well_typed_expr env u ==> arg_type_fits (lowered_value_type ce u) (expr_type u)) /\
    expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
    alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e) /\
    bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    value_runtime_typed env (lowered_value_type ce e) v
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def, evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
          evaluate_type_def, value_runtime_typed_def, value_has_type_def,
          type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def, evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
          evaluate_type_def, value_runtime_typed_def, value_has_type_def,
          type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[Once evaluate_def, bind_def, return_def, read_result_def, evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_literal_def, well_formed_type_def,
          evaluate_type_def, value_runtime_typed_def, value_has_type_def,
          type_slot_size_def, compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >~ [`Builtin _ NamedConst [Literal _ (StringL _)]`]
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[evaluate_def, bind_def, ignore_bind_def, return_def, read_result_def,
          type_check_def, assert_def, builtin_args_length_ok_def, get_accounts_def,
          is_self_codesize_def, lift_sum_def, evaluate_builtin_def, precompile_builtin_def,
          evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def,
          well_typed_literal_def, well_formed_type_def, evaluate_type_def,
          value_runtime_typed_def, value_has_type_def, type_slot_size_def,
          compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >~ [`Builtin _ NamedConst [Literal _ (BytesL _)]`]
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[evaluate_def, bind_def, ignore_bind_def, return_def, read_result_def,
          type_check_def, assert_def, builtin_args_length_ok_def, get_accounts_def,
          is_self_codesize_def, lift_sum_def, evaluate_builtin_def, precompile_builtin_def,
          evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def,
          well_typed_literal_def, well_formed_type_def, evaluate_type_def,
          value_runtime_typed_def, value_has_type_def, type_slot_size_def,
          compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >~ [`Builtin _ NamedConst [Literal _ (HexBytesL _)]`]
  >- (rpt gen_tac >> simp[lowered_value_type_def] >> strip_tac >>
      gvs[evaluate_def, bind_def, ignore_bind_def, return_def, read_result_def,
          type_check_def, assert_def, builtin_args_length_ok_def, get_accounts_def,
          is_self_codesize_def, lift_sum_def, evaluate_builtin_def, precompile_builtin_def,
          evaluate_literal_def] >>
      gvs[well_typed_expr_def, well_typed_builtin_app_def, expr_type_def,
          well_typed_literal_def, well_formed_type_def, evaluate_type_def,
          value_runtime_typed_def, value_has_type_def, type_slot_size_def,
          compatible_bound_def] >>
      imp_res_tac word_size_monotone >> decide_tac)
  >~ [`Builtin _ (Concat _) _`]
  >- (rpt gen_tac >> strip_tac >> drule_all ctor_read_concat_mods >> simp[])
  >~ [`TypeBuiltin _ (AbiEncode _ _) _ _`]
  >- (suspend "abi")
  >~ [`Call _ (IntCall _) _ _`]
  >- (rpt gen_tac >> strip_tac >> drule_all ctor_read_intcall_mods >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all ctor_read_annotation_mods >> simp[lowered_value_type_def]
QED

Resume ctor_physical_read_ind_mods[abi]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target args)` >>
  `EVERY (\e. well_typed_expr env e /\ alloc_limits_expr ce e /\
              call_evaluation_safe cx (int_calls_expr e)) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     fs[Once well_typed_expr_def, int_calls_expr_def, alloc_limits_expr_def] >>
     metis_tac[well_typed_exprs_member, alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]) >>
  `well_typed_type_builtin_args (AbiEncode ensure mid) target (MAP expr_type args)` by
    fs[Once well_typed_expr_def] >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def, lift_sum_def] >>
  Cases_on `eval_exprs cx args es` >> Cases_on `q` >>
  simp[return_def, raise_def, read_result_def] >>
  Cases_on `1 <= LENGTH args` >> simp[return_def, raise_def] >>
  simp[CaseEq "sum", read_result_def, return_def] >> rpt strip_tac >>
  rename1 `eval_exprs cx args es = (INL vs, st)` >>
  Cases_on `evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs` >>
  gvs[return_def, raise_def, read_result_def] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
    (irule ctor_read_arg_types_mods >>
     qexistsl_tac [`cx`,`ee`,`mods`,`es`] >> simp[] >> rpt strip_tac >>
     Cases_on `LENGTH args = 1 /\ ~ensure`
     >- (gvs[LENGTH_EQ_NUM_compute] >> first_x_assum irule >>
         goal_assum (drule_at Any) >> simp[]) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (well_typed_expr env) args` by fs[EVERY_MEM] >>
  `EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args` by
    (fs[EVERY_MEM] >> rpt strip_tac >> metis_tac[]) >>
  drule_all ctor_read_arg_layouts_mods >> strip_tac >>
  irule ctor_read_abi_from_args_mods >> simp[] >>
  qexistsl_tac [`cx`,`ptvs`,`stvs`,`vs`] >> simp[]
QED

Finalise ctor_physical_read_ind_mods[local]

Theorem ctor_physical_read_mods[local]:
  (!u. well_typed_expr env u ==> arg_type_fits (lowered_value_type ce u) (expr_type u)) ==>
  !e es v ee. expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
    alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e) /\
    bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    value_runtime_typed env (lowered_value_type ce e) v
Proof
  rpt strip_tac >> drule_all ctor_physical_read_ind_mods >> simp[]
QED

Theorem ctor_physical_static_mods[local]:
  expr_sim_inv_mods mods ce cx env es ==>
  !e. well_typed_expr env e ==>
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    (post_value_type ce e = expr_type e \/
     post_value_type ce e = lowered_value_type ce e) /\
    (post_value_type ce e = lowered_value_type ce e \/
     is_bytestring_type (post_value_type ce e) /\
     is_bytestring_type (lowered_value_type ce e))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
      gvs[vyperTypeSystemTheory.well_typed_expr_def, lowered_value_type_def,
          vyperASTTheory.expr_type_def] >>
      first_x_assum (drule_then SUBST1_TAC) >>
      rename1 `type_widens_to env.type_defs sg.ret_ty ty` >>
      `arg_type_fits sg.ret_ty ty` by
        fs[vyperTypeSystemTheory.type_widens_to_def] >>
      Cases_on `is_word_type ty` >> simp[]
      >- metis_tac[compileEnvTheory.type_widens_to_word] >>
      Cases_on `is_bytestring_type ty` >> simp[] >>
      disj2_tac >> irule compileEnvTheory.arg_type_fits_bytestring_source >>
      goal_assum drule >> simp[]) >>
  `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates,
              vyperTypeSystemTheory.well_formed_type_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
  `post_value_type ce e = expr_type e` by
    metis_tac[post_value_type_not_int_call] >>
  drule_all exprSimIfExpCompatTheory.ifexp_lowered_type_classify >>
  strip_tac >> gvs[]
QED

Theorem ctor_physical_memory_size_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME rt ==>
  type_memory_bytes ce ty = type_memory_size rt
Proof
  strip_tac >> irule typedMemoryCopyTheory.typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >> fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem ctor_physical_bound_read_type_mods:
  expr_body_pre_mods mods ce cx env e st /\
  bind (eval_expr cx e) (read_result cx) st = (INL v,ee) ==>
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       value_has_type tv v
Proof
  strip_tac >>
  `expr_sim_inv_mods mods ce cx env st /\ well_typed_expr env e /\
   alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e)` by
    fs[expr_body_pre_mods_def] >>
  `env.type_defs = get_tenv cx` by
    metis_tac[expr_sim_inv_mods_env, env_consistent_type_defs_get_tenv] >>
  drule ctor_physical_static_mods >> strip_tac >>
  `!u. well_typed_expr env u ==>
       arg_type_fits (lowered_value_type ce u) (expr_type u)` by metis_tac[] >>
  drule_all ctor_physical_read_mods >> simp[value_runtime_typed_def]
QED

Theorem ctor_materialize_unwrap_retag_mods:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce ty e sa = (vv,sm) /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv a /\
  ~is_word_type (lowered_value_type ce e) /\
  unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) mid = (op,su) ==>
  unwrap_value ce vv mid = (op,su) /\
  ~is_word_type (post_value_type ce e) /\
  ?rty. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rty /\
        (!val. read_result cx tv ee = (INL val,ee) ==> value_has_type rty val) /\
        type_memory_bytes ce (post_value_type ce e) = type_memory_size rty /\
        type_memory_size rty < 2 ** 64
Proof
  strip_tac >>
  `expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
   alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e)` by
    fs[expr_body_pre_mods_def] >>
  drule ctor_physical_static_mods >>
  disch_then (fn th => assume_tac th >> qspec_then `e` drule th) >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[is_bytestring_word_type] >>
  `unwrap_value ce vv mid = (op,su)` by
    (Cases_on `vv` >- fs[ext_call_arg_value_def] >>
     rename1 `LocatedValue tag p` >>
     `p.ptr_location <> LocMemory ==> tag = lowered_value_type ce e` by
       (strip_tac >>
        `post_value_type ce e = lowered_value_type ce e` by
          (drule snapshot_changed_type_location >> fs[vv_location_def]) >>
        fs[bodyFullPostsModsTheory.vv_post_mods_def,
           bodyFullPostsModsTheory.vv_holds_mods_def, vv_holds_def] >>
        Cases_on `p.ptr_location = LocCode` >> gvs[]) >>
     Cases_on `p.ptr_location = LocMemory`
     >- (`~is_word_type tag` by
           (fs[bodyFullPostsModsTheory.vv_post_mods_def,
               bodyFullPostsModsTheory.vv_holds_mods_def, vv_holds_def] >>
            metis_tac[is_bytestring_word_type]) >>
         gvs[ext_call_arg_value_def, unwrap_value_def]) >>
     gvs[ext_call_arg_value_def]) >>
  `bind (eval_expr cx e) (read_result cx) es = (INL v,ee)` by simp[bind_def] >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all ctor_read_annotation_mods >> simp[]) >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (irule ctor_physical_read_mods >> simp[] >>
     metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >> simp[env_consistent_def, env_context_consistent_def]) >>
  `value_runtime_typed env (post_value_type ce e) v` by metis_tac[] >>
  `arg_type_fits (post_value_type ce e) (expr_type e)` by
    metis_tac[ifexp_arg_type_fits_refl] >>
  qpat_x_assum `value_runtime_typed _ (expr_type _) _` mp_tac >>
  simp[value_runtime_typed_def] >>
  disch_then (qx_choose_then `aty` strip_assume_tac) >>
  qpat_x_assum `value_runtime_typed _ (post_value_type _ _) _` mp_tac >>
  simp[value_runtime_typed_def] >>
  disch_then (qx_choose_then `rty` strip_assume_tac) >>
  qexists_tac `rty` >> simp[] >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size rty` by
    metis_tac[ctor_physical_memory_size_mods] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size aty` by
    metis_tac[ctor_physical_memory_size_mods] >>
  `type_memory_size rty <= type_memory_size aty` by
    metis_tac[cj 1 arg_fits_evaluated_memory_size] >>
  drule alloc_limits_expr_type_alloc_ok >>
  `~is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  simp[type_alloc_ok_def]
QED

Theorem ctor_materialize_unwrap_physical_mods:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e es = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  ~is_word_type (lowered_value_type ce e) /\
  expr_post_mods H ctx func ce cx e es sa su s0 ee v op z /\
  ptr_val_ok cx (post_value_type ce e) v op Gz tz z /\
  ptr_buf_ok ce e op Gz z /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op z = SOME w ==>
          type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
  wb_frame ce ee ee mid a z /\
  ghost_kept_at lo ce ee mid Ga ta a Gz tz ==>
  (?stv sw.
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
     value_has_type stv v /\ val_wf stv v /\
     type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
     eval_operand op z = SOME sw /\ op_taint tz op = {} /\
     (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
            val_in_memory stv v (w2n sw) mem) /\
     (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= z.vs_alloca_next) /\
     (0 < type_memory_size stv ==>
      ?src. op = Var src /\ ptr_covers Gz tz src z (type_memory_size stv))) /\
  (!p w aid b n.
     not_fresh_at mid p /\ lookup_var p a = SOME w /\ ptr_covers Ga ta p a n /\
     FLOOKUP a.vs_allocas aid = SOME (b,n) /\ aid < mid.cs_next_id /\
     (!id base len. local_region ce ee.scopes a id base len ==>
                    regions_disjoint b n base len) ==>
     lookup_var p z = SOME w /\ ptr_covers Gz tz p z n /\
     FLOOKUP Gz p = FLOOKUP Ga p /\ op_taint tz (Var p) = op_taint ta (Var p) /\
     FLOOKUP z.vs_allocas aid = SOME (b,n) /\
     mem_bytes_at b n z.vs_memory = mem_bytes_at b n a.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tz.t_mem ==> i IN ta.t_mem))
Proof
  strip_tac >> conj_tac
  >- (`expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
       alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e)` by
        fs[expr_body_pre_mods_def] >>
      `env.type_defs = get_tenv cx` by
        metis_tac[expr_sim_inv_mods_env, env_consistent_type_defs_get_tenv] >>
      `bind (eval_expr cx e) (read_result cx) es = (INL v,ee)` by simp[bind_def] >>
      drule ctor_physical_static_mods >> strip_tac >>
      `!u. well_typed_expr env u ==>
           arg_type_fits (lowered_value_type ce u) (expr_type u)` by metis_tac[] >>
      drule_all ctor_physical_read_mods >>
      simp[value_runtime_typed_def] >>
      disch_then (qx_choose_then `stv` strip_assume_tac) >>
      `~is_word_type (post_value_type ce e)` by
        metis_tac[is_bytestring_word_type] >>
      `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
        (Cases_on `post_value_type ce e = lowered_value_type ce e` >> simp[] >>
         drule_all ctor_read_annotation_mods >>
         simp[value_runtime_typed_def] >> metis_tac[]) >>
      `?sw. eval_operand op z = SOME sw` by
        fs[expr_post_mods_def, expr_post_def, expr_val_rel_def] >>
      `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv` by
        metis_tac[ctor_physical_memory_size_mods] >>
      `op_taint tz op = {}` by fs[ptr_val_ok_def] >>
      `!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
             val_in_memory ptv v (w2n sw) mem` by fs[ptr_val_ok_def, ptr_mem_ok_def] >>
      `!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
             val_in_memory stv v (w2n sw) mem` by
        (Cases_on `post_value_type ce e = lowered_value_type ce e`
         >- gvs[] >>
         rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`, `get_tenv cx`, `ptv`] >>
         simp[] >> metis_tac[]) >>
      qexistsl_tac [`stv`, `sw`] >> simp[value_has_type_memory_wf] >>
      conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >> strip_tac >>
      irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
      simp[] >>
      qexistsl_tac [`ce`, `e`] >> simp[]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  simp[regions_disjoint_def] >> rpt gen_tac >> strip_tac >>
  `lookup_var p z = SOME w /\ FLOOKUP Gz p = FLOOKUP Ga p /\
   op_taint tz (Var p) = op_taint ta (Var p)` by metis_tac[] >>
  `ptr_covers Gz tz p z n` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`Ga`,`a`,`ta`] >> simp[]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`mem_bytes_at b n z.vs_memory = _`] >-
    (qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz z.vs_memory = _`
       (qspecl_then [`aid`, `b`, `n`] mp_tac) >> simp[] >>
     disch_then MATCH_MP_TAC >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!aid off sz i. _ ==> i IN ta.t_mem`
    (qspecl_then [`aid`, `b`, `n`, `i`] mp_tac) >> simp[] >>
  disch_then MATCH_MP_TAC >> first_assum ACCEPT_TAC
QED

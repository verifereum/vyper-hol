Theory bodyCopyReadPhysicalTypeMods
Ancestors
  bodyCopyEqualRhsTypeMods bodyCopyAtomicRhsTypeMods bodyCopyAggregateRhsTypeMods
  bodyCopyArgReadTypesMods exprBodyPreCallSafetyProps exprSimSource exprSimConcatSource
  exprSimAbiEncodeArgsPhysicalCapacity exprSimLayoutTransport abiEncodeMaterialize
  exprLowering abiTypeBoundProps vyperTypeEvalSoundness vyperTypeSystem vyperTypeArgFits
  vyperTypeInvariants vyperTypeExprSoundness vyperInterpreter vyperState list
  logArgumentTypes logArgumentTypeEval vyperEventArgCompat typedCopyCompatibility
  exprSimAbiEncodeRuntimeInputs exprBodyPreProps exprBodyPreTypingProps
  typedMemoryCopy loweringPosts allocLimits exprSafeOperand vyperValueOperation
  vyperAST exprSimHypsDefs exprSimHyps vyperTypeCallGraph vyperValue vyperTyping

(* Static compatibility uses the linked struct table: unlike the event
   metadata relation, it does not restrict all struct keys to the root module. *)
Theorem copy_abi_read_fits[local]:
  env_consistent env cx es /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target args) /\
  EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args ==>
  arg_type_fits (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) ann
Proof
  strip_tac >>
  `!t. MEM t (MAP expr_type args) ==>
     abi_size_bound ce.ce_struct_fields t = vyper_abi_size_bound env.type_defs t /\
     abi_embedded_static_size ce.ce_struct_fields t +
       (if is_abi_dynamic ce.ce_struct_fields t then abi_size_bound ce.ce_struct_fields t else 0) =
     vyper_abi_embedded_size env.type_defs t` by
    (simp[MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     `?rt. evaluate_type env.type_defs (expr_type y) = SOME rt` by
       (`well_typed_expr env y` by
          (fs[Once well_typed_expr_def] >> metis_tac[well_typed_exprs_member]) >>
        `well_formed_type env.type_defs (expr_type y)` by
           metis_tac[checked_expr_type_well_formed] >>
        fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
     drule_all abi_props_vyper_typed >> simp[]) >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args)) =
   vyper_abi_size_bound env.type_defs (TupleT (MAP expr_type args))` by
    (irule abi_size_bound_tuple_agrees >> metis_tac[]) >>
  `abi_size_bound ce.ce_struct_fields
       (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
        else TupleT (MAP (lowered_value_type ce) args)) <=
   abi_size_bound ce.ce_struct_fields
       (if LENGTH args = 1 /\ ~ensure then expr_type (HD args)
        else TupleT (MAP expr_type args))` by
    (IF_CASES_TAC
     >- (gvs[LENGTH_EQ_NUM_compute] >>
         metis_tac[cj 1 abi_args_fits_size_bound]) >>
     `arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args)` by
       (qpat_x_assum `EVERY _ args` mp_tac >>
        rpt (pop_assum kall_tac) >> Induct_on `args` >> simp[arg_type_fits_def]) >>
     pure_rewrite_tac[COND_CLAUSES] >> irule (cj 2 abi_args_fits_size_bound) >> simp[]) >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[Once well_typed_expr_def, type_builtin_result_ok_def, abi_encode_size_ok_def,
       abi_encode_source_argument_type] >> strip_tac >> gvs[] >>
  drule checked_abi_encode_method_id_size >> strip_tac >>
  simp[lowered_value_type_def, arg_type_fits_def, SF ETA_ss] >>
  Cases_on `args` >> gvs[] >> rename1 `well_typed_exprs env (h::rest)` >>
  Cases_on `rest` >> Cases_on `ensure` >> gvs[] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem copy_lowered_fits_mods[local]:
  !ce e. expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e ==>
    arg_type_fits (lowered_value_type ce e) (expr_type e)
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`AbiEncode`]
  >- (strip_tac >> strip_tac >> simp[expr_type_def] >>
      irule copy_abi_read_fits >> reverse conj_tac
      >- (qexistsl_tac [`cx`,`env`,`es`] >> simp[] >>
          drule_then assume_tac expr_sim_inv_mods_env >> simp[] >>
          `env.type_defs = get_tenv cx` by metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv] >>
          qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` mp_tac >>
          simp[expr_sim_inv_mods_def]) >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      `well_typed_expr env e` by
        (fs[Once well_typed_expr_def] >> metis_tac[well_typed_exprs_member]) >>
      Cases_on `LENGTH args = 1 /\ ~ensure` >> gvs[] >>
      gvs[LENGTH_EQ_NUM_compute] >> metis_tac[])
  >~ [`IntCall`]
  >- (strip_tac >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      fs[Once well_typed_expr_def] >>
      drule_all expr_sim_inv_mods_return_type >>
      gvs[lowered_value_type_def, expr_type_def, type_widens_to_def,
          GSYM event_arg_compatible_alias_def, event_arg_compatible_reflexive])
  >~ [`Concat`]
  >- (strip_tac >> simp[GSYM event_arg_compatible_alias_def] >>
      irule concat_event_arg_compatible >>
      fs[Once well_typed_expr_def, expr_type_def, event_arg_compatible_reflexive]) >>
  strip_tac >>
  ((simp[lowered_value_type_def] >> NO_TAC) ORELSE
   (simp[GSYM event_arg_compatible_alias_def] >> irule literal_event_arg_compatible >>
    fs[Once well_typed_expr_def, expr_type_def, event_arg_compatible_reflexive]))
QED

Theorem copy_read_annotation_type_mods[local]:
  expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
  call_evaluation_safe cx (int_calls_expr e) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  drule_at (Pat `bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
  disch_then (qspec_then `env` mp_tac) >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >>
  simp[]
QED

(* Concat's physical capacity depends on the operand annotations, so the
   lowered-type induction gives no recursive premise for its arguments. *)
Theorem copy_concat_read_lowered_mods[local]:
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
    (fs[exprs_runtime_typed_def, value_runtime_typed_def, LIST_REL_EL_EQN, EL_MAP]) >>
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

Theorem copy_read_lowered_type_mods[local]:
  !ce e es v ee.
    expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
    alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e) /\
    bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
    value_runtime_typed env (lowered_value_type ce e) v
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> irule (cj 1 copy_literal_read_lowered_mods) >> simp[] >>
      qexistsl_tac [`cx`,`es`,`ee`] >> simp[SF ETA_ss])
  >- (rpt gen_tac >> strip_tac >> irule (cj 2 copy_literal_read_lowered_mods) >> simp[] >>
      qexistsl_tac [`cx`,`es`,`ee`] >> simp[SF ETA_ss])
  >- (rpt gen_tac >> strip_tac >> irule (cj 3 copy_literal_read_lowered_mods) >> simp[] >>
      qexistsl_tac [`cx`,`es`,`ee`] >> simp[SF ETA_ss])
  >~ [`Builtin _ (Concat _) _`]
  >- (rpt gen_tac >> strip_tac >> irule copy_concat_read_lowered_mods >> simp[] >>
      qexistsl_tac [`cx`,`ee`,`es`,`mods`] >> simp[])
  >~ [`TypeBuiltin _ (AbiEncode _ _) _ _`]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      rename1 `well_typed_expr env (TypeBuiltin ann (AbiEncode ensure mid) target args)` >>
      `EVERY (\e. well_typed_expr env e /\ alloc_limits_expr ce e /\
                  call_evaluation_safe cx (int_calls_expr e)) args` by
        (simp[EVERY_MEM] >> rpt strip_tac >>
         fs[Once well_typed_expr_def, int_calls_expr_def, alloc_limits_expr_def] >>
         metis_tac[well_typed_exprs_member, alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]) >>
      `well_typed_type_builtin_args (AbiEncode ensure mid) target (MAP expr_type args)` by
        fs[Once well_typed_expr_def] >>
      `env_consistent env cx es` by metis_tac[expr_sim_inv_mods_env] >>
      `env.type_defs = get_tenv cx` by
        metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv] >>
      `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
        (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `bind _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, vyperContextTheory.type_builtin_args_length_ok_def, lift_sum_def] >>
      Cases_on `eval_exprs cx args es` >> Cases_on `q` >>
      simp[return_def, raise_def, read_result_def] >>
      Cases_on `1 <= LENGTH args` >> simp[return_def, raise_def] >>
      simp[CaseEq "sum", read_result_def, return_def] >> rpt strip_tac >>
      rename1 `eval_exprs cx args es = (INL vs, st)` >>
      Cases_on `evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs` >>
      gvs[return_def, raise_def, read_result_def] >>
      `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
        (irule copy_arg_read_types_from_members_mods >>
         qexistsl_tac [`cx`,`ee`,`mods`,`es`] >> simp[] >> rpt strip_tac >>
         Cases_on `LENGTH args = 1 /\ ~ensure`
         >- (gvs[LENGTH_EQ_NUM_compute] >> first_x_assum irule >>
             goal_assum (drule_at Any) >> simp[]) >>
         fs[EVERY_MEM] >> metis_tac[]) >>
      `EVERY (well_typed_expr env) args` by fs[EVERY_MEM] >>
      `EVERY (\e. arg_type_fits (lowered_value_type ce e) (expr_type e)) args` by
        (fs[EVERY_MEM] >> rpt strip_tac >>
         irule copy_lowered_fits_mods >> simp[] >> metis_tac[]) >>
      drule_all copy_arg_read_layouts_mods >> strip_tac >>
      irule copy_abiencode_lowered_from_args_mods >> simp[] >>
      qexistsl_tac [`cx`,`ptvs`,`stvs`,`vs`] >> simp[])
  >~ [`Call _ (IntCall _) _ _`]
  >- (rpt gen_tac >> strip_tac >> irule copy_intcall_read_lowered_mods >>
      simp[ETA_AX] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all copy_read_annotation_type_mods >> simp[lowered_value_type_def]
QED

(* The post/layout tag can differ from the annotation only at an internal
   call; in that case the post retains exactly the lowered return type. *)
Theorem copy_read_post_tag[local]:
  post_value_type ce e = expr_type e \/ post_value_type ce e = lowered_value_type ce e
Proof
  Cases_on `e` >> simp[] >> rename1 `Call _ ct _ _` >> Cases_on `ct` >>
  simp[expr_type_def, post_value_type_def] >> IF_CASES_TAC >> simp[]
QED

Theorem copy_read_type_memory[local]:
  expr_sim_inv_mods mods ce cx env es /\ evaluate_type (get_tenv cx) ty = SOME rt ==>
  type_memory_bytes ce ty = type_memory_size rt
Proof
  strip_tac >> irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_inv_mods_def]) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
    (drule_then strip_assume_tac) >> simp[]
QED

Theorem copy_read_physical_type_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  ~is_word_type (expr_type e) ==>
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)) /\
  ?pt rt.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt
Proof
  strip_tac >>
  Cases_on `lowered_value_type ce e = expr_type e`
  >- (drule_all copy_equal_rhs_type_mods >> strip_tac >> fs[] >> metis_tac[]) >>
  `expr_sim_inv_mods mods ce cx env es /\ well_typed_expr env e /\
   alloc_limits_expr ce e /\ call_evaluation_safe cx (int_calls_expr e)` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >> simp[expr_body_pre_mods_def]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> simp[] >> metis_tac[]) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[copy_read_post_tag, compatible_word_type] >>
  drule_all materialize_post_lowered_classify >> strip_tac >> simp[] >>
  drule_all copy_read_lowered_type_mods >> strip_tac >>
  `value_runtime_typed env (post_value_type ce e) v` by
    (qspecl_then [`ce`,`e`] strip_assume_tac (Q.GENL [`ce`,`e`] copy_read_post_tag) >>
     simp[] >> drule_all copy_read_annotation_type_mods >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     metis_tac[vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv]) >>
  qpat_x_assum `value_runtime_typed env (lowered_value_type ce e) v`
    (qx_choose_then `rt` strip_assume_tac o REWRITE_RULE[value_runtime_typed_def]) >>
  qpat_x_assum `value_runtime_typed env (post_value_type ce e) v`
    (qx_choose_then `pt` strip_assume_tac o REWRITE_RULE[value_runtime_typed_def]) >>
  qexistsl_tac [`pt`,`rt`] >> gvs[] >>
  irule copy_read_type_memory >> qexistsl_tac [`cx`,`env`,`es`,`mods`] >> fs[]
QED

(* The all-tail expression post supplies the read with a selected gas prefix;
   the typing environment still describes the original source state. *)
Theorem copy_read_physical_type_gas_obs_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  ~is_word_type (expr_type e) ==>
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)) /\
  ?pt rt.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt
Proof
  strip_tac >>
  `(expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) <=>
    expr_body_pre_mods mods ce cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def, expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all copy_read_physical_type_mods >> simp[]
QED

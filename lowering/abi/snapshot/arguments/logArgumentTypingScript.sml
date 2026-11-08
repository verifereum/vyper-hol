(* TOP-LEVEL: checked event argument compatibility also holds for the
   actual layout types retained by compile_log_eval_all. *)
Theory logArgumentTyping
Ancestors
  vyperEventArgCompat
  logArgumentTypes logArgumentTypeEval eventLoweringStructure
  abiTypeShape vyperTypeSystem vyperTypeInvariants vyperTypeEnvExtension
  exprLowering stmtLowering compileEnv vyperAST list combin pair finite_map

Theorem checked_abi_encode_event_arg_compatible:
  !env cx st cenv fty ann ensure method_id target_ty args.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_expr env (TypeBuiltin ann (AbiEncode ensure method_id) target_ty args) /\
    event_arg_compatible fty ann ==>
    event_arg_compatible fty
      (lowered_value_type cenv (TypeBuiltin ann (AbiEncode ensure method_id) target_ty args))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr env _`
    (mp_tac o ONCE_REWRITE_RULE [well_typed_expr_def]) >> strip_tac >>
  drule_all checked_exprs_type_evaluations >> strip_tac >>
  drule_all abi_encode_event_arg_compatible >> simp[]
QED

Theorem checked_type_builtin_event_arg_compatible:
  !env cx st cenv fty ann tb target_ty args.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_expr env (TypeBuiltin ann tb target_ty args) /\
    event_arg_compatible fty ann ==>
    event_arg_compatible fty (lowered_value_type cenv (TypeBuiltin ann tb target_ty args))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `tb` >>
  FIRST [drule_all checked_abi_encode_event_arg_compatible >> simp[],
    simp[lowered_value_type_def, expr_type_def]]
QED

Theorem checked_expr_event_arg_compatible:
  !env cx st cenv fty e.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_expr env e /\ event_arg_compatible fty (expr_type e) ==>
    event_arg_compatible fty (lowered_value_type cenv e)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >> fs[expr_type_def]
  >~ [`Builtin _ b _`]
  >- (Cases_on `b` >>
      FIRST [irule concat_event_arg_compatible >> fs[Once well_typed_expr_def],
        simp[lowered_value_type_def, expr_type_def]]) >>
  FIRST [irule literal_event_arg_compatible >> fs[Once well_typed_expr_def],
    drule_all checked_type_builtin_event_arg_compatible >> simp[],
    simp[lowered_value_type_def, expr_type_def]]
QED

Theorem checked_exprs_event_arg_compatible:
  !args fields env cx st cenv.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_exprs env args /\ LIST_REL (\fty e. event_arg_compatible fty (expr_type e)) fields args ==>
    LIST_REL event_arg_compatible fields (MAP (lowered_value_type cenv) args)
Proof
  Induct_on `args` >- simp[] >> rpt gen_tac >>
  rename1 `well_typed_exprs env (e::rest)` >> Cases_on `fields` >- simp[] >>
  rename1 `LIST_REL _ (fty::fields) (e::rest)` >>
  simp_tac bool_ss [Once well_typed_expr_def, LIST_REL_def, MAP] >> strip_tac >>
  conj_tac >- (drule_all checked_expr_event_arg_compatible >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem checked_compile_log_eval_all_types:
  !env cx st cenv fields args cs.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    well_typed_exprs env args /\ LIST_REL (\fty e. event_arg_compatible fty (expr_type e)) fields args ==>
    LIST_REL event_arg_compatible fields (MAP SND (FST (compile_log_eval_all cenv args cs)))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [compile_log_eval_all_types] >>
  drule_all checked_exprs_event_arg_compatible >> simp[]
QED

Theorem event_fields_expr_compatibility:
  !args fields.
    LIST_REL (\e ((_,fty),_). event_arg_compatible fty (expr_type e)) args fields <=>
    LIST_REL (\fty e. event_arg_compatible fty (expr_type e)) (MAP (SND o FST) fields) args
Proof
  Induct_on `args` >- (Cases_on `fields` >> simp[]) >> gen_tac >>
  Cases_on `fields` >- simp[] >> rename1 `LIST_REL _ (_::_) (event_field::_)` >>
  PairCases_on `event_field` >> simp[]
QED

Theorem checked_log_compiler_argument_types:
  !env cx st cenv ret event_id args env' fields cs.
    env_consistent env cx st /\ abi_struct_env_rel env.type_defs cenv.ce_struct_fields /\
    type_stmt env ret (Log event_id args) = SOME env' /\
    FLOOKUP env.event_fields event_id = SOME fields ==>
    LIST_REL event_arg_compatible (MAP (SND o FST) fields)
      (MAP SND (FST (compile_log_eval_all cenv args cs)))
Proof
  rpt gen_tac >> strip_tac >> fs[type_log_inversion] >> gvs[] >>
  `LIST_REL (\fty e. event_arg_compatible fty (expr_type e)) (MAP (SND o FST) fields) args` by
    fs[GSYM event_fields_expr_compatibility] >>
  drule_all checked_compile_log_eval_all_types >> simp[]
QED

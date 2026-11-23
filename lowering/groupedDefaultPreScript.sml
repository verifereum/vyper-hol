(* Runtime defaults have no internal calls or ABI decoders. *)
Theory groupedDefaultPre
Ancestors
  bodyExprPreFacts exprSimHypsDefs supportedExprTraverse supportedProgram
  vyperTypeContract vyperTypeCallGraph whitelistCheckerConsts vyperABI list

val body_call_root = ``\e. expr_internal_call_root e \/ expr_abi_decode_target_root target e \/ expr_evm_run_root e``;

Theorem runtime_constant_no_call_root[local]:
  (!p e. p = ^body_call_root /\ runtime_constant_expr mods e ==>
     ~supported_expr_exists p e) /\
  (!p t. p = ^body_call_root /\ F ==> ~supported_target_exists p t) /\
  (!p es. p = ^body_call_root /\ EVERY (runtime_constant_expr mods) es ==>
     ~supported_exprs_exists p es) /\
  (!p opt. p = ^body_call_root /\ F ==> ~supported_opt_exists p opt) /\
  (!p fs. p = ^body_call_root /\ EVERY (runtime_constant_expr mods) (MAP SND fs) ==>
     ~supported_fields_exists p fs)
Proof
  ho_match_mp_tac supported_expr_exists_ind >>
  rw[runtime_constant_expr_def, supported_expr_exists_def, expr_internal_call_root_def,
     expr_abi_decode_target_root_def, expr_evm_run_root_def] >>
  fs[EVERY_MEM] >>
  TRY (rename1 `constant_type_builtin tb` >> Cases_on `tb` >>
       gvs[constant_type_builtin_def, expr_abi_decode_target_root_def]) >>
  metis_tac[constant_expr_runtime_constant]
QED

Theorem runtime_constant_expr_body_pre:
  runtime_constant_expr mods e /\ expr_sim_inv ce cx env es /\ well_typed_expr env e /\
  byte_widths_expr e /\ alloc_limits_expr ce e /\ call_evaluation_safe cx [] /\
  ~supported_expr_exists (const_name_root cx) e /\
  get_tenv cx = type_env (cx_tops cx) ==>
  expr_body_pre ce cx env e es
Proof
  strip_tac >>
  `!target. ~supported_expr_exists expr_internal_call_root e /\
    ~supported_expr_exists (expr_abi_decode_target_root target) e /\ ~expr_has_evm_run e` by
    (gen_tac >> qpat_assum `runtime_constant_expr mods e`
       (fn th => mp_tac (MATCH_MP (Q.SPECL [`^body_call_root`,`e`]
         (cj 1 runtime_constant_no_call_root)) (CONJ (REFL body_call_root) th))) >>
     simp_tac (srw_ss()) [supported_expr_exists_disj, expr_has_evm_run_def] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `int_calls_expr e = []` by
    (irule (cj 1 no_internal_call_int_calls) >> simp[]) >>
  simp[expr_body_pre_def]
QED

Theorem runtime_constant_expr_body_pre_mods:
  runtime_constant_expr mods e /\ expr_sim_inv_mods mods ce cx env es /\
  well_typed_expr env e /\ byte_widths_expr e /\ alloc_limits_expr ce e /\
  call_evaluation_safe cx [] /\
  ~supported_expr_exists (const_name_root_mods mods) e /\
  ~supported_expr_exists (unallocated_bare_global_root ce env) e /\
  get_tenv cx = type_env_all_modules mods ==>
  expr_body_pre_mods mods ce cx env e es
Proof
  strip_tac >>
  `!target. ~supported_expr_exists expr_internal_call_root e /\
    ~supported_expr_exists (expr_abi_decode_target_root target) e /\ ~expr_has_evm_run e` by
    (gen_tac >> qpat_assum `runtime_constant_expr mods e`
       (fn th => mp_tac (MATCH_MP (Q.SPECL [`^body_call_root`,`e`]
         (cj 1 runtime_constant_no_call_root)) (CONJ (REFL body_call_root) th))) >>
     simp_tac (srw_ss()) [supported_expr_exists_disj, expr_has_evm_run_def] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `int_calls_expr e = []` by
    (irule (cj 1 no_internal_call_int_calls) >> simp[]) >>
  simp[expr_body_pre_mods_def]
QED

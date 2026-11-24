Theory exprBodyPreProps
Ancestors
  bodyCallSupport exprSimHypsDefs bodyInvCodeProps vyperTypeInvariants

Theorem body_inv_expr_body_pre_mods:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
  expr_body_pre_mods [(NONE,tops)] cenv cx env e es
Proof
  strip_tac >> drule body_inv_main_code >> strip_tac >>
  fs[expr_body_pre_split_def]
QED

Theorem expr_body_pre_mods_well_typed:
  expr_body_pre_mods mods cenv cx env e es ==> well_typed_expr env e
Proof
  simp[expr_body_pre_mods_def]
QED

Theorem expr_body_pre_mods_inv:
  expr_body_pre_mods mods cenv cx env e es ==> expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_body_pre_mods_def]
QED

Theorem expr_sim_inv_mods_env:
  expr_sim_inv_mods mods cenv cx env es ==> env_consistent env cx es
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem expr_sim_inv_mods_return_type:
  expr_sim_inv_mods mods cenv cx env es /\ FLOOKUP env.fn_sigs fid = SOME sg ==>
  cenv.ce_func_return_type (nsid_to_string fid) = sg.ret_ty
Proof
  simp[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem expr_body_pre_mods_int_calls:
  expr_body_pre_mods mods cenv cx env e es ==>
  EVERY (source_body_call_supported cx) (int_calls_expr e)
Proof
  simp[expr_body_pre_mods_def]
QED

Theorem expr_body_pre_static_facts:
  expr_body_pre cenv cx env e es ==>
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  alloc_limits_expr cenv e /\ ~expr_has_evm_run e /\
  ~supported_expr_exists (const_name_root cx) e
Proof
  simp[expr_body_pre_split_def, expr_body_pre_mods_def,
       const_name_root_mods_singleton]
QED

Theorem expr_body_pre_env_type_defs:
  expr_body_pre cenv cx env e es ==> env.type_defs = get_tenv cx
Proof
  simp[expr_body_pre_split_def, expr_sim_inv_split_def, expr_sim_inv_mods_def,
       env_consistent_def, env_context_consistent_def]
QED

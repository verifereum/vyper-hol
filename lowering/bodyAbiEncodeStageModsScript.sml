(* Actual compiler cuts for the shared linked ABI argument staging. *)
Theory bodyAbiEncodeStageMods
Ancestors
  exprSimAbiEncodeRuntimeInputs gasShadowCompileHelpers gasShadowCompile
  gasShadowState gasShadowCompileBase gasShadow abiBuiltinEncodeCode
  abiBuiltinEncodeSource abiBuiltinEncodeMethod allocLimits
  exprBodyPreProps exprSimHypsDefs vyperTypeSystem
  exprLowering compileEnv fragExec vyperAST list option pair

Theorem abi_encode_paired_argument_cuts_mods:
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) target args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) cty
    (gas_shadow_expr (TypeBuiltin ann (AbiEncode ensure mid) target args)) shadow_sa =
      (vv,shadow_sb) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  gas_shadow_state sa shadow_sa ==>
  ?svs st shadow_st out.
    compile_abi_encode_args compile_expr ce args sa = (svs,st) /\
    compile_abi_encode_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr args) shadow_sa = (svs,shadow_st) /\
    lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
      (abi_size_bound ce.ce_struct_fields
        (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
         else TupleT (MAP (lowered_value_type ce) args)))
      (compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure)
        svs (MAP (lowered_value_type ce) args)) st = (out,sb) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\ LENGTH svs = LENGTH args /\
    fn_has_code sa st func /\ fn_has_code st sb func /\
    fn_has_code shadow_sa shadow_st shadow_func /\
    fn_has_code shadow_st shadow_sb shadow_func /\
    gas_shadow_state st shadow_st
Proof
  strip_tac >> drule_all compile_abi_encode_body_layout >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[Once gas_shadow_expr_def, NoAsms] >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ shadow_sa = _`) compile_abi_encode_body_layout >>
  disch_then drule >> strip_tac >>
  `gas_shadow_compiles (compile_abi_encode_args compile_expr ce args)
     (compile_abi_encode_args compile_expr (gas_shadow_env T ce)
       (MAP gas_shadow_expr args))` by
    (irule (SIMP_RULE bool_ss []
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_abi_encode_args_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem abi_encode_stage_static_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es ==>
  1 <= LENGTH args /\
  abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word mid) =
    abi_encode_method_id_bytes mid /\
  32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
       else TupleT (MAP (lowered_value_type ce) args)) +
     (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64
Proof
  strip_tac >> conj_tac
  >- (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
      strip_tac >> Cases_on `args` >> gvs[well_typed_type_builtin_args_def]) >>
  conj_tac
  >- (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
      strip_tac >> drule abi_builtin_encode_checked_prefix >> simp[]) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
  drule alloc_limits_abi_encode_output >> simp[]
QED

Theory bodyPtrBytestringBuiltinsActualUnit
Ancestors
  bodyPtrBytestringBuiltinsUnitProbe compileVyper

(* Concrete stage fixture: naming the evaluated environment keeps subsequent
   compilation equations small without recomputing source-program packaging. *)
Definition order_actual_base_env_def:
  order_actual_base_env =
  <| ce_target := K T; ce_vars := FEMPTY |+ ("arr", MemLoc 0 96);
     ce_module_vars := FEMPTY; ce_storage_layout := FEMPTY;
     ce_module := NONE; ce_struct_fields := FEMPTY;
     ce_dynarray_capacity := (\s. if s = "arr" then 2 else 0);
     ce_module_dynarray_capacity := K 0;
     ce_method_id := (\s tys. w2n (calldata_method_id
       (function_selector s (vyper_to_abi_types FEMPTY tys))));
     ce_flag_member_id := K (K 0); ce_flag_n_members := K 0;
     ce_var_type := (\n. if "arr" = n then
       SOME (ArrayT (BaseT AddressT) (Dynamic 2)) else NONE);
     ce_module_var_type := K NONE; ce_hashmap_info := K NONE;
     ce_event_info := K NONE; ce_type_env := FEMPTY;
     ce_returns_count := 0; ce_return_buf := NONE; ce_return_pc := NONE;
     ce_ctor_exit_label := NONE; ce_is_external := T;
     ce_ret_enc_info := AbiPrimWord; ce_ret_dec_info := DecPrimWord NoClamp;
     ce_max_return_size := 0; ce_is_ctor := F; ce_imm_alloca := NONE;
     ce_func_info := K (0,0,[]); ce_func_param_types := K [];
     ce_func_return_type := K NoneT; ce_func_ids := K 0;
     ce_nonreentrant := (F,0,F,F); ce_raw_return := F;
     ce_alloca_locals := T |>
End

Theorem order_actual_base_env:
  build_compile_env order_unit_tops External Nonpayable "probe"
    [("arr", ArrayT (BaseT AddressT) (Dynamic 2))]
    (BaseT (BytesT (Dynamic 1)))
    [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)] F =
  order_actual_base_env
Proof
  rewrite_tac[order_actual_base_env_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

(* The return-ABI fields are the only packaging changes for this function. *)
Definition order_actual_env_def:
  order_actual_env = order_actual_base_env with <|
    ce_ret_enc_info := AbiComplex [(AbiBytestring 1,32,64,T)];
    ce_ret_dec_info := DecBytestring 1; ce_max_return_size := 96 |>
End

Theorem order_actual_package:
  set_external_package_target order_frame_policy.rpol_target
    (package_external_fn order_unit_tops F (assign_nkeys order_unit_tops 0)
      (Nonpayable, F, F, "probe",
       [("arr", ArrayT (BaseT AddressT) (Dynamic 2))], [],
       BaseT (BytesT (Dynamic 1)),
       [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)])) =
  ("fn_probe", order_actual_env,
   [("arr", F,T,32,DecDynArray (DecPrimWord (IntClamp 160 F)) 32 32 F 2)],
   36,F,F,0,F,F,
   [Return (SOME bodyPtrBytestringBuiltinsOrderProbe$order_probe_expr)],
   SOME (BaseT (BytesT (Dynamic 1))))
Proof
  rewrite_tac[package_external_fn_def, order_actual_base_env,
              order_actual_env_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

Theorem order_actual_unit_exists:
  ?u. lower_vyper_runtime_unit order_unit_tops order_frame_policy = SOME u
Proof
  rewrite_tac[order_unit_guard_free, order_unit_selectors_boundary,
              order_unit_classification, order_unit_fallback_boundary] >>
  pure_rewrite_tac[listTheory.MAP, combinTheory.o_THM, order_actual_package] >>
  rewrite_tac[vyperCompilerTheory.run_lowering_def, order_unit_policy_guard] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

(* THE names the actual computed unit, not a substituted function body. *)
Definition order_actual_unit_def:
  order_actual_unit = THE (lower_vyper_runtime_unit order_unit_tops order_frame_policy)
End

Theorem order_actual_lowering:
  lower_vyper_runtime_unit order_unit_tops order_frame_policy = SOME order_actual_unit
Proof
  mp_tac order_actual_unit_exists >> strip_tac >>
  simp[order_actual_unit_def]
QED

Theorem order_actual_function_names:
  MAP (\fn. fn.fn_name) order_actual_unit.cu_context.ctx_functions =
    ["__entry"]
Proof
  rewrite_tac[order_actual_unit_def, order_unit_guard_free,
              order_unit_selectors_boundary, order_unit_classification,
              order_unit_fallback_boundary] >>
  pure_rewrite_tac[listTheory.MAP, combinTheory.o_THM, order_actual_package] >>
  rewrite_tac[vyperCompilerTheory.run_lowering_def, order_unit_policy_guard] >>
  CONV_TAC (LAND_CONV (computeLib.RESTR_EVAL_CONV [``function_selector``])) >>
  simp[wordsTheory.dimword_def]
QED


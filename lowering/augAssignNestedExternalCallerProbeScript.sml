(* External visibility permits the saved-place index call in the source caller. *)
Theory augAssignNestedExternalCallerProbe
Ancestors
  augAssignNestedCallerProbe compileVyper vyperCompiler bodySim
Libs finite_mapLib computeLib supportedEvalLib cv_transLib

val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])

Definition nested_external_tops_def:
  nested_external_tops = nested_reach_tops ++
    [FunctionDecl External Nonpayable F F "probe" [] [] NoneT
      [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE]]
End

Definition nested_external_cx_def:
  nested_external_cx = nested_valid_cx with sources := [(0w,[(NONE,nested_external_tops)])]
End

Definition nested_external_env_def:
  nested_external_env = nested_caller_env
End

Definition nested_external_unit_def:
  nested_external_unit = THE
    (lower_vyper_runtime_unit nested_external_tops nested_premise_policy)
End

Theorem nested_external_supported:
  supported_program nested_external_tops
Proof
  EVAL_TAC
QED

Theorem nested_external_classify:
  classify_functions nested_external_tops =
    ([(Nonpayable,F,F,"probe",[],[],NoneT,
       [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
         (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE])],
     [(Nonpayable,F,F,"f",[],[],BaseT (UintT 256),nested_reach_body)],
     NONE,NONE)
Proof
  EVAL_TAC
QED

Theorem nested_external_allocs:
  EVERY (fn_allocs_ok nested_external_tops)
    (FST (classify_functions nested_external_tops) ++
     FST (SND (classify_functions nested_external_tops)))
Proof
  rewrite_tac[nested_external_classify] >> EVAL_TAC
QED

Theorem nested_external_immutables:
  compute_immutables_len
    (get_struct_fields (make_struct_fields_map nested_external_tops))
    nested_external_tops = 0
Proof
  EVAL_TAC
QED

Theorem nested_external_compile_env:
  build_compile_env nested_external_tops External Nonpayable "probe" [] NoneT
    [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE] F =
  <|ce_target := K T; ce_vars := FEMPTY;
    ce_module_vars := FEMPTY |+ ((NONE,"a"),StorageLoc 0w);
    ce_storage_layout := FEMPTY |+ ("a",0w); ce_module := NONE;
    ce_struct_fields := FEMPTY; ce_dynarray_capacity := K 0;
    ce_module_dynarray_capacity := (\s. if s = (NONE,"a") then 1 else 0);
    ce_method_id := (\s tys. w2n (calldata_method_id
      (function_selector s (vyper_to_abi_types FEMPTY tys))));
    ce_flag_member_id := K (K 0); ce_flag_n_members := K 0;
    ce_var_type := (\n. NONE);
    ce_module_var_type := (\n. if n = (NONE,"a") then SOME nested_reach_outer_ty else NONE);
    ce_hashmap_info := K NONE; ce_event_info := K NONE; ce_type_env := FEMPTY;
    ce_returns_count := 0; ce_return_buf := NONE; ce_return_pc := NONE;
    ce_ctor_exit_label := NONE; ce_is_external := T;
    ce_ret_enc_info := AbiPrimWord; ce_ret_dec_info := DecPrimWord NoClamp;
    ce_max_return_size := 0; ce_is_ctor := F; ce_imm_alloca := NONE;
    ce_func_info := (\s. if s = "f" then (1,0,[]) else (0,0,[]));
    ce_func_param_types := (\s. []);
    ce_func_return_type := (\s. if s = "f" then BaseT (UintT 256) else NoneT);
    ce_func_mutability := (\s. Nonpayable); ce_func_ids := (\s. 0);
    ce_nonreentrant := (F,0,F,F); ce_raw_return := F; ce_alloca_locals := T|>
Proof
  CONV_TAC (RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``]) >> simp[]
QED

Theorem nested_external_nkeys:
  assign_nkeys nested_external_tops 0 = K 0
Proof
  EVAL_TAC >> simp[]
QED

Theorem nested_external_package:
  package_external_fn nested_external_tops F (assign_nkeys nested_external_tops 0)
    (Nonpayable,F,F,"probe",[],[],NoneT,
      [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE]) =
  ("fn_probe",
    build_compile_env nested_external_tops External Nonpayable "probe" [] NoneT
      [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE] F,
    [],4,F,F,0,F,F,
    [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE],NONE)
Proof
  simp[package_external_fn_def, nested_external_nkeys,
       nested_external_compile_env, update_cenv_nonreentrant_def,
       build_positional_args_def, min_calldata_size_def]
QED

Theorem nested_external_selectors:
  build_selectors (type_env nested_external_tops)
    (FST (classify_functions nested_external_tops)) =
    [compute_selector FEMPTY "probe" []]
Proof
  `type_env nested_external_tops = FEMPTY` by EVAL_TAC >>
  simp[nested_external_classify, build_selectors_def]
QED

Theorem nested_external_return_guard:
  EVERY external_return_buffer_ok
    (MAP (set_external_package_target nested_premise_policy.rpol_target o
      package_external_fn nested_external_tops F (assign_nkeys nested_external_tops 0))
      (FST (classify_functions nested_external_tops)))
Proof
  simp[nested_external_classify, nested_external_package,
       set_external_package_target_def, external_return_buffer_ok_def]
QED

Theorem nested_external_selector_bytes:
  function_selector "probe" [] = [183w;74w;245w;169w]
Proof
  CONV_TAC (LAND_CONV supportedEvalLib.function_selector_conv) >> REFL_TAC
QED

Theorem nested_external_selector:
  compute_selector FEMPTY "probe" [] = (3075143081,"fn_probe",F)
Proof
  simp[compute_selector_def, nested_external_selector_bytes] >>
  EVAL_TAC
QED

Theorem nested_external_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit nested_external_tops nested_premise_policy)
Proof
  simp[lower_vyper_runtime_unit_def, nested_external_classify,
       nested_external_immutables, nested_external_package,
       build_selectors_def, nested_external_compile_env] >>
  CONV_TAC (RESTR_EVAL_CONV [``function_selector``]) >> simp[]
QED

Theorem nested_external_entry_registered:
  ?func. lookup_function "__entry" nested_external_unit.cu_context.ctx_functions = SOME func /\
    MEM "fn_probe" (MAP (\bb. bb.bb_label) func.fn_blocks)
Proof
  rewrite_tac[nested_external_unit_def, lower_vyper_runtime_unit_def,
    nested_external_classify, nested_external_immutables,
    nested_external_package, nested_external_compile_env] >>
  CONV_TAC (RESTR_EVAL_CONV [``function_selector``]) >> simp[]
QED

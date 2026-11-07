(* The gas-shadow compile env: the internal functions' default arguments
   shadowed like every other source expression. The expression lowering
   reads the defaults only when an internal call omits arguments, so every
   other part of it compiles the same under either env. *)
Theory gasShadowCenv
Ancestors
  gasShadow gasShadowCompileBase exprCallBounds exprLowering context
  compileEnv vyperAST list pair alist rich_list

Definition gas_shadow_cenv_def:
  gas_shadow_cenv cenv =
    cenv with ce_func_defaults :=
      MAP (I ## MAP gas_shadow_expr) cenv.ce_func_defaults
End

local
  val fields =
    TypeBase.fields_of ``:compile_env``
    |> map fst |> filter (fn n => n <> "ce_func_defaults")
  fun field_thm n =
    prove(Parse.Term [QUOTE ("!c. (gas_shadow_cenv c)." ^ n ^ " = c." ^ n)],
          simp[gas_shadow_cenv_def])
  fun update_thm n =
    prove(Parse.Term [QUOTE ("!c f. (gas_shadow_cenv c with " ^ n ^
            " updated_by f) = gas_shadow_cenv (c with " ^ n ^ " updated_by f)")],
          simp[gas_shadow_cenv_def])
in
  val gas_shadow_cenv_fields = LIST_CONJ (map field_thm fields)
  val gas_shadow_cenv_updates = LIST_CONJ (map update_thm fields)
end

Theorem gas_shadow_cenv_fields[simp] = gas_shadow_cenv_fields

(* Updates of other fields commute with the shadowing. *)
Theorem gas_shadow_cenv_updates[simp] = gas_shadow_cenv_updates

(* One-step induction over targets (HOL#2115), as vyperTypeEvalSoundness. *)
Theorem base_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

(* ===== The defaults ===== *)

Theorem gas_shadow_cenv_defaults_size[simp]:
  cenv_defaults_size (gas_shadow_cenv cenv) = cenv_defaults_size cenv
Proof
  simp[cenv_defaults_size_def, gas_shadow_cenv_def] >>
  simp[combinTheory.o_DEF]
QED

Theorem gas_shadow_cenv_omitted_defaults:
  omitted_defaults (gas_shadow_cenv cenv) name n =
  MAP gas_shadow_expr (omitted_defaults cenv name n)
Proof
  simp[omitted_defaults_def, gas_shadow_cenv_def] >>
  `ALOOKUP (MAP (I ## MAP gas_shadow_expr) cenv.ce_func_defaults) name =
   OPTION_MAP (MAP gas_shadow_expr) (ALOOKUP cenv.ce_func_defaults name)`
    by (Q.SPEC_TAC (`cenv.ce_func_defaults`, `l`) >> Induct >>
        simp[pairTheory.FORALL_PROD] >> rw[]) >>
  Cases_on `ALOOKUP cenv.ce_func_defaults name` >> simp[MAP_DROP]
QED

Theorem gas_shadow_cenv_without_defaults:
  cenv_without_defaults (gas_shadow_cenv cenv) name =
  gas_shadow_cenv (cenv_without_defaults cenv name)
Proof
  simp[cenv_without_defaults_def, gas_shadow_cenv_def,
       compile_env_component_equality] >>
  Q.SPEC_TAC (`cenv.ce_func_defaults`, `l`) >> Induct >>
  simp[pairTheory.FORALL_PROD] >> rw[]
QED

(* ===== Helpers that never read the defaults ===== *)

Theorem type_memory_bytes_gsc[simp]:
  !c. type_memory_bytes (gas_shadow_cenv c) = type_memory_bytes c
Proof
  rw[FUN_EQ_THM] >> irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem elem_size_in_location_gsc[simp]:
  !c. elem_size_in_location (gas_shadow_cenv c) = elem_size_in_location c
Proof
  simp[FUN_EQ_THM, elem_size_in_location_def]
QED

Theorem punnable_gsc[simp]:
  (!c. punnable (gas_shadow_cenv c) = punnable c) /\
  (!c. punnable_list (gas_shadow_cenv c) = punnable_list c)
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac punnable_ind >> rpt strip_tac >>
  once_rewrite_tac[punnable_def] >> simp[]
QED

Theorem compile_store_memory_typed_gsc[simp]:
  (!c. compile_store_memory_typed (gas_shadow_cenv c) =
       compile_store_memory_typed c) /\
  (!c. compile_typed_copy_fields (gas_shadow_cenv c) =
       compile_typed_copy_fields c) /\
  (!c. compile_copy_sarray_typed (gas_shadow_cenv c) =
       compile_copy_sarray_typed c) /\
  (!c. compile_copy_dynarray_typed (gas_shadow_cenv c) =
       compile_copy_dynarray_typed c) /\
  (!c. compile_struct_typed_copy (gas_shadow_cenv c) =
       compile_struct_typed_copy c)
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> once_rewrite_tac[compile_store_memory_typed_def] >>
  rw[] >> BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Theorem compile_store_memory_gsc[simp]:
  !c. compile_store_memory (gas_shadow_cenv c) = compile_store_memory c
Proof
  simp[FUN_EQ_THM, compile_store_memory_def]
QED

Theorem lowered_value_type_gsc[simp]:
  !c. lowered_value_type (gas_shadow_cenv c) = lowered_value_type c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac lowered_value_type_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[lowered_value_type_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem place_type_gsc[simp]:
  !c. place_type (gas_shadow_cenv c) = place_type c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac place_type_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[place_type_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem infer_array_location_gsc[simp]:
  !c. infer_array_location (gas_shadow_cenv c) = infer_array_location c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac infer_array_location_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[infer_array_location_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem unwrap_value_gsc[simp]:
  !c. unwrap_value (gas_shadow_cenv c) = unwrap_value c
Proof
  simp[FUN_EQ_THM] >> gen_tac >> Cases >> simp[unwrap_value_def]
QED

Theorem type_to_abi_enc_info_gsc[simp]:
  !sf c. type_to_abi_enc_info sf (gas_shadow_cenv c) = type_to_abi_enc_info sf c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac type_to_abi_enc_info_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[type_to_abi_enc_info_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  rw[listTheory.GENLIST_FUN_EQ, listTheory.MAP_EQ_f, pairTheory.FORALL_PROD] >>
  metis_tac[]
QED

Theorem type_to_abi_dec_info_gsc[simp]:
  !sf c. type_to_abi_dec_info sf (gas_shadow_cenv c) = type_to_abi_dec_info sf c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac type_to_abi_dec_info_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[type_to_abi_dec_info_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  rw[listTheory.GENLIST_FUN_EQ, listTheory.MAP_EQ_f, pairTheory.FORALL_PROD] >>
  metis_tac[]
QED

Theorem call_can_mutate_gsc[simp]:
  !c. call_can_mutate (gas_shadow_cenv c) = call_can_mutate c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac call_can_mutate_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[call_can_mutate_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem expr_can_mutate_gsc[simp]:
  (!c e. expr_can_mutate (gas_shadow_cenv c) e = expr_can_mutate c e) /\
  (!c es. exprs_can_mutate (gas_shadow_cenv c) es = exprs_can_mutate c es) /\
  (!c opt. opt_expr_can_mutate (gas_shadow_cenv c) opt =
           opt_expr_can_mutate c opt) /\
  (!c kes. named_exprs_can_mutate (gas_shadow_cenv c) kes =
           named_exprs_can_mutate c kes)
Proof
  ho_match_mp_tac expr_can_mutate_ind >> rw[expr_can_mutate_def]
QED

Theorem compile_extcall_store_values_gsc[simp]:
  !c. compile_extcall_store_values (gas_shadow_cenv c) =
      compile_extcall_store_values c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_extcall_store_values_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[compile_extcall_store_values_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_store_abi_tuple_gsc[simp]:
  !c. compile_store_abi_tuple (gas_shadow_cenv c) = compile_store_abi_tuple c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_store_abi_tuple_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[compile_store_abi_tuple_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_stage_intcall_args_gsc[simp]:
  !c. compile_stage_intcall_args (gas_shadow_cenv c) =
      compile_stage_intcall_args c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_stage_intcall_args_ind >>
  rpt strip_tac >> fs[GSYM FUN_EQ_THM, SF ETA_ss] >> once_rewrite_tac[compile_stage_intcall_args_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_invert_gsc[simp]:
  !v ty c. compile_invert v ty (gas_shadow_cenv c) = compile_invert v ty c
Proof
  ho_match_mp_tac compile_invert_ind >> rw[compile_invert_def]
QED

Theorem compile_target_base_gsc[simp]:
  !c. compile_target_base (gas_shadow_cenv c) = compile_target_base c
Proof
  simp[FUN_EQ_THM] >> gen_tac >> ho_match_mp_tac base_target_induct >>
  simp[compile_target_base_def]
QED

Theorem same_memory_layout_gsc[simp]:
  !c. same_memory_layout (gas_shadow_cenv c) = same_memory_layout c
Proof
  simp[FUN_EQ_THM, same_memory_layout_def]
QED

Theorem plain_helpers_gsc[simp]:
  (!c. compile_materialize_vv (gas_shadow_cenv c) = compile_materialize_vv c) /\
  (!c. compile_ifexp_arm (gas_shadow_cenv c) = compile_ifexp_arm c) /\
  (!c. compile_name_vv (gas_shadow_cenv c) = compile_name_vv c) /\
  (!c. compile_var_array_membership (gas_shadow_cenv c) =
       compile_var_array_membership c) /\
  (!c. compile_default_return_path (gas_shadow_cenv c) =
       compile_default_return_path c) /\
  (!c. compile_external_call_kwargs (gas_shadow_cenv c) =
       compile_external_call_kwargs c) /\
  (!c. compile_dynarray_append (gas_shadow_cenv c) = compile_dynarray_append c) /\
  (!c. compile_create_snapshot (gas_shadow_cenv c) = compile_create_snapshot c) /\
  (!c. compile_addmod_names (gas_shadow_cenv c) = compile_addmod_names c) /\
  (!c. compile_mulmod_names (gas_shadow_cenv c) = compile_mulmod_names c) /\
  (!c. compile_powmod256_names (gas_shadow_cenv c) = compile_powmod256_names c)
Proof
  simp[FUN_EQ_THM, compile_materialize_vv_def, compile_ifexp_arm_def,
       compile_name_vv_def, compile_var_array_membership_def,
       compile_default_return_path_def, compile_external_call_kwargs_def,
       compile_dynarray_append_def, compile_create_snapshot_def,
       compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def]
QED

(* ===== Helpers that pass the env to the expression compiler ===== *)

Theorem lower_value_gsc[simp]:
  (!cfn c. lower_value cfn (gas_shadow_cenv c) =
           lower_value (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. lower_value_with_loc cfn (gas_shadow_cenv c) =
           lower_value_with_loc (\c'. cfn (gas_shadow_cenv c')) c)
Proof
  simp[FUN_EQ_THM, lower_value_def, lower_value_with_loc_def]
QED

Theorem compile_multi_vvs_gsc[simp]:
  !cfn c. compile_multi_vvs cfn (gas_shadow_cenv c) =
          compile_multi_vvs (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Induct >> rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> simp[compile_multi_vvs_def]
QED

Theorem compile_multi_exprs_gsc[simp]:
  !cfn c. compile_multi_exprs cfn (gas_shadow_cenv c) =
          compile_multi_exprs (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Induct >> rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> simp[compile_multi_exprs_def]
QED

Theorem compile_abi_encode_args_gsc[simp]:
  !cfn c. compile_abi_encode_args cfn (gas_shadow_cenv c) =
          compile_abi_encode_args (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Induct >> rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >>
  simp[compile_abi_encode_args_def]
QED

Theorem compile_make_tuple_gsc[simp]:
  !cfn c. compile_make_tuple cfn (gas_shadow_cenv c) =
          compile_make_tuple (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Induct >> rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> simp[compile_make_tuple_def]
QED

Theorem compile_make_array_gsc[simp]:
  (!cfn c. compile_make_array_elems cfn (gas_shadow_cenv c) =
           compile_make_array_elems (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_make_array cfn (gas_shadow_cenv c) =
           compile_make_array (\c'. cfn (gas_shadow_cenv c')) c)
Proof
  conj_asm1_tac
  >- (simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Induct >> rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >>
      simp[compile_make_array_elems_def]) >>
  simp[FUN_EQ_THM, compile_make_array_def]
QED

Theorem compile_concat_gsc[simp]:
  !cfn c. compile_concat cfn (gas_shadow_cenv c) =
          compile_concat (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_concat_ind >>
  rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> once_rewrite_tac[compile_concat_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_struct_lit_gsc[simp]:
  !cfn c. compile_struct_lit cfn (gas_shadow_cenv c) =
          compile_struct_lit (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 3 gen_tac >> Induct >> rpt strip_tac >>
  fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> TRY (Cases_on `h`) >>
  simp[compile_struct_lit_def]
QED

Theorem compile_extcall_store_args_gsc[simp]:
  !cfn c. compile_extcall_store_args cfn (gas_shadow_cenv c) =
          compile_extcall_store_args (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_extcall_store_args_ind >>
  rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> once_rewrite_tac[compile_extcall_store_args_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_ext_call_kwarg_gsc[simp]:
  !cfn c. compile_ext_call_kwarg cfn (gas_shadow_cenv c) =
          compile_ext_call_kwarg (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM, compile_ext_call_kwarg_def]
QED

Theorem compile_ext_call_kwargs_gsc[simp]:
  !cfn c. compile_ext_call_kwargs cfn (gas_shadow_cenv c) =
          compile_ext_call_kwargs (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ho_match_mp_tac compile_ext_call_kwargs_ind >>
  rpt strip_tac >> fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> once_rewrite_tac[compile_ext_call_kwargs_def] >> simp[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem compile_get_target_ptr_gsc[simp]:
  !cfn c. compile_get_target_ptr cfn (gas_shadow_cenv c) =
          compile_get_target_ptr (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 2 gen_tac >> ho_match_mp_tac base_target_induct >>
  simp[compile_get_target_ptr_def] >> rpt strip_tac >>
  fs[Once (GSYM FUN_EQ_THM), SF ETA_ss] >> simp[]
QED

Theorem compile_subscript_attribute_gsc[simp]:
  (!cfn c. compile_subscript cfn (gas_shadow_cenv c) =
           compile_subscript (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_attribute cfn (gas_shadow_cenv c) =
           compile_attribute (\c'. cfn (gas_shadow_cenv c')) c)
Proof
  simp[FUN_EQ_THM, compile_subscript_def, compile_attribute_def]
QED

Theorem compile_create_gsc[simp]:
  (!cfn c. compile_create_salt cfn (gas_shadow_cenv c) =
           compile_create_salt (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_create_ctor_tuple cfn (gas_shadow_cenv c) =
           compile_create_ctor_tuple (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_create_blueprint_args cfn (gas_shadow_cenv c) =
           compile_create_blueprint_args (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_raw_create cfn (gas_shadow_cenv c) =
           compile_raw_create (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!cfn c. compile_create_call cfn (gas_shadow_cenv c) =
           compile_create_call (\c'. cfn (gas_shadow_cenv c')) c)
Proof
  conj_asm1_tac
  >- (simp[FUN_EQ_THM] >> ntac 2 gen_tac >> Cases >>
      simp[compile_create_salt_def]) >>
  conj_asm1_tac >- simp[FUN_EQ_THM, compile_create_ctor_tuple_def] >>
  conj_asm1_tac >- simp[FUN_EQ_THM, compile_create_blueprint_args_def] >>
  conj_asm1_tac >- simp[FUN_EQ_THM, compile_raw_create_def] >>
  simp[FUN_EQ_THM, compile_create_call_def]
QED

Theorem compile_acc_gsc[simp]:
  !cfn c. compile_acc cfn (gas_shadow_cenv c) =
          compile_acc (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM] >> ntac 3 gen_tac >> Cases >> simp[compile_acc_def]
QED

(* Every call but an internal one compiles its arguments in the caller's
   env alone. *)
Theorem compile_call_gsc:
  !cfn c ret_ty ty target args dr st.
    (!fid. target <> IntCall fid) ==>
    compile_call cfn (gas_shadow_cenv c) ret_ty ty target args dr st =
    compile_call (\c'. cfn (gas_shadow_cenv c')) c ret_ty ty target args dr st
Proof
  ho_match_mp_tac compile_call_ind >> rpt strip_tac >> gvs[] >>
  once_rewrite_tac[compile_call_def] >> simp[]
QED

(* ===== The compiler bodies ===== *)

Theorem compile_type_builtin_dispatch_body_gsc:
  !cfn c. compile_type_builtin_dispatch_body cfn (gas_shadow_cenv c) =
          compile_type_builtin_dispatch_body (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM, compile_type_builtin_dispatch_body_def]
QED

Theorem compile_builtin_dispatch_body_gsc:
  !cfn c. compile_builtin_dispatch_body cfn (gas_shadow_cenv c) =
          compile_builtin_dispatch_body (\c'. cfn (gas_shadow_cenv c')) c
Proof
  simp[FUN_EQ_THM, compile_builtin_dispatch_body_def]
QED

Theorem compile_expr_body_gsc:
  !f bf tf c ty e.
    (!a fid args dr. e <> Call a (IntCall fid) args dr) ==>
    compile_expr_body f bf tf (gas_shadow_cenv c) ty e =
    compile_expr_body (\c'. f (gas_shadow_cenv c'))
      (\c'. bf (gas_shadow_cenv c')) (\c'. tf (gas_shadow_cenv c')) c ty e
Proof
  rpt gen_tac >> Cases_on `e` >> simp[FUN_EQ_THM, compile_expr_body_def] >>
  rpt strip_tac >> simp[compile_call_gsc]
QED

(* ===== The guarded child callbacks ===== *)

Theorem child_callbacks_gsc[simp]:
  (!b cfn c. expr_child_callback b cfn (gas_shadow_cenv c) =
             expr_child_callback b (\c'. cfn (gas_shadow_cenv c')) c) /\
  (!b d c. builtin_child_callback b d (gas_shadow_cenv c) =
           builtin_child_callback b (\c'. d (gas_shadow_cenv c')) c) /\
  (!b d c. type_child_callback b d (gas_shadow_cenv c) =
           type_child_callback b (\c'. d (gas_shadow_cenv c')) c)
Proof
  simp[FUN_EQ_THM]
QED

Theorem gas_shadow_expr_intcall:
  gas_shadow_expr e = Call a (IntCall fid) args dr <=>
  ?args0 dr0. e = Call a (IntCall fid) args0 dr0 /\
              args = MAP gas_shadow_expr args0 /\
              dr = OPTION_MAP gas_shadow_expr dr0
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def] >> metis_tac[]
QED

(* The callback-shift lemmas rewrite the shadowed env into the callback;
   only the expression-level simulation wants that, so they are not
   exported as simp rules. *)
Theorem gsc_shift_thms = LIST_CONJ [lower_value_gsc, compile_multi_vvs_gsc, compile_multi_exprs_gsc, compile_abi_encode_args_gsc, compile_make_tuple_gsc, compile_make_array_gsc, compile_concat_gsc, compile_struct_lit_gsc, compile_extcall_store_args_gsc, compile_ext_call_kwarg_gsc, compile_ext_call_kwargs_gsc, compile_get_target_ptr_gsc, compile_subscript_attribute_gsc, compile_create_gsc, compile_acc_gsc, child_callbacks_gsc]

val _ = delsimps ["lower_value_gsc", "compile_multi_vvs_gsc", "compile_multi_exprs_gsc", "compile_abi_encode_args_gsc", "compile_make_tuple_gsc", "compile_make_array_gsc", "compile_concat_gsc", "compile_struct_lit_gsc", "compile_extcall_store_args_gsc", "compile_ext_call_kwarg_gsc", "compile_ext_call_kwargs_gsc", "compile_get_target_ptr_gsc", "compile_subscript_attribute_gsc", "compile_create_gsc", "compile_acc_gsc", "child_callbacks_gsc"]

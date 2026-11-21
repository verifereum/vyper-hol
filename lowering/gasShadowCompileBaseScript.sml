(* Relational interfaces for structurally guarded compiler callbacks. *)
Theory gasShadowCompileBase
Ancestors
  gasShadow gasShadowState exprCallBounds exprLowering context compileEnv emitHelper
  vyperAST list pair

(* The shadow compiler run's environment: with sd, the internal functions'
   default arguments are shadowed too, so an omitted default's msg.gas
   compiles to GASPRICE as an explicit one does. *)
Definition gas_shadow_env_def:
  gas_shadow_env sd cenv =
    if sd then
      cenv with ce_func_defaults :=
        MAP (I ## MAP gas_shadow_expr) cenv.ce_func_defaults
    else cenv
End

Theorem gas_shadow_env_F[simp]:
  gas_shadow_env F cenv = cenv
Proof
  simp[gas_shadow_env_def]
QED

Theorem gas_shadow_env_fields[simp]:
  (gas_shadow_env sd cenv).ce_target = cenv.ce_target /\
  (gas_shadow_env sd cenv).ce_vars = cenv.ce_vars /\
  (gas_shadow_env sd cenv).ce_module_vars = cenv.ce_module_vars /\
  (gas_shadow_env sd cenv).ce_storage_layout = cenv.ce_storage_layout /\
  (gas_shadow_env sd cenv).ce_module = cenv.ce_module /\
  (gas_shadow_env sd cenv).ce_struct_fields = cenv.ce_struct_fields /\
  (gas_shadow_env sd cenv).ce_dynarray_capacity = cenv.ce_dynarray_capacity /\
  (gas_shadow_env sd cenv).ce_module_dynarray_capacity = cenv.ce_module_dynarray_capacity /\
  (gas_shadow_env sd cenv).ce_method_id = cenv.ce_method_id /\
  (gas_shadow_env sd cenv).ce_flag_member_id = cenv.ce_flag_member_id /\
  (gas_shadow_env sd cenv).ce_flag_n_members = cenv.ce_flag_n_members /\
  (gas_shadow_env sd cenv).ce_var_type = cenv.ce_var_type /\
  (gas_shadow_env sd cenv).ce_module_var_type = cenv.ce_module_var_type /\
  (gas_shadow_env sd cenv).ce_hashmap_info = cenv.ce_hashmap_info /\
  (gas_shadow_env sd cenv).ce_event_info = cenv.ce_event_info /\
  (gas_shadow_env sd cenv).ce_error_info = cenv.ce_error_info /\
  (gas_shadow_env sd cenv).ce_type_env = cenv.ce_type_env /\
  (gas_shadow_env sd cenv).ce_returns_count = cenv.ce_returns_count /\
  (gas_shadow_env sd cenv).ce_return_buf = cenv.ce_return_buf /\
  (gas_shadow_env sd cenv).ce_return_pc = cenv.ce_return_pc /\
  (gas_shadow_env sd cenv).ce_ctor_exit_label = cenv.ce_ctor_exit_label /\
  (gas_shadow_env sd cenv).ce_is_external = cenv.ce_is_external /\
  (gas_shadow_env sd cenv).ce_ret_enc_info = cenv.ce_ret_enc_info /\
  (gas_shadow_env sd cenv).ce_ret_dec_info = cenv.ce_ret_dec_info /\
  (gas_shadow_env sd cenv).ce_max_return_size = cenv.ce_max_return_size /\
  (gas_shadow_env sd cenv).ce_is_ctor = cenv.ce_is_ctor /\
  (gas_shadow_env sd cenv).ce_imm_alloca = cenv.ce_imm_alloca /\
  (gas_shadow_env sd cenv).ce_func_info = cenv.ce_func_info /\
  (gas_shadow_env sd cenv).ce_func_param_types = cenv.ce_func_param_types /\
  (gas_shadow_env sd cenv).ce_func_return_type = cenv.ce_func_return_type /\
  (gas_shadow_env sd cenv).ce_func_mutability = cenv.ce_func_mutability /\
  (gas_shadow_env sd cenv).ce_func_ids = cenv.ce_func_ids /\
  (gas_shadow_env sd cenv).ce_modules = cenv.ce_modules /\
  (gas_shadow_env sd cenv).ce_nonreentrant = cenv.ce_nonreentrant /\
  (gas_shadow_env sd cenv).ce_raw_return = cenv.ce_raw_return /\
  (gas_shadow_env sd cenv).ce_alloca_locals = cenv.ce_alloca_locals
Proof
  rw[FUN_EQ_THM, gas_shadow_env_def]
QED

Theorem gas_shadow_env_defaults:
  (gas_shadow_env sd cenv).ce_func_defaults =
    if sd then MAP (I ## MAP gas_shadow_expr) cenv.ce_func_defaults
    else cenv.ce_func_defaults
Proof
  rw[FUN_EQ_THM, gas_shadow_env_def]
QED

Theorem gas_shadow_env_defaults_size[simp]:
  cenv_defaults_size (gas_shadow_env sd cenv) = cenv_defaults_size cenv
Proof
  rw[cenv_defaults_size_def, gas_shadow_env_def] >>
  qspec_tac (`cenv.ce_func_defaults`, `l`) >>
  Induct >> simp[list_size_def, FORALL_PROD] >>
  rw[] >> Induct_on `p_2` >> simp[list_size_def, gas_shadow_expr_size]
QED

(* The lowering's helpers read no default arguments, so they compile alike
   under the shadow environment. *)
Theorem cenv_sft_gas_shadow_env[simp]:
  !cenv. cenv_sft (gas_shadow_env sd cenv) = cenv_sft cenv
Proof
  rw[FUN_EQ_THM, cenv_sft_def]
QED

Theorem type_memory_bytes_gas_shadow_env[simp]:
  !cenv.
    type_memory_bytes (gas_shadow_env sd cenv) = type_memory_bytes cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac type_memory_bytes_ind >> rpt strip_tac >>
  once_rewrite_tac[type_memory_bytes_def] >> gs[Cong MAP_CONG]
QED

Theorem elem_size_in_location_gas_shadow_env[simp]:
  !cenv. elem_size_in_location (gas_shadow_env sd cenv) = elem_size_in_location cenv
Proof
  rw[FUN_EQ_THM, elem_size_in_location_def]
QED

Theorem compile_store_memory_typed_gas_shadow_env[simp]:
  (!cenv dst dst_ty src src_ty.
     compile_store_memory_typed (gas_shadow_env sd cenv) dst dst_ty src src_ty = compile_store_memory_typed cenv dst dst_ty src src_ty) /\
  (!cenv dst src dst_tys src_tys i j.
     compile_typed_copy_fields (gas_shadow_env sd cenv) dst src dst_tys src_tys i j = compile_typed_copy_fields cenv dst src dst_tys src_tys i j) /\
  (!cenv dst dst_elem src src_elem n.
     compile_copy_sarray_typed (gas_shadow_env sd cenv) dst dst_elem src src_elem n = compile_copy_sarray_typed cenv dst dst_elem src src_elem n) /\
  (!cenv dst dst_elem dst_cap src src_elem.
     compile_copy_dynarray_typed (gas_shadow_env sd cenv) dst dst_elem dst_cap src src_elem = compile_copy_dynarray_typed cenv dst dst_elem dst_cap src src_elem) /\
  (!cenv dst src dst_fields src_fields i j.
     compile_struct_typed_copy (gas_shadow_env sd cenv) dst src dst_fields src_fields i j = compile_struct_typed_copy cenv dst src dst_fields src_fields i j)
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_memory_typed_def] >> gs[Cong MAP_CONG] >>
  rw[] >> rpt CASE_TAC >> gs[]
QED

Theorem compile_store_memory_gas_shadow_env[simp]:
  !cenv. compile_store_memory (gas_shadow_env sd cenv) = compile_store_memory cenv
Proof
  rw[FUN_EQ_THM, compile_store_memory_def]
QED

Theorem punnable_gas_shadow_env[simp]:
  (!cenv.
     punnable (gas_shadow_env sd cenv) = punnable cenv) /\
  (!cenv.
     punnable_list (gas_shadow_env sd cenv) = punnable_list cenv)
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac punnable_ind >> rpt strip_tac >>
  once_rewrite_tac[punnable_def] >> gs[Cong MAP_CONG]
QED

Theorem same_memory_layout_gas_shadow_env[simp]:
  !cenv. same_memory_layout (gas_shadow_env sd cenv) = same_memory_layout cenv
Proof
  rw[FUN_EQ_THM, same_memory_layout_def]
QED

Theorem compile_store_slots_gas_shadow_env[simp]:
  (!cenv src slot ty transient.
     compile_store_slots (gas_shadow_env sd cenv) src slot ty transient = compile_store_slots cenv src slot ty transient) /\
  (!cenv src slot members mem_off slot_off transient.
     compile_store_slots_members (gas_shadow_env sd cenv) src slot members mem_off slot_off transient = compile_store_slots_members cenv src slot members mem_off slot_off transient) /\
  (!cenv src_data slot_data elem len transient.
     compile_copy_elements_to_slots (gas_shadow_env sd cenv) src_data slot_data elem len transient = compile_copy_elements_to_slots cenv src_data slot_data elem len transient)
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_slots_def] >> gs[Cong MAP_CONG] >>
  rw[] >> rpt CASE_TAC >> gs[]
QED

Theorem place_type_gas_shadow_env[simp]:
  !cenv.
    place_type (gas_shadow_env sd cenv) = place_type cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac place_type_ind >> rpt strip_tac >>
  once_rewrite_tac[place_type_def] >> gs[Cong MAP_CONG]
QED

Theorem lowered_value_type_gas_shadow_env[simp]:
  !cenv.
    lowered_value_type (gas_shadow_env sd cenv) = lowered_value_type cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac lowered_value_type_ind >> rpt strip_tac >>
  once_rewrite_tac[lowered_value_type_def] >> gs[Cong MAP_CONG]
QED

Theorem infer_array_location_gas_shadow_env[simp]:
  !cenv.
    infer_array_location (gas_shadow_env sd cenv) = infer_array_location cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac infer_array_location_ind >> rpt strip_tac >>
  once_rewrite_tac[infer_array_location_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_var_array_membership_gas_shadow_env[simp]:
  !cenv. compile_var_array_membership (gas_shadow_env sd cenv) = compile_var_array_membership cenv
Proof
  rw[FUN_EQ_THM, compile_var_array_membership_def]
QED

Theorem compile_default_return_path_gas_shadow_env[simp]:
  !cenv. compile_default_return_path (gas_shadow_env sd cenv) = compile_default_return_path cenv
Proof
  rw[FUN_EQ_THM, compile_default_return_path_def]
QED

Theorem unwrap_value_gas_shadow_env[simp]:
  !cenv vv.
    unwrap_value (gas_shadow_env sd cenv) vv = unwrap_value cenv vv
Proof
  rpt gen_tac >> Cases_on `vv` >> rw[unwrap_value_def]
QED

Theorem compile_extcall_store_values_gas_shadow_env[simp]:
  !cenv vals buf_op offset.
    compile_extcall_store_values (gas_shadow_env sd cenv) vals buf_op offset = compile_extcall_store_values cenv vals buf_op offset
Proof
  ho_match_mp_tac compile_extcall_store_values_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_extcall_store_values_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_dynarray_append_gas_shadow_env[simp]:
  !cenv. compile_dynarray_append (gas_shadow_env sd cenv) = compile_dynarray_append cenv
Proof
  rw[FUN_EQ_THM, compile_dynarray_append_def]
QED

Theorem type_to_abi_enc_info_gas_shadow_env[simp]:
  !sfields cenv.
    type_to_abi_enc_info sfields (gas_shadow_env sd cenv) = type_to_abi_enc_info sfields cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac type_to_abi_enc_info_ind >> rpt strip_tac >>
  once_rewrite_tac[type_to_abi_enc_info_def] >> gs[Cong MAP_CONG] >> rw[] >~ [`GENLIST`]
  >- (Cases_on `n` >> gs[] >> first_x_assum (qspec_then `0` mp_tac) >> gs[]) >>
  CASE_TAC >> gs[] >> irule MAP_CONG >> simp[FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem compile_abi_encode_value_rows_gas_shadow_env[simp]:
  !cenv dst cursor static_ofst rows.
    compile_abi_encode_value_rows (gas_shadow_env sd cenv) dst cursor static_ofst rows = compile_abi_encode_value_rows cenv dst cursor static_ofst rows
Proof
  ho_match_mp_tac compile_abi_encode_value_rows_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_abi_encode_value_rows_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_abi_encode_values_to_buf_gas_shadow_env[simp]:
  !cenv. compile_abi_encode_values_to_buf (gas_shadow_env sd cenv) = compile_abi_encode_values_to_buf cenv
Proof
  rw[FUN_EQ_THM, compile_abi_encode_values_to_buf_def]
QED

Theorem compile_external_call_kwargs_gas_shadow_env[simp]:
  !cenv. compile_external_call_kwargs (gas_shadow_env sd cenv) = compile_external_call_kwargs cenv
Proof
  rw[FUN_EQ_THM, compile_external_call_kwargs_def]
QED

Theorem type_to_abi_dec_info_gas_shadow_env[simp]:
  !sfields cenv.
    type_to_abi_dec_info sfields (gas_shadow_env sd cenv) = type_to_abi_dec_info sfields cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac type_to_abi_dec_info_ind >> rpt strip_tac >>
  once_rewrite_tac[type_to_abi_dec_info_def] >> gs[Cong MAP_CONG] >> rw[] >~ [`GENLIST`]
  >- (Cases_on `n` >> gs[] >> first_x_assum (qspec_then `0` mp_tac) >> gs[]) >>
  CASE_TAC >> gs[] >> irule MAP_CONG >> simp[FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem compile_name_vv_gas_shadow_env[simp]:
  !cenv. compile_name_vv (gas_shadow_env sd cenv) = compile_name_vv cenv
Proof
  rw[FUN_EQ_THM, compile_name_vv_def]
QED

Theorem compile_store_abi_tuple_gas_shadow_env[simp]:
  !cenv buf off vals.
    compile_store_abi_tuple (gas_shadow_env sd cenv) buf off vals = compile_store_abi_tuple cenv buf off vals
Proof
  ho_match_mp_tac compile_store_abi_tuple_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_store_abi_tuple_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_materialize_vv_gas_shadow_env[simp]:
  !cenv. compile_materialize_vv (gas_shadow_env sd cenv) = compile_materialize_vv cenv
Proof
  rw[FUN_EQ_THM, compile_materialize_vv_def]
QED

Theorem compile_ifexp_arm_gas_shadow_env[simp]:
  !cenv. compile_ifexp_arm (gas_shadow_env sd cenv) = compile_ifexp_arm cenv
Proof
  rw[FUN_EQ_THM, compile_ifexp_arm_def]
QED

Theorem call_can_mutate_gas_shadow_env[simp]:
  !cenv.
    call_can_mutate (gas_shadow_env sd cenv) = call_can_mutate cenv
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac call_can_mutate_ind >> rpt strip_tac >>
  once_rewrite_tac[call_can_mutate_def] >> gs[Cong MAP_CONG]
QED

Theorem expr_can_mutate_gas_shadow_env[simp]:
  (!cenv.
     expr_can_mutate (gas_shadow_env sd cenv) = expr_can_mutate cenv) /\
  (!cenv.
     exprs_can_mutate (gas_shadow_env sd cenv) = exprs_can_mutate cenv) /\
  (!cenv.
     opt_expr_can_mutate (gas_shadow_env sd cenv) = opt_expr_can_mutate cenv) /\
  (!cenv.
     named_exprs_can_mutate (gas_shadow_env sd cenv) = named_exprs_can_mutate cenv)
Proof
  rewrite_tac[FUN_EQ_THM] >>
  ho_match_mp_tac expr_can_mutate_ind >> rpt strip_tac >>
  once_rewrite_tac[expr_can_mutate_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_snapshot_vv_gas_shadow_env[simp]:
  !cenv. compile_snapshot_vv (gas_shadow_env sd cenv) = compile_snapshot_vv cenv
Proof
  rw[FUN_EQ_THM, compile_snapshot_vv_def]
QED

Theorem copies_subscript_base_gas_shadow_env[simp]:
  !cenv. copies_subscript_base (gas_shadow_env sd cenv) = copies_subscript_base cenv
Proof
  rw[FUN_EQ_THM, copies_subscript_base_def]
QED

Theorem compile_abi_encode_payload_gas_shadow_env[simp]:
  !cenv. compile_abi_encode_payload (gas_shadow_env sd cenv) = compile_abi_encode_payload cenv
Proof
  rw[FUN_EQ_THM, compile_abi_encode_payload_def]
QED

Theorem compile_create_snapshot_gas_shadow_env[simp]:
  !cenv. compile_create_snapshot (gas_shadow_env sd cenv) = compile_create_snapshot cenv
Proof
  rw[FUN_EQ_THM, compile_create_snapshot_def]
QED

Theorem compile_invert_gas_shadow_env[simp]:
  !v ty cenv.
    compile_invert v ty (gas_shadow_env sd cenv) = compile_invert v ty cenv
Proof
  ho_match_mp_tac compile_invert_ind >> rpt strip_tac >>
  once_rewrite_tac[compile_invert_def] >> gs[Cong MAP_CONG]
QED

Theorem compile_addmod_names_gas_shadow_env[simp]:
  !cenv. compile_addmod_names (gas_shadow_env sd cenv) = compile_addmod_names cenv
Proof
  rw[FUN_EQ_THM, compile_addmod_names_def]
QED

Theorem compile_mulmod_names_gas_shadow_env[simp]:
  !cenv. compile_mulmod_names (gas_shadow_env sd cenv) = compile_mulmod_names cenv
Proof
  rw[FUN_EQ_THM, compile_mulmod_names_def]
QED

Theorem compile_powmod256_names_gas_shadow_env[simp]:
  !cenv. compile_powmod256_names (gas_shadow_env sd cenv) = compile_powmod256_names cenv
Proof
  rw[FUN_EQ_THM, compile_powmod256_names_def]
QED

Theorem gas_shadow_compiles_pair:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) ==>
  gas_shadow_compiles
    (\s. let (x,s1) = f s in h x s1)
    (\t. let (x,t1) = g t in k x t1)
Proof
  pure_rewrite_tac[GSYM comp_bind_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  MATCH_ACCEPT_TAC gas_shadow_compiles_bind
QED

Theorem gas_shadow_compiles_ignore_bind:
  gas_shadow_compiles f g /\ gas_shadow_compiles h k ==>
  gas_shadow_compiles (comp_ignore_bind f h) (comp_ignore_bind g k)
Proof
  simp[comp_ignore_bind_def, gas_shadow_compiles_bind]
QED

Theorem gas_shadow_compiles_map_result:
  gas_shadow_compiles f g ==>
  gas_shadow_compiles
    (\s. let (x,s1) = f s in (h x,s1))
    (\t. let (x,t1) = g t in (h x,t1))
Proof
  strip_tac >> ho_match_mp_tac gas_shadow_compiles_pair >>
  pure_rewrite_tac[GSYM comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_invalid_expr_call:
  gas_shadow_compiles (invalid_expr_call ty) (invalid_expr_call ty)
Proof
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  pure_rewrite_tac[invalid_expr_call_def] >>
  ho_match_mp_tac gas_shadow_compiles_map_result >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  MATCH_ACCEPT_TAC gas_shadow_compiles_emit_inst
QED

Theorem gas_shadow_args_size[simp]:
  list_size expr_size (MAP gas_shadow_expr args) = list_size expr_size args
Proof
  Induct_on `args` >> simp[list_size_def, gas_shadow_expr_size] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem gas_shadow_compiles_expr_child:
  (!cenv ty e shadow. expr_size e + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv ty e)
       (g (gas_shadow_env sd cenv) ty (if shadow then gas_shadow_expr e else e))) ==>
  !cenv ty e shadow.
    gas_shadow_compiles (expr_child_callback bound f cenv ty e)
      (expr_child_callback bound g (gas_shadow_env sd cenv) ty
        (if shadow then gas_shadow_expr e else e))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `expr_size e + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[expr_child_callback_def, gas_shadow_expr_size] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspec_then `cenv` mp_tac) >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

Theorem gas_shadow_compiles_builtin_child:
  (!cenv ret_ty ty bi args shadow. list_size expr_size args + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv ret_ty ty bi args)
       (g (gas_shadow_env sd cenv) ret_ty ty (if shadow then gas_shadow_builtin bi else bi)
         (if shadow then MAP gas_shadow_expr args else args))) ==>
  !cenv ret_ty ty bi args shadow.
    gas_shadow_compiles (builtin_child_callback bound f cenv ret_ty ty bi args)
      (builtin_child_callback bound g (gas_shadow_env sd cenv) ret_ty ty
        (if shadow then gas_shadow_builtin bi else bi)
        (if shadow then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `list_size expr_size args + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[builtin_child_callback_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspecl_then [`cenv`, `ret_ty`, `ty`, `bi`, `args`] mp_tac) >>
  simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

Theorem gas_shadow_compiles_type_child:
  (!cenv vv_ty ty tb ret_ty args shadow. list_size expr_size args + cenv_defaults_size cenv < bound ==>
     gas_shadow_compiles (f cenv vv_ty ty tb ret_ty args)
       (g (gas_shadow_env sd cenv) vv_ty ty tb ret_ty
         (if shadow then MAP gas_shadow_expr args else args))) ==>
  !cenv vv_ty ty tb ret_ty args shadow.
    gas_shadow_compiles (type_child_callback bound f cenv vv_ty ty tb ret_ty args)
      (type_child_callback bound g (gas_shadow_env sd cenv) vv_ty ty tb ret_ty
        (if shadow then MAP gas_shadow_expr args else args))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `shadow` >>
  Cases_on `list_size expr_size args + cenv_defaults_size cenv < bound` >>
  CONV_TAC (BINOP_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[type_child_callback_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[gas_shadow_compiles_invalid_expr_call] >>
  first_x_assum (qspec_then `cenv` mp_tac) >>
  disch_then (qspec_then `vv_ty` mp_tac) >>
  disch_then (qspec_then `ty` mp_tac) >>
  disch_then (qspec_then `tb` mp_tac) >>
  disch_then (qspec_then `ret_ty` mp_tac) >>
  disch_then (qspec_then `args` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (Q.SPEC `T` th) >> mp_tac (Q.SPEC `F` th)) >> simp[]
QED

(* Eta-insensitive state-threading boundary. *)
Theorem comp_bind_uncurry:
  (\s. UNCURRY h (f s)) = comp_bind f h
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
  Cases_on `f s` >> simp[]
QED

Theorem gas_shadow_compiles_uncurry:
  gas_shadow_compiles f g /\
  (!x. gas_shadow_compiles (h x) (k x)) ==>
  gas_shadow_compiles (\s. UNCURRY h (f s)) (\t. UNCURRY k (g t))
Proof
  simp[comp_bind_uncurry, gas_shadow_compiles_bind]
QED

Theory bodyIntCallPinActionsMods
Ancestors
  exprLowering compileEnv

Theorem lower_value_module_pin_cong:
  f (ce with ce_module := src) ty e = g ce ty e /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) ==>
  lower_value f (ce with ce_module := src) ty e = lower_value g ce ty e
Proof
  strip_tac >> simp[lower_value_def]
QED

Theorem compile_multi_exprs_module_pin_cong:
  (!e. MEM e es ==> f (ce with ce_module := src) (expr_type e) e =
                    g ce (expr_type e) e) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) ==>
  compile_multi_exprs f (ce with ce_module := src) es = compile_multi_exprs g ce es
Proof
  Induct_on `es` >> simp[compile_multi_exprs_def] >> rpt strip_tac >>
  fs[] >> simp[lower_value_def]
QED

Theorem compile_abi_encode_args_module_pin_cong:
  (!e. MEM e es ==> f (ce with ce_module := src) (expr_type e) e =
                    g ce (expr_type e) e) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) /\
  (!es'. exprs_can_mutate (ce with ce_module := src) es' = exprs_can_mutate ce es') /\
  (!m vv. compile_snapshot_vv (ce with ce_module := src) m vv =
          compile_snapshot_vv ce m vv) ==>
  compile_abi_encode_args f (ce with ce_module := src) es =
  compile_abi_encode_args g ce es
Proof
  simp[compile_abi_encode_args_def] >>
  Induct_on `es` >> simp[compile_ext_call_args_def] >> rpt strip_tac >> fs[]
QED

Theorem compile_stage_intcall_args_module_pin_cong:
  (!e. MEM e es ==> f (ce with ce_module := src) (expr_type e) e =
                    g ce (expr_type e) e) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!ty. type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty) /\
  (!v buf dst_ty src_ty.
      compile_store_memory (ce with ce_module := src) v buf dst_ty src_ty =
      compile_store_memory ce v buf dst_ty src_ty) ==>
  compile_stage_intcall_args f (ce with ce_module := src) es flags tys =
  compile_stage_intcall_args g ce es flags tys
Proof
  map_every qid_spec_tac [`tys`, `flags`] >>
  Induct_on `es` >- simp[compile_stage_intcall_args_def] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  Cases_on `flags` >- simp[compile_stage_intcall_args_def] >>
  Cases_on `tys` >- simp[compile_stage_intcall_args_def] >>
  rename1 `compile_stage_intcall_args f _ (_::_) (flag::_) (_::_) = _` >>
  Cases_on `flag` >> simp[compile_stage_intcall_args_def]
QED

(* Erasing a defaults-table entry does not also change the module selector. *)
Theorem pin_without_defaults[local]:
  cenv_without_defaults (ce with ce_module := src) name =
  (cenv_without_defaults ce name) with ce_module := src
Proof
  simp[cenv_without_defaults_def, compile_env_fupdcanon]
QED

Theorem compile_call_int_module_pin_cong:
  (!flags tys.
    compile_stage_intcall_args f (ce with ce_module := src) args flags tys =
    compile_stage_intcall_args g ce args flags tys) /\
  (!flags tys.
    compile_stage_intcall_args f
      ((cenv_without_defaults ce (nsid_to_string id)) with ce_module := src)
      (omitted_defaults ce (nsid_to_string id) (LENGTH args)) flags tys =
    compile_stage_intcall_args g (cenv_without_defaults ce (nsid_to_string id))
      (omitted_defaults ce (nsid_to_string id) (LENGTH args)) flags tys) ==>
  compile_call f (ce with ce_module := src) ret_ty ty (IntCall id) args default_ret st =
  compile_call g ce ret_ty ty (IntCall id) args default_ret st
Proof
  strip_tac >>
  `omitted_defaults (ce with ce_module := src) (nsid_to_string id) (LENGTH args) =
   omitted_defaults ce (nsid_to_string id) (LENGTH args)` by simp[omitted_defaults_def] >>
  simp[compile_call_def, pin_without_defaults]
QED

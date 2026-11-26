Theory bodyIntCallPinBodiesMods
Ancestors
  exprLowering compileEnv vyperAST list pair
  boolChainOpsCong exprLoweringEquations
Libs dep_rewrite

Theorem compile_concat_module_pin_cong:
  (!ty e. lower_value f (ce with ce_module := src) ty e =
          lower_value g ce ty e) ==>
  compile_concat f (ce with ce_module := src) es data infos off =
  compile_concat g ce es data infos off
Proof
  strip_tac >> qid_spec_tac `infos` >> Induct_on `es`
  >- simp[compile_concat_def] >>
  Cases_on `infos` >- simp[compile_concat_def] >>
  rename1 `compile_concat _ _ (_::_) _ (info::_) _ = _` >>
  PairCases_on `info` >> simp[compile_concat_def]
QED

Theorem compile_make_tuple_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!ty. type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!v dst m ty. compile_store_memory (ce with ce_module := src) v dst m ty =
                compile_store_memory ce v dst m ty) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) ==>
  compile_make_tuple f (ce with ce_module := src) es tys buf off =
  compile_make_tuple g ce es tys buf off
Proof
  strip_tac >> qid_spec_tac `off` >> qid_spec_tac `tys` >> Induct_on `es`
  >- simp[compile_make_tuple_def] >>
  Cases_on `tys` >> simp[compile_make_tuple_def]
QED

Triviality compile_make_array_elems_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!v dst m ty. compile_store_memory (ce with ce_module := src) v dst m ty =
                compile_store_memory ce v dst m ty) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) ==>
  compile_make_array_elems f (ce with ce_module := src) es ety sz lw buf idx =
  compile_make_array_elems g ce es ety sz lw buf idx
Proof
  strip_tac >> qid_spec_tac `idx` >> Induct_on `es` >>
  simp[compile_make_array_elems_def]
QED

Theorem compile_make_array_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!v dst m ty. compile_store_memory (ce with ce_module := src) v dst m ty =
                compile_store_memory ce v dst m ty) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) ==>
  compile_make_array f (ce with ce_module := src) es ety sz lw buf =
  compile_make_array g ce es ety sz lw buf
Proof
  strip_tac >>
  `compile_make_array_elems f (ce with ce_module := src) es ety sz lw buf 0 =
   compile_make_array_elems g ce es ety sz lw buf 0` by
    (irule compile_make_array_elems_module_pin_cong >> simp[]) >>
  simp[compile_make_array_def]
QED

Theorem compile_bool_chain_ops_module_pin_cong:
  (!e. lower_value f (ce with ce_module := src) (BaseT BoolT) e =
       lower_value g ce (BaseT BoolT) e) ==>
  compile_bool_chain_ops f (ce with ce_module := src) d r exit_lbl es =
  compile_bool_chain_ops g ce d r exit_lbl es
Proof
  strip_tac >> irule compile_bool_chain_ops_lower_value_cong >> simp[]
QED

Theorem compile_builtin_dispatch_body_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!ty e. lower_value f (ce with ce_module := src) ty e = lower_value g ce ty e) /\
  (!ty. type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!v dst m ty. compile_store_memory (ce with ce_module := src) v dst m ty =
                compile_store_memory ce v dst m ty) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) /\
  (!v ty. compile_invert v ty (ce with ce_module := src) = compile_invert v ty ce) /\
  (!e item. compile_acc f (ce with ce_module := src) e item = compile_acc g ce e item) /\
  (!es. compile_multi_exprs f (ce with ce_module := src) es = compile_multi_exprs g ce es) /\
  (!v vv ty d. compile_var_array_membership (ce with ce_module := src) v vv ty d =
               compile_var_array_membership ce v vv ty d) ==>
  compile_builtin_dispatch_body f (ce with ce_module := src) ret ty bi args st =
  compile_builtin_dispatch_body g ce ret ty bi args st
Proof
  strip_tac >>
  `type_memory_bytes (ce with ce_module := src) = type_memory_bytes ce` by simp[FUN_EQ_THM] >>
  Cases_on `bi` >>
  FIRST [
    rename1 `compile_builtin_dispatch_body _ _ _ _ (NamedConst) _ _ = _` >>
      simp[compile_builtin_dispatch_body_def],
    rename1 `compile_builtin_dispatch_body _ _ _ _ (BoolChain _ _) _ _ = _` >>
      `!d r lbl es. compile_bool_chain_ops f (ce with ce_module := src) d r lbl es =
                     compile_bool_chain_ops g ce d r lbl es` by
        (rpt gen_tac >> irule compile_bool_chain_ops_module_pin_cong >> simp[]) >>
      simp[compile_builtin_dispatch_body_def],
    rename1 `compile_builtin_dispatch_body _ _ _ _ (Concat _) _ _ = _` >>
      `!dp infos off. compile_concat f (ce with ce_module := src) args dp infos off =
                       compile_concat g ce args dp infos off` by
        (rpt gen_tac >> irule compile_concat_module_pin_cong >> simp[]) >>
      simp[compile_builtin_dispatch_body_def],
    rename1 `compile_builtin_dispatch_body _ _ _ _ (MakeArray _ _) _ _ = _` >>
      `!tys buf off. compile_make_tuple f (ce with ce_module := src) args tys buf off =
                      compile_make_tuple g ce args tys buf off` by
        (rpt gen_tac >> irule compile_make_tuple_module_pin_cong >> simp[]) >>
      `!ety sz lw buf. compile_make_array f (ce with ce_module := src) args ety sz lw buf =
                        compile_make_array g ce args ety sz lw buf` by
        (rpt gen_tac >> irule compile_make_array_module_pin_cong >> simp[]) >>
      simp[compile_builtin_dispatch_body_def],
    simp[compile_builtin_dispatch_body_def]]
QED

Theorem compile_type_builtin_dispatch_body_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!ty e. lower_value f (ce with ce_module := src) ty e = lower_value g ce ty e) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!ty. type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty) /\
  (lowered_value_type (ce with ce_module := src) = lowered_value_type ce) /\
  (!es. compile_abi_encode_args f (ce with ce_module := src) es = compile_abi_encode_args g ce es) /\
  (!single vs tys. compile_abi_encode_payload (ce with ce_module := src) single vs tys =
                   compile_abi_encode_payload ce single vs tys) /\
  (!ty. type_to_abi_dec_info ce.ce_struct_fields (ce with ce_module := src) ty =
        type_to_abi_dec_info ce.ce_struct_fields ce ty) ==>
  compile_type_builtin_dispatch_body f (ce with ce_module := src) vv_ty ty tb ret_ty args st =
  compile_type_builtin_dispatch_body g ce vv_ty ty tb ret_ty args st
Proof
  strip_tac >> Cases_on `tb` >> simp[compile_type_builtin_dispatch_body_def]
QED

Triviality compile_expr_body_builtin_pin:
  (!ret ty bi es. b (ce with ce_module := src) ret ty bi es = b' ce ret ty bi es) /\
  (!ty id. compile_name_vv (ce with ce_module := src) ty id = compile_name_vv ce ty id) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) ==>
  compile_expr_body f b t (ce with ce_module := src) ty (Builtin ann bi es) st =
  compile_expr_body g b' t' ce ty (Builtin ann bi es) st
Proof
  strip_tac >>
  Cases_on `?at a bt b mt m. bi = AddMod /\ es = [Name at a; Name bt b; Name mt m]`
  >- gvs[compile_expr_body_def, expr_type_def, compile_addmod_names_def] >>
  Cases_on `?at a bt b mt m. bi = MulMod /\ es = [Name at a; Name bt b; Name mt m]`
  >- gvs[compile_expr_body_def, expr_type_def, compile_mulmod_names_def] >>
  Cases_on `?at a bt b. bi = PowMod256 /\ es = [Name at a; Name bt b]`
  >- gvs[compile_expr_body_def, expr_type_def, compile_powmod256_names_def] >>
  dep_rewrite.DEP_REWRITE_TAC [compile_expr_body_builtin_default] >> fs[]
QED

Theorem compile_expr_body_module_pin_cong:
  (!ty e. f (ce with ce_module := src) ty e = g ce ty e) /\
  (!ty e. lower_value f (ce with ce_module := src) ty e = lower_value g ce ty e) /\
  (!ret ty bi es. b (ce with ce_module := src) ret ty bi es = b' ce ret ty bi es) /\
  (!ann ty tb ret es. t (ce with ce_module := src) ann ty tb ret es = t' ce ann ty tb ret es) /\
  (!ty id. compile_name_vv (ce with ce_module := src) ty id = compile_name_vv ce ty id) /\
  (!vv. unwrap_value (ce with ce_module := src) vv = unwrap_value ce vv) /\
  (!e. lowered_value_type (ce with ce_module := src) e = lowered_value_type ce e) /\
  (!ret ty vv. compile_ifexp_arm (ce with ce_module := src) ret ty vv =
                compile_ifexp_arm ce ret ty vv) /\
  (!ret ty e idx. compile_subscript f (ce with ce_module := src) ret ty e idx =
                   compile_subscript g ce ret ty e idx) /\
  (!ret ty e fld. compile_attribute f (ce with ce_module := src) ret ty e fld =
                   compile_attribute g ce ret ty e fld) /\
  (!ty fields buf off. compile_struct_lit f (ce with ce_module := src) ty fields buf off =
                        compile_struct_lit g ce ty fields buf off) /\
  (!ret ty target args dflt st.
     compile_call f (ce with ce_module := src) ret (ty:type) target args (dflt:expr option) st =
     compile_call g ce ret ty target args dflt st) /\
  (!target. compile_get_target_ptr f (ce with ce_module := src) target =
            compile_get_target_ptr g ce target) /\
  (!loc ty. elem_size_in_location (ce with ce_module := src) loc ty =
             elem_size_in_location ce loc ty) ==>
  compile_expr_body f b t (ce with ce_module := src) ty e st =
  compile_expr_body g b' t' ce ty e st
Proof
  strip_tac >> Cases_on `e` >>
  FIRST [
    rename1 `compile_expr_body _ _ _ _ _ (Builtin _ _ _) _ = _` >>
      irule compile_expr_body_builtin_pin >> simp[],
    simp[compile_expr_body_def]]
QED

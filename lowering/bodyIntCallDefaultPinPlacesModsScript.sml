(* Module-pin transport for the reached place actions.  Only the callbacks
   occurring in the reached expression are compared. *)
Theory bodyIntCallDefaultPinPlacesMods
Ancestors
  bodyIntCallPinSupportMods bodyIntCallPinActionsMods
  exprLowering exprCallBounds compileEnv
  vyperTypeContract supportedExprTraverse list pair

val bad_builtin_arity_pin = ``\e. case e of
    Builtin _ bt args => ~builtin_args_length_ok bt (LENGTH args)
  | TypeBuiltin _ bt _ args => ~type_builtin_args_length_ok bt (LENGTH args)
  | _ => F``;

Theorem elem_size_module_pin_local[local]:
  !ce src loc et. elem_size_in_location (ce with ce_module := src) loc et =
    elem_size_in_location ce loc et
Proof
  simp[elem_size_in_location_def,
       bodyIntCallPinSupportModsTheory.type_memory_bytes_module_pin]
QED

Theorem runtime_default_subscript_body_module_pin:
  !mods ce src f bd td ty type_ann e1 e2 st.
    runtime_constant_expr mods (Subscript type_ann e1 e2) /\
    ~supported_expr_exists ^bad_builtin_arity_pin
      (Subscript type_ann e1 e2) /\
    (!e cty cs. expr_size e < expr_size (Subscript type_ann e1 e2) /\
      runtime_constant_expr mods e /\
      ~supported_expr_exists ^bad_builtin_arity_pin e ==>
      f (ce with ce_module := src) cty e cs = f ce cty e cs) ==>
    compile_expr_body f bd td (ce with ce_module := src) ty
      (Subscript type_ann e1 e2) st =
    compile_expr_body f bd td ce ty (Subscript type_ann e1 e2) st
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_constant_expr mods e1 /\ runtime_constant_expr mods e2` by
    (fs[runtime_constant_expr_def]) >>
  `~supported_expr_exists ^bad_builtin_arity_pin e1 /\
   ~supported_expr_exists ^bad_builtin_arity_pin e2` by
    (fs[supported_expr_exists_def]) >>
  `!cty. f (ce with ce_module := src) cty e1 = f ce cty e1` by
    (rpt gen_tac >> simp[FUN_EQ_THM] >> first_x_assum irule >>
     simp[vyperASTTheory.expr_size_def]) >>
  `!cty. f (ce with ce_module := src) cty e2 = f ce cty e2` by
    (rpt gen_tac >> simp[FUN_EQ_THM] >> first_x_assum irule >>
     simp[vyperASTTheory.expr_size_def]) >>
  `!vv. compile_snapshot_vv (ce with ce_module := src) T vv =
    compile_snapshot_vv ce T vv` by
    (simp[compile_snapshot_vv_def, compile_materialize_vv_def,
         unwrap_value_module_pin, compile_store_memory_module_pin,
         type_memory_bytes_module_pin]) >>
  `!loc. elem_size_in_location (ce with ce_module := src) loc =
         elem_size_in_location ce loc` by
    (simp[FUN_EQ_THM, elem_size_module_pin_local]) >>
  `!cty. lower_value f (ce with ce_module := src) cty e2 =
         lower_value f ce cty e2` by
    (gen_tac >>
     irule bodyIntCallPinActionsModsTheory.lower_value_module_pin_cong >>
     simp[unwrap_value_module_pin]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  rewrite_tac[compile_subscript_def, copies_subscript_base_def] >>
  qpat_assum `!cty. f _ cty e1 = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!vv. compile_snapshot_vv _ T vv = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!loc. elem_size_in_location _ loc = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!cty. lower_value f _ cty e2 = _` (fn th => rewrite_tac[th]) >>
  simp[place_type_module_pin, LET_THM]
QED

Theorem runtime_default_attribute_body_module_pin:
  !mods ce src f bd td ty type_ann e1 fld st.
    runtime_constant_expr mods (Attribute type_ann e1 fld) /\
    ~supported_expr_exists ^bad_builtin_arity_pin
      (Attribute type_ann e1 fld) /\
    (!e cty cs. expr_size e < expr_size (Attribute type_ann e1 fld) /\
      runtime_constant_expr mods e /\
      ~supported_expr_exists ^bad_builtin_arity_pin e ==>
      f (ce with ce_module := src) cty e cs = f ce cty e cs) ==>
    compile_expr_body f bd td (ce with ce_module := src) ty
      (Attribute type_ann e1 fld) st =
    compile_expr_body f bd td ce ty (Attribute type_ann e1 fld) st
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_constant_expr mods e1` by (fs[runtime_constant_expr_def]) >>
  `~supported_expr_exists ^bad_builtin_arity_pin e1` by
    (fs[supported_expr_exists_def]) >>
  `f (ce with ce_module := src) ty e1 = f ce ty e1` by
    (simp[FUN_EQ_THM] >> first_x_assum irule >> simp[vyperASTTheory.expr_size_def]) >>
  once_rewrite_tac[compile_expr_body_def] >>
  simp[compile_attribute_def, LET_THM]
QED

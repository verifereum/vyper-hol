Theory bodyIntCallPinCallsMods
Ancestors
  bodyIntCallCallsMods exprLowering compileEnv
Libs
  monadsyntax

(* Place actions and the public module-pin interface for non-internal calls. *)

Theorem pin_call_elem_size[local]:
  elem_size_in_location (ce with ce_module := src) loc =
  elem_size_in_location ce loc
Proof
  `!ty. type_memory_bytes (ce with ce_module := src) ty = type_memory_bytes ce ty` by
    (gen_tac >> irule type_memory_bytes_struct_fields >> simp[]) >>
  simp[FUN_EQ_THM, elem_size_in_location_def]
QED

Theorem compile_subscript_module_pin_cong:
  f (ce with ce_module := src) = g ce /\
  lower_value f (ce with ce_module := src) = lower_value g ce /\
  compile_snapshot_vv (ce with ce_module := src) = compile_snapshot_vv ce /\
  place_type (ce with ce_module := src) = place_type ce ==>
  compile_subscript f (ce with ce_module := src) rt ty base_e idx =
  compile_subscript g ce rt ty base_e idx
Proof
  strip_tac >>
  simp[compile_subscript_def, copies_subscript_base_def, pin_call_elem_size]
QED

Theorem compile_attribute_module_pin_cong:
  f (ce with ce_module := src) = g ce ==>
  compile_attribute f (ce with ce_module := src) rt ty base_e fld =
  compile_attribute g ce rt ty base_e fld
Proof
  strip_tac >> simp[compile_attribute_def]
QED

Theorem compile_get_target_ptr_module_pin_cong:
  lower_value f (ce with ce_module := src) = lower_value g ce ==>
  !t. compile_get_target_ptr f (ce with ce_module := src) t =
      compile_get_target_ptr g ce t
Proof
  strip_tac >> gen_tac >> measureInduct_on `base_assignment_target_size t` >>
  Cases_on `t` >> gs[vyperASTTheory.expr_size_def] >>
  simp[compile_get_target_ptr_def, pin_call_elem_size]
QED

Theorem pin_call_snapshot:
  ^(concl bodyIntCallCallsModsTheory.pin_call_snapshot)
Proof
  ACCEPT_TAC bodyIntCallCallsModsTheory.pin_call_snapshot
QED

Theorem compile_ext_call_kwargs_module_pin_cong:
  ^(concl bodyIntCallCallsModsTheory.compile_ext_call_kwargs_module_pin_cong)
Proof
  ACCEPT_TAC bodyIntCallCallsModsTheory.compile_ext_call_kwargs_module_pin_cong
QED

Theorem compile_call_ext_module_pin_cong:
  ^(concl bodyIntCallCallsModsTheory.compile_call_ext_module_pin_cong)
Proof
  ACCEPT_TAC bodyIntCallCallsModsTheory.compile_call_ext_module_pin_cong
QED

Theorem compile_call_other_module_pin_cong:
  ^(concl bodyIntCallCallsModsTheory.compile_call_other_module_pin_cong)
Proof
  ACCEPT_TAC bodyIntCallCallsModsTheory.compile_call_other_module_pin_cong
QED

Theorem compile_call_create_module_pin_cong:
  ^(concl bodyIntCallCallsModsTheory.compile_call_create_module_pin_cong)
Proof
  ACCEPT_TAC bodyIntCallCallsModsTheory.compile_call_create_module_pin_cong
QED

(* Operand-only hashing and membership correspondence. *)
Theory gasShadowCompileMembership
Ancestors
  gasShadowCompileArith gasShadowCompileContext gasShadowCompileBase
  gasShadowState exprLowering compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_bytestring_hash:
  gas_shadow_compiles (compile_bytestring_hash ptr_op) (compile_bytestring_hash ptr_op)
Proof
  simp[compile_bytestring_hash_def] >>
  rpt gen_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_emit_membership_eqs:
  !elems needle. gas_shadow_compiles (emit_membership_eqs needle elems)
    (emit_membership_eqs needle elems)
Proof
  Induct >> simp[emit_membership_eqs_def, gas_shadow_compiles_return] >>
  rpt gen_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_fold_membership_or:
  !cs acc. gas_shadow_compiles (fold_membership_or acc cs)
    (fold_membership_or acc cs)
Proof
  Induct >> simp[fold_membership_or_def, gas_shadow_compiles_return] >>
  rpt gen_tac >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[]
QED

Theorem gas_shadow_compiles_fold_membership_and:
  !cs acc. gas_shadow_compiles (fold_membership_and acc cs)
    (fold_membership_and acc cs)
Proof
  Induct >> simp[fold_membership_and_def, gas_shadow_compiles_return] >>
  rpt gen_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_list_membership_in:
  !elems needle. gas_shadow_compiles (compile_list_membership_in needle elems)
    (compile_list_membership_in needle elems)
Proof
  rpt gen_tac >> simp[compile_list_membership_in_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_membership_eqs] >>
  Cases >> simp[gas_shadow_compiles_return, gas_shadow_compiles_fold_membership_or]
QED

Theorem gas_shadow_compiles_list_membership_notin:
  !elems needle. gas_shadow_compiles (compile_list_membership_notin needle elems)
    (compile_list_membership_notin needle elems)
Proof
  rpt gen_tac >> simp[compile_list_membership_notin_def] >>
  match_mp_tac gas_shadow_compiles_bind >>
  simp[gas_shadow_compiles_emit_membership_eqs] >>
  Cases >> simp[gas_shadow_compiles_return] >>
  match_mp_tac gas_shadow_compiles_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[gas_shadow_compiles_fold_membership_and]
QED

Theorem gas_shadow_compiles_mapping_subscript:
  gas_shadow_compiles (compile_mapping_subscript base_slot key_op)
    (compile_mapping_subscript base_slot key_op)
Proof
  simp[compile_mapping_subscript_def, LET_THM, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_keccak256_key:
  gas_shadow_compiles (compile_keccak256_key key_op is_bytes32)
    (compile_keccak256_key key_op is_bytes32)
Proof
  Cases_on `is_bytes32` >>
  simp[compile_keccak256_key_def, LET_THM, comp_ignore_bind_def] >>
  rpt gen_tac >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_array_membership_loop:
  (!addr. gas_shadow_compiles (loader addr) (loader' addr)) ==>
  gas_shadow_compiles
    (compile_array_membership_loop needle arr_op len_op elem_size offset_base loader bound_opt is_in)
    (compile_array_membership_loop needle arr_op len_op elem_size offset_base loader' bound_opt is_in)
Proof
  strip_tac >> Cases_on `0 < offset_base` >> Cases_on `is_in` >> Cases_on `bound_opt` >>
  simp[compile_array_membership_loop_def, comp_ignore_bind_def] >>
  (* the bound check is a nested bind, so decompose binds on both sides *)
  rpt (FIRST [simp[gas_shadow_compiles_return, gas_shadow_compiles_fresh_var,
                   gas_shadow_compiles_fresh_label, gas_shadow_compiles_emit_inst,
                   gas_shadow_compiles_new_block, gas_shadow_compiles_emit_op] >> NO_TAC,
              match_mp_tac gas_shadow_compiles_bind >> rpt strip_tac >> TRY BETA_TAC])
QED

Theorem gas_shadow_compiles_array_subscript:
  (!addr. gas_shadow_compiles (loader addr) (loader' addr)) ==>
  gas_shadow_compiles
    (compile_array_subscript base_op idx_op dynamic static_count stride elem_size is_signed_idx loader)
    (compile_array_subscript base_op idx_op dynamic static_count stride elem_size is_signed_idx loader')
Proof
  strip_tac >> Cases_on `dynamic` >> Cases_on `is_signed_idx` >>
  simp[compile_array_subscript_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_return, gas_shadow_compiles_emit_void]
       >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_tuple_subscript:
  gas_shadow_compiles (compile_tuple_subscript base_op offset)
    (compile_tuple_subscript base_op offset)
Proof
  simp[compile_tuple_subscript_def]
QED

Theorem gas_shadow_compiles_var_array_membership:
  gas_shadow_compiles (compile_var_array_membership cenv needle arr_vv rhs_ty is_in)
    (compile_var_array_membership cenv needle arr_vv rhs_ty is_in)
Proof
  Cases_on `rhs_ty` >>
  simp[compile_var_array_membership_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_ptr_load, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_bind]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_array_membership_loop, gas_shadow_compiles_ptr_load] >>
  Cases_on `b` >> simp[comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_ptr_load, gas_shadow_compiles_return,
               gas_shadow_compiles_emit_inst, gas_shadow_compiles_bind]
       >> gen_tac >> BETA_TAC) >>
  simp[gas_shadow_compiles_array_membership_loop, gas_shadow_compiles_ptr_load]
QED

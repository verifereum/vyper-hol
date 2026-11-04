(* Opcode-independent bound-label preservation for body compilation. *)
Theory bodyBoundLabels
Ancestors
  helperBoundLabels boundLabelRules exprLowering emitHelper context compileEnv loweringShapeDefs

Theorem bound_labels_clamp:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_clamp v ty s))))
Proof
  strip_tac >> simp[compile_clamp_def] >> pairarg_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_clamp_and_return:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (clamp_and_return v ty s))))
Proof
  strip_tac >> simp[clamp_and_return_def] >>
  irule bound_labels_ignore_bind >> simp[bound_labels_clamp, comp_return_def]
QED

Theorem bound_labels_clamp_basetype:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_clamp_basetype v ty s))))
Proof
  strip_tac >> Cases_on `ty` >>
  simp[compile_clamp_basetype_def, comp_return_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[compile_clamp_basetype_def,
    bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return, comp_return_def]),
    (rename1 `BytesT sz` >> Cases_on `sz`), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_add:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_add x y ty s))))
Proof
  strip_tac >> simp[compile_safe_add_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_sub:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_sub x y ty s))))
Proof
  strip_tac >> simp[compile_safe_sub_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_mul_overflow_check:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_mul_overflow_check x y res signed bits s))))
Proof
  strip_tac >> simp[compile_mul_overflow_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_mul:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_mul x y ty s))))
Proof
  strip_tac >> simp[compile_safe_mul_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return, bound_labels_mul_overflow_check,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_div:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_div x y ty s))))
Proof
  strip_tac >> simp[compile_safe_div_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_decimal_div:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_decimal_div x y divisor ty s))))
Proof
  strip_tac >> simp[compile_safe_decimal_div_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp_and_return]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_safe_mod:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_mod x y ty s))))
Proof
  strip_tac >> simp[compile_safe_mod_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_safe_pow:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_safe_pow x y ty base_lit exp_lit s))))
Proof
  strip_tac >> Cases_on `base_lit` >> Cases_on `exp_lit` >>
  simp[compile_safe_pow_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_clamp, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_compare:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_compare op x y ty s))))
Proof
  strip_tac >> Cases_on `op` >> simp[compile_compare_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_wrap_truncate:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (wrap_truncate v ty s))))
Proof
  strip_tac >> simp[wrap_truncate_def] >>
  rpt IF_CASES_TAC >> simp[bound_labels_emit_op, comp_return_def]
QED

Theorem bound_labels_binop:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_binop op x y ty base_lit exp_lit s))))
Proof
  strip_tac >> Cases_on `op` >> simp[compile_binop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_safe_add, bound_labels_safe_sub, bound_labels_safe_mul,
    bound_labels_safe_div, bound_labels_safe_decimal_div, bound_labels_safe_mod,
    bound_labels_safe_pow, bound_labels_compare, bound_labels_wrap_truncate,
    bound_labels_select, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_bytestring_hash:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_bytestring_hash ptr_op s))))
Proof
  strip_tac >> simp[compile_bytestring_hash_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_list_membership_in:
  !xs s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_list_membership_in needle xs s))))
Proof
  Induct >> simp[compile_list_membership_in_def, comp_return_def] >>
  Cases_on `xs` >> simp[compile_list_membership_in_def, bound_labels_emit_op] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_list_membership_notin:
  !xs s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_list_membership_notin needle xs s))))
Proof
  Induct >> simp[compile_list_membership_notin_def, comp_return_def] >>
  Cases_on `xs` >> simp[compile_list_membership_notin_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_array_membership_loop:
  (!l. compiler_label l ==> P l) /\
  (!op t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (loader op t))))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_array_membership_loop needle arr len sz off loader is_in s))))
Proof
  strip_tac >> simp[compile_array_membership_loop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block, cj 4 bound_labels_primitives, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_mapping_subscript:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_mapping_subscript slot key s))))
Proof
  strip_tac >> simp[compile_mapping_subscript_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_keccak256_key:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_keccak256_key key bytes32 s))))
Proof
  strip_tac >> simp[compile_keccak256_key_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_alloc_buffer]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_var_array_membership:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_var_array_membership ce needle vv ty is_in s))))
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_var_array_membership_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_array_membership_loop, bound_labels_ptr_load, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC, split_pair_case_tac]) >>
  Cases_on `b` >> gvs[] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_array_membership_loop, bound_labels_ptr_load, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_extcodesize_check:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_extcodesize_check addr s))))
Proof
  strip_tac >> simp[compile_extcodesize_check_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, bound_labels_emit_void]
QED

Theorem bound_labels_return_value_decode:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_return_value_decode buf lo hi s))))
Proof
  strip_tac >> simp[compile_return_value_decode_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_select]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_default_return_path:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_default_return_path ce ret_ty def_ty buf result_op def_op
      addr skip lo hi info s))))
Proof
  strip_tac >> simp[compile_default_return_path_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_inst,
    bound_labels_new_block, bound_labels_store_memory,
    bound_labels_extcodesize_check, bound_labels_return_value_decode,
    cj 1 bound_labels_abi_decode, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_fresh_label_bind, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_unwrap_value:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (unwrap_value ce vv s))))
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_ptr_load,
    bound_labels_ensure_in_memory, comp_return_def]), IF_CASES_TAC]) >>
  CASE_TAC >> simp[bound_labels_ensure_in_memory, comp_return_def]
QED

Theorem bound_labels_multi_vvs:
  (!ty e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) ==>
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_multi_vvs cfn ce es s))))
Proof
  Induct_on `es` >> simp[compile_multi_vvs_def, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >> irule bound_labels_bind >>
      simp[comp_return_def] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem bound_labels_extcall_store_values:
  !vs buf off s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_extcall_store_values ce vs buf off s))))
Proof
  Induct >> simp[compile_extcall_store_values_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_extcall_store_values_def] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_unwrap_value, bound_labels_store_bytestring]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_external_call_kwargs:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_external_call_kwargs ce addr arg_vals arg_types
      mem_sz abi_sz mid ret_sz lo ret_mem static val_op gas_op skip has_default
      def_op ret_ty def_ty enc_info dec_info s))))
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_alloc_buffer, bound_labels_new_block,
    bound_labels_extcall_store_values, cj 2 bound_labels_abi_encode,
    cj 1 bound_labels_abi_decode, bound_labels_extcodesize_check,
    bound_labels_default_return_path, bound_labels_return_value_decode,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_dynarray_append:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_dynarray_append ce base_op val_op ws sz dst_ty src_ty
      cap prim ld st s))))
Proof
  strip_tac >> simp[compile_dynarray_append_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_store_memory, bound_labels_word_copy_loop, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_dynarray_pop:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_dynarray_pop base_op ws sz ld st s))))
Proof
  strip_tac >> simp[compile_dynarray_pop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

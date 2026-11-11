(* Opcode-independent bound-label preservation for body compilation. *)
Theory bodyBoundLabels
Ancestors
  helperBoundLabels boundLabelRules exprLowering stmtLowering emitHelper context compileEnv loweringShapeDefs

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

Theorem bound_labels_emit_membership_eqs:
  !xs s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (emit_membership_eqs needle xs s))))
Proof
  Induct >> simp[emit_membership_eqs_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_fold_membership_or:
  !cs acc s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (fold_membership_or acc cs s))))
Proof
  Induct >> simp[fold_membership_or_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_fold_membership_and:
  !cs acc s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (fold_membership_and acc cs s))))
Proof
  Induct >> simp[fold_membership_and_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_list_membership_in:
  !xs s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_list_membership_in needle xs s))))
Proof
  gen_tac >> simp[compile_list_membership_in_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def,
      bound_labels_emit_membership_eqs, bound_labels_fold_membership_or]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac, CASE_TAC])
QED

Theorem bound_labels_list_membership_notin:
  !xs s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_list_membership_notin needle xs s))))
Proof
  gen_tac >> simp[compile_list_membership_notin_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def,
      bound_labels_emit_membership_eqs, bound_labels_fold_membership_and]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac, CASE_TAC])
QED

Theorem bound_labels_array_membership_loop:
  (!l. compiler_label l ==> P l) /\
  (!op t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (loader op t))))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_array_membership_loop needle arr len sz off loader bound_opt is_in s))))
Proof
  strip_tac >> Cases_on `bound_opt` >> simp[compile_array_membership_loop_def] >>
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
    (SND (compile_return_value_decode lo hi s))))
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

Theorem bound_labels_ifexp_arm:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ifexp_arm ce res_ty arm_ty vv s))))
Proof
  strip_tac >> simp[compile_ifexp_arm_def] >> IF_CASES_TAC
  >- simp[bound_labels_unwrap_value] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer,
    bound_labels_unwrap_value, bound_labels_store_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
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
    (SND (compile_dynarray_pop base_op ws sz ctor imm loc s))))
Proof
  strip_tac >> simp[compile_dynarray_pop_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_ptr_load, bound_labels_ptr_store]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_stage_intcall_args:
  !ce vals flags tys s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stage_intcall_args ce vals flags tys s))))
Proof
  recInduct compile_stage_intcall_args_ind >> rpt strip_tac >>
  simp[compile_stage_intcall_args_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_unwrap_value,
    bound_labels_alloc_buffer, bound_labels_emit_void,
    bound_labels_store_bytestring, bound_labels_store_memory,
    comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC,
    first_x_assum irule])
QED

Theorem bound_labels_store_multi_results:
  !buf ops off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (store_multi_results buf ops off s))))
Proof
  Induct_on `ops` >> simp[store_multi_results_def, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >>
  simp[bound_labels_emit_op] >> rpt strip_tac >>
  irule bound_labels_ignore_bind >> simp[bound_labels_emit_void]
QED

Theorem bound_labels_array_subscript:
  (!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (loader base_op t))))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_array_subscript base_op idx dyn static_count scale sz signed loader s))))
Proof
  strip_tac >> simp[compile_array_subscript_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
    bound_labels_emit_void, comp_return_def]), gen_tac, strip_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_tuple_subscript:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_tuple_subscript base_op off s))))
Proof
  simp[compile_tuple_subscript_def, bound_labels_emit_op]
QED

Theorem bound_labels_store_byte_chunks:
  !ptr bs off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_store_byte_chunks ptr bs off s))))
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def, comp_return_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op] >>
  rpt strip_tac >> irule bound_labels_ignore_bind >>
  simp[bound_labels_emit_void] >> gvs[]
QED

Theorem bound_labels_bytelike_literal:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_bytelike_literal bs n s))))
Proof
  strip_tac >> simp[compile_bytelike_literal_def] >>
  irule bound_labels_bind >> simp[bound_labels_alloc_buffer] >>
  rpt strip_tac >> irule bound_labels_ignore_bind >>
  simp[bound_labels_emit_void] >> rpt strip_tac >>
  irule bound_labels_ignore_bind >>
  simp[bound_labels_store_byte_chunks, comp_return_def]
QED

Theorem bound_labels_literal_vv:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_literal_vv ty lit s))))
Proof
  strip_tac >> Cases_on `lit` >>
  simp[compile_literal_vv_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_bytelike_literal, comp_return_def]),
    CASE_TAC, irule bound_labels_bind, conj_tac, gen_tac, strip_tac]) >>
  Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def]
QED

Theorem bound_labels_name_vv:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_name_vv ce ty id s))))
Proof
  strip_tac >> simp[compile_name_vv_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, comp_return_def]),
    CASE_TAC, irule bound_labels_ignore_bind, conj_tac, gen_tac, strip_tac])
QED

Theorem bound_labels_env_var:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_env_var ev s))))
Proof
  strip_tac >> Cases_on `ev` >> simp[compile_env_var_def, bound_labels_emit_op] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op]),
    irule bound_labels_bind, conj_tac, gen_tac, strip_tac])
QED

Theorem bound_labels_load_bytestring_as_word:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (load_bytestring_as_word v opc s))))
Proof
  strip_tac >> simp[load_bytestring_as_word_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def]),
    irule bound_labels_bind, conj_tac, gen_tac, strip_tac, IF_CASES_TAC])
QED

Theorem bound_labels_int_clamp:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_int_clamp signed bits v s))))
Proof
  strip_tac >> simp[compile_int_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), IF_CASES_TAC, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, gen_tac, strip_tac])
QED

Theorem bound_labels_type_convert:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_convert v cv s))))
Proof
  strip_tac >> Cases_on `cv` >> simp[compile_type_convert_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_int_clamp, bound_labels_alloc_buffer,
    bound_labels_load_bytestring_as_word, comp_return_def]),
    gen_tac, strip_tac, pairarg_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_neg:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_neg v ty s))))
Proof
  strip_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op] >>
  rpt strip_tac >> irule bound_labels_ignore_bind >>
  simp[bound_labels_emit_void, bound_labels_emit_op]
QED

Theorem bound_labels_lower_value:
  (!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (lower_value cfn ce ty e s))))
Proof
  strip_tac >> simp[lower_value_def] >> irule bound_labels_bind >>
  simp[bound_labels_unwrap_value]
QED

Theorem bound_labels_multi_exprs:
  !es. (!e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) ==>
  !s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_multi_exprs cfn ce es s))))
Proof
  Induct >> simp[compile_multi_exprs_def, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >> irule bound_labels_bind >>
      simp[comp_return_def] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> irule bound_labels_lower_value >> simp[]
QED

Theorem bound_labels_make_tuple:
  !es. (!e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) ==>
  !buf off s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_make_tuple cfn ce es buf off s))))
Proof
  Induct >> simp[compile_make_tuple_def, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
        bound_labels_unwrap_value, bound_labels_store_memory]),
        irule bound_labels_bind, irule bound_labels_ignore_bind,
        conj_tac, gen_tac, strip_tac]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem bound_labels_make_array_elems:
  !es. (!e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) ==>
  !ty sz has_len buf idx s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_make_array_elems cfn ce es ty sz has_len buf idx s))))
Proof
  Induct >> simp[compile_make_array_elems_def, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
        bound_labels_unwrap_value, bound_labels_store_memory]),
        irule bound_labels_bind, irule bound_labels_ignore_bind,
        conj_tac, gen_tac, strip_tac]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem bound_labels_make_array:
  (!e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_make_array cfn ce es ty sz has_len buf s))))
Proof
  strip_tac >> simp[compile_make_array_def] >>
  irule bound_labels_ignore_bind >> conj_tac
  >- (rpt strip_tac >> IF_CASES_TAC >>
      simp[bound_labels_emit_void, comp_return_def]) >>
  simp[] >> rpt strip_tac >> irule bound_labels_make_array_elems >> simp[]
QED

Theorem bound_labels_concat:
  !es. (!e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) ==>
  !ptr infos off s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_concat cfn ce es ptr infos off s))))
Proof
  Induct >> simp[compile_concat_def, comp_return_def] >>
  rpt strip_tac >> Cases_on `infos` >> simp[compile_concat_def, comp_return_def] >>
  rename1 `compile_concat cfn ce (e1::es1) ptr1 (info::rest) off1 s1` >>
  PairCases_on `info` >> simp[compile_concat_def] >>
  IF_CASES_TAC >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
        irule bound_labels_bind, irule bound_labels_ignore_bind,
        conj_tac, gen_tac, strip_tac]) >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >- (simp[] >> rpt strip_tac >> irule bound_labels_lower_value >> simp[])
  >- (simp[] >> rpt strip_tac >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
        irule bound_labels_bind, irule bound_labels_ignore_bind,
        conj_tac, gen_tac, strip_tac]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> irule bound_labels_lower_value >> simp[]
QED

Theorem bound_labels_subscript:
  (!ty e t. (e = base_e \/ e = idx_e) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_subscript cfn ce ret_ty ty base_e idx_e s))))
Proof
  strip_tac >> simp[compile_subscript_def] >> irule bound_labels_bind >>
  simp[] >> rpt strip_tac >>
  qabbrev_tac `loc = case vv_location x of NONE => LocMemory | SOME l => l` >>
  Cases_on `place_type ce base_e` >> simp[] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_tuple_subscript,
    bound_labels_mapping_subscript, bound_labels_keccak256_key,
    bound_labels_lower_value, bound_labels_array_subscript,
    bound_labels_ptr_load, comp_return_def]),
    irule bound_labels_bind, conj_tac, gen_tac, strip_tac,
    CASE_TAC, IF_CASES_TAC])
QED

Theorem bound_labels_attribute:
  (!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_attribute cfn ce ret_ty ty e fld s))))
Proof
  strip_tac >> simp[compile_attribute_def] >> irule bound_labels_bind >>
  simp[] >> rpt strip_tac >> irule bound_labels_bind >>
  simp[bound_labels_emit_op, comp_return_def]
QED

Theorem bound_labels_struct_lit:
  !fields. (!name e t. MEM (name,e) fields /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (expr_type e) e t))))) ==>
  !ty buf off s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_struct_lit cfn ce ty fields buf off s))))
Proof
  Induct >> simp[compile_struct_lit_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt strip_tac >>
  simp[compile_struct_lit_def] >> irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
        bound_labels_unwrap_value, bound_labels_store_memory]),
        irule bound_labels_bind, irule bound_labels_ignore_bind,
        conj_tac, gen_tac, strip_tac]) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem bound_labels_materialize_vv:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_materialize_vv ce ty vv s))))
Proof
  strip_tac >> simp[compile_materialize_vv_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer,
    bound_labels_unwrap_value, bound_labels_store_memory, comp_return_def]),
    irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, gen_tac, strip_tac])
QED

Theorem bound_labels_abi_encode_args:
  !es s. (!ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_abi_encode_args cfn ce es s))))
Proof
  Induct >> simp[compile_abi_encode_args_def, comp_return_def] >>
  rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_materialize_vv,
                bound_labels_unwrap_value, comp_return_def]),
              irule bound_labels_bind, conj_tac, gen_tac, strip_tac,
              IF_CASES_TAC])
QED

Theorem bound_labels_ext_call_kwarg:
  (!ty t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ext_call_kwarg cfn ce ret_ty k e s))))
Proof
  strip_tac >> simp[compile_ext_call_kwarg_def] >> IF_CASES_TAC >>
  irule bound_labels_bind >> simp[bound_labels_lower_value, comp_return_def] >>
  rpt strip_tac >> irule bound_labels_bind >>
  simp[bound_labels_materialize_vv, comp_return_def]
QED

Theorem bound_labels_ext_call_kwargs:
  !es. (!ty e t. MEM e es /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce ty e t))))) ==>
  !ret_ty ks s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_ext_call_kwargs cfn ce ret_ty ks es s))))
Proof
  Induct >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
  rpt strip_tac >> Cases_on `ks` >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
  irule bound_labels_bind >> conj_tac
  >- (simp[] >> rpt strip_tac >> pairarg_tac >> simp[] >>
      irule bound_labels_bind >> simp[comp_return_def] >>
      rpt strip_tac >> pairarg_tac >> simp[comp_return_def]) >>
  simp[] >> rpt strip_tac >> irule bound_labels_ext_call_kwarg >> simp[]
QED

Theorem bound_labels_store_words:
  !vs buf off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_store_words buf vs off s))))
Proof
  Induct >> simp[compile_store_words_def, comp_return_def] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    comp_return_def]), irule bound_labels_bind, irule bound_labels_ignore_bind,
    conj_tac, gen_tac, strip_tac, IF_CASES_TAC])
QED

Theorem bound_labels_invert:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_invert v ty ce s))))
Proof
  Cases_on `ty` >> simp[compile_invert_def, bound_labels_emit_op]
QED


Theorem bound_labels_acc:
  (!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (cfn ce (BaseT AddressT) e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_acc cfn ce e acc s))))
Proof
  strip_tac >> Cases_on `acc` >> simp[compile_acc_def, bound_labels_lower_value] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_lower_value, bound_labels_emit_op,
    bound_labels_emit_inst]), irule pair_let_snd_preserves,
    conj_tac, gen_tac, strip_tac])
QED

Theorem bound_labels_get_target_ptr:
  !target. (!ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) ==>
  !s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_get_target_ptr cfn ce target s))))
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac >>
  simp[Once compile_get_target_ptr_def]
  >- (rpt CASE_TAC >> simp[comp_return_def])
  >- (rpt CASE_TAC >> simp[comp_return_def]) >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[] >> rpt strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_lower_value,
    bound_labels_keccak256_key, bound_labels_mapping_subscript,
    bound_labels_array_subscript, bound_labels_ptr_load,
    bound_labels_emit_op, comp_return_def]),
    irule bound_labels_bind, conj_tac, gen_tac, strip_tac,
    CASE_TAC, IF_CASES_TAC])
QED

Theorem bound_labels_lower_value_with_loc:
  (!t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (lower_value_with_loc cfn ce ty e s))))
Proof
  strip_tac >> simp[lower_value_with_loc_def] >>
  irule bound_labels_bind >> simp[] >> rpt strip_tac >>
  irule bound_labels_bind >> simp[comp_return_def, bound_labels_unwrap_value]
QED


Theorem bound_labels_intcall[local]:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty (IntCall fid) args default_ret s))))
Proof
  strip_tac >> Cases_on `ce.ce_func_info (nsid_to_string fid)` >>
  rename1 `ce.ce_func_info (nsid_to_string fid) = (num_ret, meta_pair)` >>
  PairCases_on `meta_pair` >> simp[compile_call_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_multi_vvs >> simp[]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[] >>
      irule pair_let_snd_preserves >>
      simp[bound_labels_alloc_buffer]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_stage_intcall_args] >>
  rpt strip_tac >> simp[] >> IF_CASES_TAC >> CASE_TAC >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_op, bound_labels_emit_multi_op,
          bound_labels_emit_void] >>
  rpt strip_tac >>
  simp[bound_labels_emit_op, bound_labels_emit_multi_op,
       bound_labels_emit_void] >>
  irule pair_let_snd_preserves >>
  simp[bound_labels_store_multi_results]
QED

Theorem bound_labels_call_send[local]:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty (Send has_gas) args default_ret s))))
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e rest_es"] >>
  simp[compile_call_def]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  Cases_on `rest_es` >> simp[compile_call_def]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  IF_CASES_TAC >> simp[]
  >- (irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
      rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
      rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (rpt CASE_TAC >> simp[] >> irule bound_labels_lower_value >>
          simp[] >> metis_tac[listTheory.MEM]) >>
      rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- simp[bound_labels_emit_op] >>
      rpt strip_tac >> simp[] >> irule pair_let_snd_preserves >>
      simp[bound_labels_emit_void]) >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]
QED

Theorem bound_labels_call_raw_calldata[local]:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty (RawCallCalldataTarget rcf)
                      args default_ret s))))
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e kw_es"] >>
  simp[compile_call_def]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_ext_call_kwargs >> simp[] >> metis_tac[listTheory.MEM]) >>
  qx_gen_tac `kvs` >> qx_gen_tac `st1` >> strip_tac >>
  PairCases_on `kvs` >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (CASE_TAC >> simp[bound_labels_emit_op]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_raw_call_outbuf] >>
  qx_gen_tac `outs` >> qx_gen_tac `st2` >> strip_tac >>
  PairCases_on `outs` >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_msg_data_to_memory] >>
  qx_gen_tac `data_ops` >> qx_gen_tac `st3` >> strip_tac >>
  PairCases_on `data_ops` >> simp[] >>
  irule pair_let_snd_preserves >>
  simp[bound_labels_raw_call_finish] >> rpt strip_tac >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_void] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem bound_labels_call_raw[local]:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty (RawCallTarget rcf) args default_ret s))))
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e rest_es"] >>
  simp[compile_call_def]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  namedCases_on `rest_es` ["", "data_e kw_es"] >> simp[]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_op] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_op] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_ext_call_kwargs >> simp[] >> metis_tac[listTheory.MEM]) >>
  qx_gen_tac `kvs` >> qx_gen_tac `st1` >> strip_tac >>
  PairCases_on `kvs` >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (CASE_TAC >> simp[bound_labels_emit_op]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_raw_call_outbuf] >>
  qx_gen_tac `outs` >> qx_gen_tac `st2` >> strip_tac >>
  PairCases_on `outs` >> simp[] >>
  irule pair_let_snd_preserves >>
  simp[bound_labels_raw_call_finish] >> rpt strip_tac >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_void] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem bound_labels_call_external[local]:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty
      (ExtCall stat skip (fname, arg_types, return_type) opts) args default_ret s))))
Proof
  strip_tac >> namedCases_on `args` ["", "addr_e rest_es"] >>
  simp[compile_call_def]
  >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[] >> metis_tac[listTheory.MEM]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_multi_vvs >> simp[] >>
      metis_tac[listTheory.MEM, rich_listTheory.MEM_TAKE]) >>
  rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_ext_call_kwargs >> simp[] >>
      metis_tac[listTheory.MEM, rich_listTheory.MEM_DROP_IMP]) >>
  qx_gen_tac `kvs` >> qx_gen_tac `st1` >> strip_tac >>
  PairCases_on `kvs` >> simp[] >>
  Cases_on `kvs2` >> simp[]
  >- (irule pair_let_snd_preserves >> reverse conj_tac
      >- (CASE_TAC >> simp[bound_labels_emit_op]) >>
      rpt strip_tac >> simp[] >> irule pair_let_snd_preserves >>
      simp[bound_labels_external_call_kwargs] >> rpt strip_tac >>
      IF_CASES_TAC >> simp[]) >>
  pairarg_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (CASE_TAC >> simp[bound_labels_emit_op]) >>
  rpt strip_tac >> simp[] >> irule pair_let_snd_preserves >>
  simp[bound_labels_external_call_kwargs] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem bound_labels_as_stack_val[local]:
  SND (as_stack_val ty m) = SND m
Proof
  Cases_on `m` >> simp[as_stack_val_def]
QED

Theorem bound_labels_create_snapshot[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_create_snapshot ce vv bty s))))
Proof
  strip_tac >> simp[compile_create_snapshot_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void, bound_labels_emit_inst,
    bound_labels_alloc_buffer, comp_return_def,
    bound_labels_location_copy, bound_labels_imm_copy_to_memory,
    bound_labels_copy_memory_dynamic]),
    gen_tac, strip_tac, split_pair_case_tac, pairarg_tac,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac,
    IF_CASES_TAC, CASE_TAC])
QED

Theorem bound_labels_create_salt[local]:
  (!e. salt = SOME e ==>
     !ty t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
       EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_create_salt cfn ce salt s))))
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, comp_return_def] >>
  strip_tac >> irule bound_labels_bind >> simp[comp_return_def] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]
QED

Theorem bound_labels_create_ctor_tuple[local]:
  (!ty e t. MEM e es /\ EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_create_ctor_tuple cfn ce es s))))
Proof
  strip_tac >> simp[compile_create_ctor_tuple_def] >> rpt strip_tac >> BETA_TAC >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_multi_vvs >> simp[]) >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_alloc_buffer] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_ignore_bind >>
  simp[bound_labels_extcall_store_values, comp_return_def]
QED

Theorem bound_labels_create_blueprint_args[local]:
  (!ty e t. MEM e es /\ EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_create_blueprint_args cfn ce raw es s))))
Proof
  strip_tac >> simp[compile_create_blueprint_args_def] >> IF_CASES_TAC
  >- (Cases_on `es` >> simp[] >- (irule bound_labels_ignore_bind >>
        simp[bound_labels_emit_inst, comp_return_def]) >>
      rename1 `h::tl` >> Cases_on `tl` >> simp[]
      >- (irule bound_labels_bind >> reverse conj_tac
          >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
          rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_emit_op] >>
          rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
          simp[bound_labels_emit_op, comp_return_def]) >>
      irule bound_labels_ignore_bind >>
      simp[bound_labels_emit_inst, comp_return_def]) >>
  IF_CASES_TAC >- simp[comp_return_def] >> rpt strip_tac >> BETA_TAC >>
  irule bound_labels_bind >> simp[bound_labels_alloc_buffer] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_create_ctor_tuple >> simp[]) >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
  simp[cj 2 bound_labels_abi_encode, comp_return_def]
QED

Theorem bound_labels_raw_create[local]:
  (!ty e t. (e = be \/ e = ve \/ MEM e cargs \/ salt = SOME e) /\
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_raw_create cfn ce be ve cargs salt rof s))))
Proof
  strip_tac >> simp[compile_raw_create_def] >> rpt strip_tac >> BETA_TAC >>
  irule bound_labels_bind >> simp[] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_create_snapshot] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_emit_op] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_emit_op] >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> IF_CASES_TAC >- simp[comp_return_def] >> rpt strip_tac >> BETA_TAC >>
      irule bound_labels_bind >> simp[bound_labels_alloc_buffer] >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_ignore_bind >>
      simp[bound_labels_copy_memory_dynamic] >> rpt strip_tac >> BETA_TAC >>
      irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_create_ctor_tuple >> simp[]) >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> simp[bound_labels_emit_op] >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
      simp[cj 2 bound_labels_abi_encode] >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
      simp[bound_labels_emit_op, comp_return_def]) >>
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> BETA_TAC >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_create_salt >> simp[]) >>
  simp[bound_labels_create_dispatch]
QED

Theorem bound_labels_create_call[local]:
  (!ty e t. MEM e args /\ EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
     EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_create_call cfn ce ck salted rof args s))))
Proof
  strip_tac >> simp[compile_create_call_def] >>
  namedCases_on `args` ["", "t_e rest1"] >> simp[]
  >- (irule bound_labels_ignore_bind >>
      simp[bound_labels_emit_inst, comp_return_def]) >>
  namedCases_on `rest1` ["", "v_e rest"] >> simp[]
  >- (irule bound_labels_ignore_bind >>
      simp[bound_labels_emit_inst, comp_return_def]) >>
  IF_CASES_TAC
  >- (irule bound_labels_ignore_bind >>
      simp[bound_labels_emit_inst, comp_return_def]) >>
  `salted ==> rest <> []` by (rpt strip_tac >> gvs[]) >>
  Cases_on `ck`
  >~ [`RawCreate`]
  >- (simp[] >> irule bound_labels_raw_create >> simp[] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >>
      metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL, rich_listTheory.MEM_LAST_NOT_NIL,
                listTheory.MEM])
  >~ [`CreateMinimalProxy`]
  >- (simp[] >>
      irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> simp[] >>
      irule bound_labels_bind >> simp[bound_labels_create_proxy_buf] >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
      simp[bound_labels_create_dispatch] >> rpt strip_tac >> BETA_TAC >>
      irule bound_labels_create_salt >> simp[] >> rpt strip_tac >>
          gvs[AllCaseEqs()] >> Cases_on `rest` >> gvs[])
  >~ [`CreateCopyOf`]
  >- (simp[] >>
      irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> simp[] >>
      irule bound_labels_bind >> simp[bound_labels_create_copy] >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_create_salt >> simp[] >> rpt strip_tac >>
          gvs[AllCaseEqs()] >> Cases_on `rest` >> gvs[]) >>
  simp[] >>
      irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
      >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[]) >>
      rpt strip_tac >> simp[] >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_create_salt >> simp[] >> rpt strip_tac >>
          gvs[AllCaseEqs()] >> Cases_on `rest` >> gvs[]) >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >> irule bound_labels_lower_value >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> Cases_on `salted` >> gvs[] >>
      Cases_on `rest` >> gvs[] >> rename1 `HD tl` >> Cases_on `tl` >> gvs[]) >>
  rpt strip_tac >> BETA_TAC >> irule bound_labels_bind >>
  simp[bound_labels_create_blueprint_check] >>
  simp[pairTheory.FORALL_PROD] >> rpt strip_tac >> BETA_TAC >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> BETA_TAC >>
      irule bound_labels_create_blueprint_args >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> Cases_on `salted` >> gvs[] >>
      Cases_on `rest` >> gvs[] >> metis_tac[listTheory.MEM_TL, listTheory.MEM]) >>
  simp[pairTheory.FORALL_PROD, bound_labels_create_blueprint_append]
QED

Theorem bound_labels_call:
  (!ty e t. MEM e args /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!ty e t. MEM e (FLAT (MAP raw_log_topic_exprs args)) /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (cfn ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_call cfn ce ret_ty ty ct args default_ret s))))
Proof
  strip_tac >> Cases_on `ct`
  >- (irule bound_labels_intcall >> simp[])
  >- (rename1 `ExtCall b b0 sig_tuple opts` >> PairCases_on `sig_tuple` >>
      irule bound_labels_call_external >> simp[])
  >- (irule bound_labels_call_send >> simp[])
  >- (irule bound_labels_call_raw >> simp[])
  >- (irule bound_labels_call_raw_calldata >> simp[])
  >~ [`CreateTarget`]
  >- (simp[compile_call_def, bound_labels_as_stack_val] >>
      irule bound_labels_create_call >> simp[])
  >~ [`RawLog`]
  >- (simp[compile_call_def] >> Cases_on `args` >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      Cases_on `t` >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      reverse (Cases_on `t'`) >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_multi_exprs >> simp[] >>
          TRY (rpt strip_tac >>
               qpat_x_assum `!ty e t. MEM e (FLAT _) /\ _ ==> _` irule >>
               simp[])) >>
      rpt gen_tac >> strip_tac >>
      Cases_on `expr_type h' = BaseT (BytesT (Fixed 32))` >> simp[] >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_emit_op,
                    bound_labels_emit_void, bound_labels_alloc_buffer]),
                  irule pair_let_snd_preserves, irule bound_labels_lower_value,
                  conj_tac, gen_tac, strip_tac]))
  >~ [`RawRevert`]
  >- (simp[compile_call_def] >> Cases_on `args` >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      reverse (Cases_on `t`) >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[]) >>
      rpt gen_tac >> strip_tac >> simp[] >> irule pair_let_snd_preserves >>
      simp[bound_labels_raw_revert])
  >~ [`SelfDestructTarget`]
  >- (simp[compile_call_def] >> Cases_on `args` >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      reverse (Cases_on `t`) >> simp[]
      >- (irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[]) >>
      rpt gen_tac >> strip_tac >> simp[] >> irule pair_let_snd_preserves >>
      simp[bound_labels_selfdestruct]) >>
  simp[compile_call_def] >> irule pair_let_snd_preserves >>
  simp[bound_labels_emit_inst]
QED

Theorem bound_labels_addmod_names:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_addmod_names ce rt aty a bty b mty m s))))
Proof
  strip_tac >> simp[compile_addmod_names_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  simp[as_stack_val_def] >> irule pair_let_snd_preserves >>
  simp[bound_labels_addmod, as_stack_val_def]
QED

Theorem bound_labels_mulmod_names:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_mulmod_names ce rt aty a bty b mty m s))))
Proof
  strip_tac >> simp[compile_mulmod_names_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  simp[as_stack_val_def] >> irule pair_let_snd_preserves >>
  simp[bound_labels_mulmod, as_stack_val_def]
QED

Theorem bound_labels_powmod256_names:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_powmod256_names ce rt aty a bty b s))))
Proof
  strip_tac >> simp[compile_powmod256_names_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_name_vv] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >> simp[] >>
  simp[as_stack_val_def] >> irule pair_let_snd_preserves >>
  simp[bound_labels_pow_mod256, as_stack_val_def]
QED


Theorem bound_labels_fresh_pair[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) /\
  (!l t. compiler_label l /\
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g (l,t)))))) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (g (fresh_label suffix s)))))
Proof
  strip_tac >> Cases_on `fresh_label suffix s` >>
  drule bound_labels_fresh_label >> strip_tac >> gvs[]
QED

Theorem bound_labels_expr_ifexp[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty (IfExp ann cond_e then_e else_e) s))))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_primitives] >> rpt strip_tac >> simp[] >>
  irule bound_labels_fresh_pair >> simp[] >> rpt strip_tac >> simp[] >>
  irule bound_labels_fresh_pair >> simp[] >> rpt strip_tac >> simp[] >>
  irule bound_labels_fresh_pair >> simp[] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_inst] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_new_block] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_ifexp_arm] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_inst] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_inst] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_new_block] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_ifexp_arm] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_inst] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_inst] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_new_block] >> rpt strip_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem bound_labels_expr_structlit[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty (StructLit ann name fields) s))))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_struct_lit >> simp[]) >> simp[]
QED

Theorem bound_labels_expr_toplevelname[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty (TopLevelName ann nsid) s))))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid`
  >- (simp[] >> irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]) >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]
QED

Theorem bound_labels_expr_pop[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty (Pop ann target) s))))
Proof
  strip_tac >> simp[compile_expr_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_get_target_ptr >> simp[]) >>
  map_every qx_gen_tac [`v`, `t`] >> strip_tac >>
  PairCases_on `v` >> simp[] >>
  irule pair_let_snd_preserves >> simp[bound_labels_dynarray_pop]
QED

Theorem bound_labels_invalid_expr_call[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (invalid_expr_call ty s))))
Proof
  strip_tac >> simp[exprCallBoundsTheory.invalid_expr_call_def] >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_inst]
QED

Theorem bound_labels_expr_child_callback[local]:
  (!ce ty e s. expr_size e < bound ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e s))))) ==>
  !ce ty e s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (expr_child_callback bound f ce ty e s))))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.expr_child_callback_def] >>
  IF_CASES_TAC >> simp[bound_labels_invalid_expr_call]
QED

Theorem bound_labels_builtin_child_callback[local]:
  (!ce rt ty bi args s. list_size expr_size args < bound ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce rt ty bi args s))))) ==>
  !ce rt ty bi args s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (builtin_child_callback bound f ce rt ty bi args s))))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.builtin_child_callback_def] >>
  IF_CASES_TAC >> simp[bound_labels_invalid_expr_call]
QED

Theorem bound_labels_type_child_callback[local]:
  (!ce vt ty tb rt args s. list_size expr_size args < bound ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce vt ty tb rt args s))))) ==>
  !ce vt ty tb rt args s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (type_child_callback bound f ce vt ty tb rt args s))))
Proof
  rpt strip_tac >> simp[exprCallBoundsTheory.type_child_callback_def] >>
  IF_CASES_TAC >> simp[bound_labels_invalid_expr_call]
QED

Theorem bound_labels_list_case_constant[local]:
  list_CASE xs c (\h t. c) = c
Proof
  Cases_on `xs` >> simp[]
QED

Theorem bound_labels_expr_case_constant[local]:
  expr_CASE e (\a b. c) (\a b. c) (\a b d. c)
    (\a b d f. c) (\a b. c) (\a b d. c) (\a b d. c)
    (\a b d. c) (\a b d. c) (\a b d f. c) (\a b. c) (\a b d f. c) = c
Proof
  Cases_on `e` >> simp[]
QED

Theorem bound_labels_expr_builtin[local]:
  (!ce rt ty bi args t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g ce rt ty bi args t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty (Builtin ann bi args) s))))
Proof
  strip_tac >> Cases_on `bi` >>
  simp([compile_expr_body_def, bound_labels_addmod_names,
        bound_labels_mulmod_names, bound_labels_powmod256_names,
        bound_labels_list_case_constant, bound_labels_expr_case_constant] @
       map TypeBase.case_rand_of [``:'a list``, ``:expr``])
QED

Theorem bound_labels_expr_body[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!ce rt ty bi args t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (g ce rt ty bi args t))))) /\
  (!ce vt ty tb rt args t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (h ce vt ty tb rt args t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_expr_body f g h ce ty e s))))
Proof
  strip_tac >> Cases_on `e` >>
  simp[bound_labels_expr_ifexp, bound_labels_expr_structlit,
       bound_labels_expr_toplevelname, bound_labels_expr_pop,
       bound_labels_expr_builtin] >>
  simp[compile_expr_body_def, bound_labels_literal_vv, bound_labels_name_vv] >>
  FIRST [irule bound_labels_subscript, irule bound_labels_attribute,
         irule bound_labels_call] >> simp[]
QED

Theorem bound_labels_as_ptr_val[local]:
  SND (as_ptr_val ty loc m) = SND m
Proof
  Cases_on `m` >> simp[as_ptr_val_def]
QED

Theorem bound_labels_builtin_scalar[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !bi. (bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
        bi = Ceil \/ bi = Floor \/ (?n. bi = Uint2Str n) \/
        (?n. bi = CalldataSlice n) \/ bi = AddMod \/ bi = MulMod \/
        bi = PowMod256) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (irule pair_let_snd_preserves >> reverse conj_tac
    >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
  simp[bound_labels_as_stack_val, bound_labels_as_ptr_val,
       bound_labels_neg, bound_labels_builtin_abs, bound_labels_blockhash,
       bound_labels_blobhash, bound_labels_ceil, bound_labels_floor,
       bound_labels_uint2str, bound_labels_slice_calldata,
       bound_labels_addmod, bound_labels_mulmod, bound_labels_pow_mod256]
QED

Theorem bound_labels_builtin_environment[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !bi. ((?i. bi = Env i) \/ (?i. bi = Acc i) \/ bi = CalldataLen) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, bound_labels_as_stack_val,
       bound_labels_env_var, bound_labels_builtin_calldatasize] >>
  irule bound_labels_acc >> simp[]
QED

Theorem bound_labels_builtin_branching_scalar[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !bi. (bi = Not \/ bi = Len \/ (?d. bi = AsWeiValue d)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def] >>
  (irule pair_let_snd_preserves >> reverse conj_tac
   >- (simp[] >> irule bound_labels_lower_value >> simp[]) >>
   rpt strip_tac >> simp[] >>
   rpt IF_CASES_TAC >>
   simp[bound_labels_as_stack_val, bound_labels_emit_op,
        bound_labels_invert, bound_labels_builtin_len,
        bound_labels_as_wei_value_decimal, bound_labels_as_wei_value_int])
QED

Theorem bound_labels_builtin_hash[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !bi. (bi = Keccak256 \/ bi = Sha256) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def] >>
  (IF_CASES_TAC
   >- (irule pair_let_snd_preserves >> reverse conj_tac
       >- (irule bound_labels_lower_value >> simp[]) >>
       rpt strip_tac >> simp[bound_labels_as_stack_val,
         bound_labels_keccak256_bytes, bound_labels_sha256_bytes]) >>
   Cases_on `expr_type (HD args)` >> simp[] >>
   TRY (rename1 `BaseT bt` >> Cases_on `bt` >> simp[] >>
        TRY (rename1 `BytesT bnd` >> Cases_on `bnd` >> simp[])) >>
   (irule pair_let_snd_preserves >> reverse conj_tac
    >- (irule bound_labels_lower_value >> simp[]) >>
    rpt strip_tac >> simp[bound_labels_as_stack_val,
      bound_labels_keccak256_bytesm, bound_labels_sha256_bytesm,
      bound_labels_keccak256_word, bound_labels_sha256_word]))
QED

Theorem bound_labels_builtin_ec[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !bi. (bi = ECRecover \/ bi = ECAdd \/ bi = ECMul) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `bi` >> simp[] >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (irule pair_let_snd_preserves >> reverse conj_tac
    >- (simp[bound_labels_unwrap_value] >>
        irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
  simp[bound_labels_as_stack_val, bound_labels_as_ptr_val,
       bound_labels_ecrecover, bound_labels_ecadd_points, bound_labels_ecmul_point]
QED

Theorem bound_labels_builtin_method_id[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty MethodId args s))))
Proof
  strip_tac >> Cases_on `method_id_literal (HD args)` >>
  simp[compile_builtin_dispatch_body_def, bound_labels_literal_vv] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >>
  rpt strip_tac >> simp[] >> IF_CASES_TAC >>
  simp[bound_labels_as_stack_val, bound_labels_as_ptr_val,
       bound_labels_method_id_runtime]
QED

Theorem bound_labels_builtin_concat[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty (Concat n) args s))))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_op] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_void] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_concat >> simp[]) >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_op] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> simp[bound_labels_emit_void]
QED

Theorem bound_labels_builtin_makearray[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty (MakeArray opt bnd) args s))))
Proof
  strip_tac >> Cases_on `opt` >> simp[compile_builtin_dispatch_body_def] >>
  (irule pair_let_snd_preserves >> reverse conj_tac
   >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >>
   simp[bound_labels_as_ptr_val] >>
   FIRST [irule bound_labels_make_tuple, irule bound_labels_make_array] >> simp[])
QED

Theorem bound_labels_bytestring_widen_copy:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_bytestring_widen_copy n v m s))))
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >>
  irule bound_labels_bind >> simp[bound_labels_alloc_buffer] >>
  rpt strip_tac >> irule bound_labels_ignore_bind >>
  simp[bound_labels_copy_memory, comp_return_def]
QED

Theorem bound_labels_type_builtin_convert[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty Convert rt args s))))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >>
  rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[] >> IF_CASES_TAC
  >- simp[bound_labels_as_stack_val, bound_labels_bytestring_widen_copy] >>
  Cases_on `rt` >> simp[bound_labels_as_stack_val, bound_labels_type_convert]
QED

Theorem bound_labels_type_builtin_constants[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  !tb. (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty tb rt args s))))
Proof
  strip_tac >> gen_tac >> Cases_on `type_bounds rt` >> Cases_on `tb` >>
  simp[compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC >> simp[] >>
  irule pair_let_snd_preserves >> simp[bound_labels_builtin_empty_complex]
QED

Theorem bound_labels_type_builtin_extract32[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty Extract32 rt args s))))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_bytestring_src] >>
  map_every qx_gen_tac [`v`, `t`] >> strip_tac >> PairCases_on `v` >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_extract32_load] >> rpt strip_tac >>
  simp[bound_labels_as_stack_val, bound_labels_clamp_basetype]
QED

Theorem bound_labels_type_builtin_abi_decode[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty (AbiDecode u) rt args s))))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_unwrap_value] >> rpt strip_tac >>
  simp[bound_labels_as_ptr_val, bound_labels_lower_abi_decode]
QED

Theorem bound_labels_store_abi_tuple[local]:
  !xs ce buf off s. (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_store_abi_tuple ce buf off xs s))))
Proof
  Induct >> rpt gen_tac
  >- simp[compile_store_abi_tuple_def, comp_return_def] >>
  PairCases_on `h` >> strip_tac >> simp[compile_store_abi_tuple_def] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op] >>
  rpt strip_tac >> irule bound_labels_ignore_bind >> simp[] >>
  IF_CASES_TAC >> simp[bound_labels_emit_void, bound_labels_copy_memory]
QED

Theorem bound_labels_type_builtin_abi_encode[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty (AbiEncode u mid) rt args s))))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (irule pair_let_snd_preserves >> reverse conj_tac
          >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
          irule pair_let_snd_preserves >> reverse conj_tac
          >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
          irule pair_let_snd_preserves >> reverse conj_tac
          >- simp[bound_labels_emit_void] >> rpt strip_tac >>
          simp[bound_labels_as_ptr_val, bound_labels_lower_abi_encode]) >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- simp[] >> rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- simp[bound_labels_unwrap_value] >> rpt strip_tac >>
      simp[bound_labels_as_ptr_val, bound_labels_lower_abi_encode]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_abi_encode_args >> simp[]) >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_store_abi_tuple] >> rpt strip_tac >>
  simp[bound_labels_as_ptr_val, bound_labels_lower_abi_encode]
QED

Theorem bound_labels_type_builtin_body[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_type_builtin_dispatch_body f ce vt ty tb rt args s))))
Proof
  strip_tac >> Cases_on `tb` >>
  simp[bound_labels_type_builtin_convert, bound_labels_type_builtin_constants,
       bound_labels_type_builtin_extract32, bound_labels_type_builtin_abi_encode,
       bound_labels_type_builtin_abi_decode]
QED

Theorem bound_labels_builtin_slice[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty (Slice n) args s))))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  Cases_on `is_msg_data (HD args) \/ is_self_code (HD args)`
  >- (rpt IF_CASES_TAC >> gvs[] >>
      rpt (irule pair_let_snd_preserves >> reverse conj_tac
        >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
      simp[bound_labels_as_ptr_val, bound_labels_slice_calldata, bound_labels_slice_code]) >>
  gvs[] >> IF_CASES_TAC
  >- (irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- simp[bound_labels_slice_out_buf] >>
      map_every qx_gen_tac [`v`, `t`] >> strip_tac >> PairCases_on `v` >> simp[] >>
      irule pair_let_snd_preserves >> reverse conj_tac
      >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >>
      simp[bound_labels_as_ptr_val, bound_labels_slice_extcode]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
  IF_CASES_TAC
  >- (irule pair_let_snd_preserves >> reverse conj_tac
      >- simp[bound_labels_bytestring_src] >>
      map_every qx_gen_tac [`v`, `t`] >> strip_tac >> PairCases_on `v` >> simp[] >>
      rpt (irule pair_let_snd_preserves >> reverse conj_tac
        >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
      simp[bound_labels_as_ptr_val, bound_labels_slice_data]) >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_alloc_buffer] >> rpt strip_tac >> simp[] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- simp[bound_labels_emit_void] >> rpt strip_tac >> simp[] >>
  rpt (irule pair_let_snd_preserves >> reverse conj_tac
    >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
  simp[bound_labels_as_ptr_val, bound_labels_slice_data]
QED

Theorem bound_labels_builtin_membership[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) /\
  (op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args))) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty (Bop op) args s))))
Proof
  strip_tac >> (simp[compile_builtin_dispatch_body_def] >>
  irule pair_let_snd_preserves >> reverse conj_tac
  >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[] >>
  Cases_on `HD (TL args)` >> simp[] >>
  TRY (rename1 `Builtin ann bi es` >> Cases_on `bi` >> simp[]) >>
  (irule pair_let_snd_preserves >> reverse conj_tac
   >- (simp[] >> irule bound_labels_multi_exprs >> simp[]) >>
   rpt strip_tac >> simp[] >> rpt IF_CASES_TAC >>
   simp[bound_labels_as_stack_val, bound_labels_list_membership_in,
        bound_labels_list_membership_notin, bound_labels_var_array_membership]))
QED

(* An Eq/NotEq bytestring operand hashes to a literal hash, or is lowered
   and hashed at runtime. *)
Theorem bound_labels_bytestring_operand_hash[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND
    (case bytestring_literal_hash e of
       NONE => (\(m,t1). compile_bytestring_hash m t1) (lower_value f ce ty e t)
     | SOME h => (Lit h, t)))))
Proof
  strip_tac >> CASE_TAC >> simp[] >>
  irule pair_let_snd_preserves >> conj_tac >>
  TRY (irule bound_labels_lower_value >> simp[] >> NO_TAC) >>
  rpt strip_tac >> simp[bound_labels_bytestring_hash]
QED

Theorem bound_labels_builtin_bop[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty (Bop op) args s))))
Proof
  strip_tac >> Cases_on `(op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args)))`
  >- (irule bound_labels_builtin_membership >> simp[]) >>
  simp[compile_builtin_dispatch_body_def] >> IF_CASES_TAC
  >- (irule pair_let_snd_preserves >> conj_tac >>
      TRY (irule bound_labels_bytestring_operand_hash >> simp[] >> NO_TAC) >>
      rpt strip_tac >> simp_tac (srw_ss()) [] >>
      irule pair_let_snd_preserves >> conj_tac >>
      TRY (irule bound_labels_bytestring_operand_hash >> simp[] >> NO_TAC) >>
      rpt strip_tac >> simp_tac (srw_ss()) [] >>
      IF_CASES_TAC >> simp[bound_labels_as_stack_val, bound_labels_emit_op] >>
      irule pair_let_snd_preserves >> simp[bound_labels_emit_op, bound_labels_as_stack_val]) >>
  rpt (irule pair_let_snd_preserves >> reverse conj_tac
    >- (irule bound_labels_lower_value >> simp[]) >> rpt strip_tac >> simp[]) >>
  simp[bound_labels_as_stack_val, bound_labels_binop]
QED

Theorem bound_labels_builtin_body[local]:
  (!ce ty e t. EVERY P (MAP (\bb. bb.bb_label) (all_blocks t)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (f ce ty e t))))) /\
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_builtin_dispatch_body f ce rt ty bi args s))))
Proof
  strip_tac >> Cases_on `bi` >>
  simp[bound_labels_builtin_scalar, bound_labels_builtin_environment,
       bound_labels_builtin_branching_scalar, bound_labels_builtin_hash,
       bound_labels_builtin_ec, bound_labels_builtin_method_id,
       bound_labels_builtin_concat, bound_labels_builtin_makearray,
       bound_labels_builtin_slice, bound_labels_builtin_bop]
QED

Theorem bound_labels_expr_mutual:
  (!l. compiler_label l ==> P l) ==>
  (!ce ty e s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks (SND (compile_expr ce ty e s))))) /\
  (!ce rt ty bi args s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_builtin_dispatch ce rt ty bi args s))))) /\
  (!ce vt ty tb rt args s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_type_builtin_dispatch ce vt ty tb rt args s)))))
Proof
  strip_tac >> ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_expr_raw_def] >>
  simp[bound_labels_expr_body, bound_labels_builtin_body,
       bound_labels_type_builtin_body, bound_labels_expr_child_callback,
       bound_labels_builtin_child_callback, bound_labels_type_child_callback]
QED

Theorem bound_labels_log_eval_all[local]:
  (!l. compiler_label l ==> P l) ==>
  !es s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_log_eval_all ce es s))))
Proof
  strip_tac >> Induct_on `es` >> rpt strip_tac >>
  simp[compile_log_eval_all_def, comp_return_def] >>
  irule bound_labels_bind >> reverse conj_tac
  >- (simp[] >> rpt strip_tac >> irule bound_labels_lower_value >>
      simp[bound_labels_expr_mutual]) >>
  rpt strip_tac >> simp[] >> irule bound_labels_bind >> conj_tac >>
  (* the saved argument is the operand itself or a materialised copy *)
  TRY (rpt strip_tac >> simp[compile_log_save_arg_def] >> IF_CASES_TAC >>
       simp[comp_return_def, bound_labels_materialize_vv] >> NO_TAC) >>
  rpt strip_tac >> simp[] >> irule bound_labels_bind >> simp[comp_return_def]
QED

Theorem bound_labels_log_topic_ops[local]:
  (!l. compiler_label l ==> P l) ==>
  !ops s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_log_topic_ops ops s))))
Proof
  strip_tac >> Induct_on `ops` >> rpt strip_tac >>
  simp[compile_log_topic_ops_def, comp_return_def] >>
  irule bound_labels_bind >> simp[bound_labels_encode_log_topic] >>
  rpt strip_tac >> simp[] >> irule bound_labels_bind >> simp[comp_return_def]
QED

Theorem bound_labels_log_store_data[local]:
  (!l. compiler_label l ==> P l) ==>
  !ce ops tys buf off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_log_store_data ce ops tys buf off s))))
Proof
  strip_tac >> ho_match_mp_tac compile_log_store_data_ind >> rpt strip_tac >>
  simp[compile_log_store_data_def, comp_return_def, bound_labels_emit_void] >>
  irule bound_labels_bind >> simp[bound_labels_emit_op] >> rpt strip_tac >>
  irule bound_labels_ignore_bind >> simp[bound_labels_store_memory]
QED

Theorem bound_labels_load_tuple_elements[local]:
  !tys off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_load_tuple_elements ce base_op tys off s))))
Proof
  Induct_on `tys` >> rpt strip_tac >>
  simp[compile_load_tuple_elements_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_revert_with_reason[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_revert_with_reason ce vv ty sz s))))
Proof
  strip_tac >> simp[compile_revert_with_reason_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer, bound_labels_emit_void,
    bound_labels_emit_op, bound_labels_emit_inst, bound_labels_unwrap_value,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

Theorem bound_labels_reason_message[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (compile_reason_message ce e s))))
Proof
  strip_tac >> Cases_on `e` >> simp[compile_reason_message_def,
    cj 1 bound_labels_expr_mutual] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >>
  simp[compile_reason_message_def, cj 1 bound_labels_expr_mutual] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_reason_message_def, cj 1 bound_labels_expr_mutual] >>
  Cases_on `lit` >> simp[compile_reason_message_def, cj 1 bound_labels_expr_mutual] >>
  irule bound_labels_bind >> simp[bound_labels_bytelike_literal, comp_return_def]
QED

Theorem bound_labels_internal_return[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_internal_return ce rv pc nret rt st et buf s))))
Proof
  strip_tac >> simp[compile_internal_return_def] >> IF_CASES_TAC
  >- (Cases_on `rv` >> simp[bound_labels_emit_inst] >> IF_CASES_TAC >>
      simp[bound_labels_emit_inst] >> irule bound_labels_bind >>
      simp[bound_labels_load_tuple_elements, bound_labels_emit_inst]) >>
  Cases_on `buf` >> simp[bound_labels_emit_inst] >>
  Cases_on `rv` >> simp[bound_labels_emit_inst] >>
  irule bound_labels_ignore_bind >>
  simp[bound_labels_store_memory, bound_labels_emit_inst]
QED

Theorem bound_labels_external_return[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_external_return rv prim raw info sz nr key trans view s))))
Proof
  strip_tac >> simp[compile_external_return_def] >>
  irule bound_labels_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[bound_labels_nonreentrant_unlock, comp_return_def]) >>
  simp[] >> rpt strip_tac >> Cases_on `rv` >> simp[bound_labels_emit_inst] >>
  rpt IF_CASES_TAC >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer, bound_labels_emit_op,
    bound_labels_emit_void, bound_labels_emit_inst, bound_labels_abi_encode,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac])
QED

val bound_labels_assign_case_tac =
  simp[compile_assign_value_def] >>
  rpt (FIRST [gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC,
    CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_emit_inst, bound_labels_alloc_buffer, bound_labels_copy_memory,
    bound_labels_store_memory, bound_labels_memory_typed,
    bound_labels_dynarray_to_storage, bound_labels_store_storage,
    compile_memory_to_storage_def, compile_memory_to_transient_def,
    bound_labels_word_copy_loop, bound_labels_store_transient, bound_labels_imm_store_word,
    bound_labels_imm_store_words, comp_return_def]), CASE_TAC]);

Theorem bound_labels_assign_value[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_assign_value ce dst loc v prim src dt st da sz s))))
Proof
  strip_tac >> Cases_on `loc`
  >~ [`compile_assign_value _ _ LocMemory _ _ _ _ _ _ _ _`]
  >- bound_labels_assign_case_tac
  >~ [`compile_assign_value _ _ LocStorage _ _ _ _ _ _ _ _`]
  >- bound_labels_assign_case_tac
  >~ [`compile_assign_value _ _ LocTransient _ _ _ _ _ _ _ _`]
  >- bound_labels_assign_case_tac
  >~ [`compile_assign_value _ _ LocCode _ _ _ _ _ _ _ _`]
  >- bound_labels_assign_case_tac >>
  bound_labels_assign_case_tac
QED

Theorem bound_labels_tuple_load_all[local]:
  !tys off s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_tuple_load_all ce src tys off s))))
Proof
  Induct_on `tys` >> rpt strip_tac >>
  simp[compile_tuple_load_all_def, comp_return_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_load_memory,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_store_at_loc[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_store_at_loc imm dst v loc s))))
Proof
  strip_tac >> Cases_on `loc` >> simp[compile_store_at_loc_def,
    bound_labels_emit_void] >> Cases_on `x` >>
  simp[compile_store_at_loc_def, bound_labels_emit_void, bound_labels_imm_store_word]
QED

Theorem bound_labels_declare_local[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (declare_local ce id ty s))))
Proof
  strip_tac >> simp[declare_local_def] >> IF_CASES_TAC >>
  simp[comp_return_def] >> irule bound_labels_bind >>
  simp[cj 4 bound_labels_primitives, comp_return_def]
QED

Theorem bound_labels_emit_local_alloca[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (emit_local_alloca ce id s))))
Proof
  strip_tac >> simp[emit_local_alloca_def] >>
  rpt CASE_TAC >> simp[bound_labels_emit_inst, comp_return_def]
QED

Theorem bound_labels_declare_stmt_local[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label)
    (all_blocks (SND (declare_stmt_local ce stmt s))))
Proof
  Cases_on `stmt` >> simp[declare_stmt_local_def,
    bound_labels_declare_local, comp_return_def]
QED

Theorem bound_labels_return_unlock[local]:
  !s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_return_unlock ce s))))
Proof
  rpt strip_tac >> simp[compile_return_unlock_def] >> pairarg_tac >> gvs[] >>
  IF_CASES_TAC >> simp[bound_labels_nonreentrant_unlock, comp_return_def]
QED

Theorem bound_labels_internal_return_from_env[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_internal_return_from_env ce ty sty v pc s))))
Proof
  strip_tac >> simp[compile_internal_return_from_env_def] >>
  irule bound_labels_ignore_bind >> rpt conj_tac >>
  TRY (simp[bound_labels_return_unlock] >> NO_TAC) >>
  rpt strip_tac >>
  irule bound_labels_bind >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule bound_labels_bind >>
      simp[bound_labels_internal_return, comp_return_def]) >>
  simp[] >> rpt CASE_TAC >> simp[comp_return_def] >> rpt strip_tac >>
  irule bound_labels_bind >> simp[bound_labels_emit_op, comp_return_def]
QED

Theorem bound_labels_tuple_store_all[local]:
  (!l. compiler_label l ==> P l) ==>
  !tys targets vals s.
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_tuple_store_all ce tys targets vals s))))
Proof
  strip_tac >> Induct_on `tys` >> rpt gen_tac >>
  Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, comp_return_def] >>
  Cases_on `h'` >> simp[compile_tuple_store_all_def, comp_return_def] >>
  strip_tac >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_void, bound_labels_assign_value,
    bound_labels_store_at_loc, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  irule bound_labels_get_target_ptr >> simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_tuple_unpack[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_tuple_unpack ce ty stage targets src s))))
Proof
  strip_tac >> simp[compile_tuple_unpack_def] >> IF_CASES_TAC >>
  simp[bound_labels_emit_inst] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_alloc_buffer,
    bound_labels_emit_void, bound_labels_tuple_load_all,
    bound_labels_tuple_store_all, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_range_bound_checks[local]:
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_range_bound_checks lo hi rounds rb signed s))))
Proof
  strip_tac >> simp[compile_range_bound_checks_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_iter_elem_copy[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_iter_elem_copy ce src dst sz loc slot dt st s))))
Proof
  strip_tac >> simp[compile_iter_elem_copy_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_ptr_load, compile_slot_to_memory_def,
    bound_labels_word_copy_loop, bound_labels_imm_copy_to_memory,
    bound_labels_copy_memory, bound_labels_store_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC, CASE_TAC])
QED

Theorem bound_labels_stmt_annassign[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (AnnAssign id ty e) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  irule bound_labels_ignore_bind >> simp[bound_labels_emit_local_alloca] >>
  rpt strip_tac >> irule bound_labels_bind >>
  simp[cj 1 bound_labels_expr_mutual] >> rpt strip_tac >>
  irule bound_labels_bind >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule bound_labels_bind >>
      simp[comp_return_def] >> rpt strip_tac >>
      Cases_on `FLOOKUP ce.ce_vars id` >> simp[bound_labels_emit_void] >>
      rename1 `SOME vl` >> Cases_on `vl` >> simp[bound_labels_emit_void] >>
      IF_CASES_TAC >> simp[bound_labels_emit_void, bound_labels_assign_value]) >>
  simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  simp[comp_return_def, bound_labels_unwrap_value]
QED

Theorem bound_labels_stmt_assign[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Assign (BaseTarget bt) e) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cj 1 bound_labels_expr_mutual,
    bound_labels_unwrap_value, bound_labels_emit_void,
    bound_labels_assign_value, bound_labels_store_at_loc, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC, CASE_TAC]) >>
  irule bound_labels_get_target_ptr >> simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_stmt_augassign[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (AugAssign ty bt bop e) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op, bound_labels_emit_void,
    bound_labels_binop, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac, CASE_TAC]) >>
  FIRST [irule bound_labels_get_target_ptr, irule bound_labels_lower_value] >>
  simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_stmt_assert[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Assert e reason) s))))
Proof
  strip_tac >> Cases_on `reason` >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_new_block,
    bound_labels_reason_message, bound_labels_revert_with_reason, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac]) >>
  irule bound_labels_lower_value >> simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_stmt_log[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Log id args) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt CASE_TAC >> simp[bound_labels_emit_inst] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_log_eval_all,
    bound_labels_log_topic_ops, bound_labels_alloc_buffer,
    bound_labels_log_store_data, bound_labels_abi_encode,
    bound_labels_emit_inst, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem bound_labels_stmt_raise[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Raise reason) s))))
Proof
  strip_tac >> Cases_on `reason` >>
  simp[compile_stmt_def, bound_labels_emit_inst]
  >- (irule bound_labels_bind >>
      simp[bound_labels_reason_message, bound_labels_revert_with_reason]) >>
  irule bound_labels_ignore_bind >> simp[bound_labels_emit_inst, comp_return_def]
QED

Theorem bound_labels_stmt_return_none[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Return NONE) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst,
    bound_labels_emit_op, bound_labels_nonreentrant_unlock,
    bound_labels_return_unlock, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC, CASE_TAC,
    pairarg_tac])
QED

Theorem bound_labels_stmt_return_some[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Return (SOME e)) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >> irule bound_labels_bind >> conj_tac
  >- (rpt strip_tac >> simp[] >>
      Cases_on `ce.ce_return_pc` >> simp[] >>
      TRY (rename1 `SOME vl` >> Cases_on `vl` >> simp[]) >>
      rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_op,
        bound_labels_internal_return_from_env, bound_labels_external_return,
        bound_labels_alloc_buffer, bound_labels_memory_typed,
        bound_labels_return_unlock, bound_labels_nonreentrant_unlock,
        comp_return_def]),
        gen_tac, strip_tac, irule bound_labels_bind,
        irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC])) >>
  simp[] >> rpt strip_tac >> irule bound_labels_lower_value >>
  simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_stmt_append[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Append target e) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_dynarray_append,
    bound_labels_alloc_buffer, bound_labels_store_memory, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_bind,
    irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  irule bound_labels_lower_value >> simp[bound_labels_expr_mutual]
QED

Theorem bound_labels_stmt_tuple_assign[local]:
  (!l. compiler_label l ==> P l) /\
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
  EVERY P (MAP (\bb. bb.bb_label) (all_blocks
    (SND (compile_stmt ce lc rt (Assign (TupleTarget targets) e) s))))
Proof
  strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[cj 1 bound_labels_expr_mutual,
    bound_labels_unwrap_value, bound_labels_tuple_unpack]),
    gen_tac, strip_tac, irule bound_labels_bind, conj_tac])
QED

Theorem bound_labels_stmt_mutual:
  (!l. compiler_label l ==> P l) ==>
  (!ce lc ty stmt s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_stmt ce lc ty stmt s))))) /\
  (!ce lc ty stmts s. EVERY P (MAP (\bb. bb.bb_label) (all_blocks s)) ==>
    EVERY P (MAP (\bb. bb.bb_label) (all_blocks
      (SND (compile_stmts ce lc ty stmts s)))))
Proof
  strip_tac >> ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >>
  simp[bound_labels_stmt_annassign, bound_labels_stmt_assign,
    bound_labels_stmt_augassign, bound_labels_stmt_assert,
    bound_labels_stmt_log, bound_labels_stmt_raise,
    bound_labels_stmt_return_none, bound_labels_stmt_return_some,
    bound_labels_stmt_append, bound_labels_stmt_tuple_assign] >>
  rpt gen_tac
  >~ [`compile_stmt ce lc ty (If cond tb eb)`] >- suspend "if"
  >~ [`compile_stmt ce lc ty (For id fty (Range start_e end_e) bound stmts)`] >- suspend "range"
  >~ [`compile_stmt ce lc ty (For id fty (Array arr_e) bound stmts)`] >- suspend "iter"
  >~ [`compile_stmts ce lc ty (h::t)`] >- suspend "cons"
  >> rpt strip_tac >> simp[compile_stmt_def, comp_return_def,
       bound_labels_emit_inst] >>
  FIRST [irule bound_labels_ignore_bind, irule bound_labels_bind] >>
  simp[cj 1 bound_labels_expr_mutual, bound_labels_emit_inst, comp_return_def]
QED

Resume bound_labels_stmt_mutual[if]:
  rpt strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_new_block,
    bound_labels_jmp_if_not_terminated, cj 2 bound_labels_primitives,
    comp_return_def]), gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac, IF_CASES_TAC]) >>
  irule bound_labels_lower_value >> simp[bound_labels_expr_mutual]
QED

Resume bound_labels_stmt_mutual[cons]:
  strip_tac >> gen_tac >> strip_tac >> simp[compile_stmt_def] >>
  irule bound_labels_bind >> conj_tac
  >- (rpt strip_tac >> simp[] >> IF_CASES_TAC >> simp[comp_return_def] >>
      irule bound_labels_bind >> simp[bound_labels_declare_stmt_local] >>
      rpt strip_tac >> simp[] >> irule bound_labels_ignore_bind >> simp[] >>
      metis_tac[]) >>
  simp[cj 2 bound_labels_primitives]
QED

Resume bound_labels_stmt_mutual[range]:
  rpt strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_new_block,
    bound_labels_emit_op, bound_labels_emit_void, bound_labels_declare_local,
    bound_labels_emit_local_alloca, bound_labels_jmp_if_not_terminated,
    cj 4 bound_labels_primitives, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac]) >>
  FIRST [
    (irule bound_labels_lower_value >> simp[bound_labels_expr_mutual]),
    (rename1 `FLOOKUP ce'.ce_vars _` >>
      Cases_on `FLOOKUP ce'.ce_vars id` >> simp[bound_labels_emit_void] >>
      rename1 `SOME vl` >> Cases_on `vl` >> simp[bound_labels_emit_void]),
    (Cases_on `start_e` >> simp[bound_labels_range_bound_checks,
       bound_labels_emit_op, comp_return_def] >>
      Cases_on `end_e` >> simp[bound_labels_range_bound_checks,
       bound_labels_emit_op, comp_return_def] >>
      qmatch_goalsub_rename_tac `literal_CASE lit _ _ _ _ _` >>
      Cases_on `lit` >> simp[bound_labels_range_bound_checks,
       bound_labels_emit_op, comp_return_def] >>
      qmatch_goalsub_rename_tac `literal_CASE lit2 _ _ _ _ _` >>
      Cases_on `lit2` >> simp[bound_labels_range_bound_checks,
       bound_labels_emit_op, comp_return_def]) ]
QED

Resume bound_labels_stmt_mutual[iter]:
  rpt strip_tac >> simp[compile_stmt_def] >>
  rpt (FIRST [CHANGED_TAC (simp[bound_labels_emit_inst, bound_labels_new_block,
    bound_labels_emit_op, bound_labels_emit_void, bound_labels_declare_local,
    bound_labels_emit_local_alloca, bound_labels_jmp_if_not_terminated,
    bound_labels_ptr_load, cj 4 bound_labels_primitives,
    cj 1 bound_labels_expr_mutual, comp_return_def]),
    gen_tac, strip_tac, irule bound_labels_fresh_label_bind,
    irule bound_labels_bind, irule bound_labels_ignore_bind, conj_tac,
    IF_CASES_TAC]) >>
  rename1 `FLOOKUP ce'.ce_vars _` >>
  Cases_on `FLOOKUP ce'.ce_vars id` >> simp[bound_labels_emit_void] >>
  rename1 `SOME vl` >> Cases_on `vl` >>
  simp[bound_labels_emit_void, bound_labels_iter_elem_copy]
QED

Finalise bound_labels_stmt_mutual

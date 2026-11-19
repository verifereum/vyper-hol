(* Operand exclusion for checked arithmetic, comparison and membership. *)
Theory runtimeLabelBuiltinArithmetic
Ancestors
  runtimeLabelBuiltinCore runtimeLabelBuiltinSystem
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_clamp_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (K T) (compile_clamp v ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_clamp_def, LET_THM] >>
  pairarg_tac >> BETA_TAC >> Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

Theorem rb_clamp_and_return_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (clamp_and_return v ty)
Proof
  strip_tac >> pure_rewrite_tac[clamp_and_return_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_clamp_for, rb_step_return_for]
QED

Theorem rb_compile_clamp_basetype_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, rb_step_return_for] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, rb_step_return_for] >> strip_tac
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return_for, rb_step_return_for])
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return_for, rb_step_return_for])
  >- (rename1 `BytesT len` >> Cases_on `len` >>
      simp[compile_clamp_basetype_def, rb_step_return_for] >>
      rename1 `m < 32` >> Cases_on `m < 32` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_safe_add_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_add x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_add_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return_for] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_safe_sub_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_sub x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_sub_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return_for] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_mul_overflow_check_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y /\ (rb_operand_ok_for source_checks) res ==>
  (rb_step_for source_checks) (K T) (compile_mul_overflow_check x y res signed bits)
Proof
  strip_tac >> pure_rewrite_tac[compile_mul_overflow_check_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `signed /\ bits = 256` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]) >>
  simp[rb_emit_void_for]
QED

Theorem rb_compile_safe_mul_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_mul x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mul_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `type_bits ty > 128` >>
      simp[rb_compile_mul_overflow_check_for, rb_step_return_for]) >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `is_decimal_type ty` >> simp[rb_emit_op_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >> Cases_on `type_bits ty < 256 \/ is_decimal_type ty` >>
  simp[rb_clamp_and_return_for, rb_step_return_for]
QED

Theorem rb_compile_safe_div_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_div x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_div_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty = 256` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]) >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return_for, rb_step_return_for]
QED

Theorem rb_compile_safe_decimal_div_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_decimal_div x y divisor ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_decimal_div_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_clamp_and_return_for]
QED

Theorem rb_compile_safe_mod_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_mod x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mod_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op_for]
QED

Theorem rb_compile_safe_pow_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_safe_pow x y ty bl el)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_pow_def, LET_THM] >> BETA_TAC >>
  Cases_on `bl` >> simp[]
  >- suspend "exponent" >>
  rename1 `bi = -1` >> Cases_on `bi = -1 \/ bi = 0 \/ bi = 1` >> simp[LET_THM]
  >- (irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac
      >- (Cases_on `is_signed_type ty` >> simp[rb_step_return_for] >>
          irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]) >>
      gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]
QED

Resume rb_compile_safe_pow_for[exponent]:
  Cases_on `el` >> simp[]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_compile_clamp_for, rb_step_return_for]) >>
  rename1 `Num ei = 1` >> Cases_on `ei = 0 \/ Num ei = 1` >> simp[LET_THM]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]) >>
  Cases_on `is_signed_type ty` >> simp[LET_THM]
  >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]
QED

Finalise rb_compile_safe_pow_for

Theorem rb_wrap_truncate_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (wrap_truncate v ty)
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, rb_emit_op_for, rb_step_return_for]
QED

Theorem rb_compile_compare_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_compare op x y ty)
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, rb_emit_op_for, LET_THM]
  >> FIRST_PROVE
     [irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for],
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for, rb_step_return_for]]
QED

Theorem rb_compile_binop_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >>
  simp[compile_binop_def, rb_compile_safe_add_for, rb_compile_safe_sub_for,
       rb_compile_safe_mul_for, rb_compile_safe_mod_for, rb_compile_safe_pow_for,
       rb_compile_compare_for, rb_emit_op_for, LET_THM]
  >>~- ([`if is_decimal_type ty then _ else _`],
        Cases_on `is_decimal_type ty` >> simp[rb_compile_safe_decimal_div_for, rb_compile_safe_div_for])
  >>~- ([`if is_signed_type ty then emit_op _ _ else _`],
        Cases_on `is_signed_type ty` >> simp[rb_emit_op_for])
  >>~- ([`comp_bind (emit_op _ _) (\res. wrap_truncate res ty)`],
        irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_wrap_truncate_for])
  >>~- ([`comp_ignore_bind (emit_inst _ _ _) _`],
        irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_inst_for, rb_step_return_for])
  >>~- ([`(rb_step_for source_checks) (rb_operand_ok_for source_checks) (comp_bind (emit_op _ _) (\v. comp_bind _ _))`],
        irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
        irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for])
  >>~- ([`(rb_step_for source_checks) (rb_operand_ok_for source_checks) (comp_bind (emit_op _ _) (\v. emit_op _ _))`],
        irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for])
  >>~- ([`(rb_step_for source_checks) (rb_operand_ok_for source_checks) (comp_bind (if is_uint256 ty then _ else _) _)`],
        irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
        reverse conj_tac >- (Cases_on `is_uint256 ty` >> simp[rb_emit_op_for]) >>
        simp[rb_compile_select_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_bind_emit_op_for, rb_emit_op_for]
QED

Theorem rb_compile_bytestring_hash_for:
  (rb_operand_ok_for source_checks) p ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_bytestring_hash p)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_hash_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Theorem rb_emit_membership_eqs_for:
  !elems needle. EVERY (rb_operand_ok_for source_checks) elems /\ (rb_operand_ok_for source_checks) needle ==>
  (rb_step_for source_checks) (EVERY (rb_operand_ok_for source_checks)) (emit_membership_eqs needle elems)
Proof
  Induct >> simp[emit_membership_eqs_def, rb_step_return_for] >> rpt strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[] >>
  simp[rb_step_return_for]
QED

Theorem rb_fold_membership_or_for:
  !cs acc. EVERY (rb_operand_ok_for source_checks) cs /\ (rb_operand_ok_for source_checks) acc ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (fold_membership_or acc cs)
Proof
  Induct >> simp[fold_membership_or_def, rb_step_return_for] >> rpt strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[]
QED

Theorem rb_fold_membership_and_for:
  !cs acc. EVERY (rb_operand_ok_for source_checks) cs /\ (rb_operand_ok_for source_checks) acc ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (fold_membership_and acc cs)
Proof
  Induct >> simp[fold_membership_and_def, rb_step_return_for] >> rpt strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[]
QED

Theorem rb_compile_list_membership_in_for:
  EVERY (rb_operand_ok_for source_checks) elems /\ (rb_operand_ok_for source_checks) needle ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_list_membership_in needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_in_def] >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs_for] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return_for, rb_fold_membership_or_for]
QED

Theorem rb_compile_list_membership_notin_for:
  EVERY (rb_operand_ok_for source_checks) elems /\ (rb_operand_ok_for source_checks) needle ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_list_membership_notin needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_notin_def] >>
  irule rb_step_bind_for >> qexists_tac `EVERY (rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs_for] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return_for] >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_fold_membership_and_for]
QED

Theorem rb_compile_mapping_subscript_for:
  (rb_operand_ok_for source_checks) slot /\ (rb_operand_ok_for source_checks) key ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_mapping_subscript slot key)
Proof
  strip_tac >> pure_rewrite_tac[compile_mapping_subscript_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]
QED

Theorem rb_compile_keccak256_key_for:
  (rb_operand_ok_for source_checks) key ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_keccak256_key key bytes32)
Proof
  strip_tac >> Cases_on `bytes32` >>
  simp[compile_keccak256_key_def]
  >- (irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
      gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]) >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

Theorem rb_compile_array_membership_loop_for:
  (rb_operand_ok_for source_checks) needle /\ (rb_operand_ok_for source_checks) arr /\ (rb_operand_ok_for source_checks) len /\
  (!p. (rb_operand_ok_for source_checks) p ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (loader p)) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_array_membership_loop needle arr len sz off loader bound is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_array_membership_loop_def] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `bound` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_inst_for]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  suspend "body"
QED

Resume rb_compile_array_membership_loop_for[body]:
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `off > 0` >> simp[rb_emit_op_for, rb_step_return_for]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  Cases_on `is_in` >> simp[rb_step_return_for, rb_emit_op_for]
QED

Finalise rb_compile_array_membership_loop_for

Theorem rb_compile_var_array_membership_for:
  (rb_env_ok_for source_checks) ce /\ (rb_operand_ok_for source_checks) needle /\ (rb_value_ok_for source_checks) vv ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_var_array_membership ce needle vv ty is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_var_array_membership_def, LET_THM] >>
  BETA_TAC >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `(case ty of ArrayT _ (Dynamic _) => T | _ => F)` >>
      simp[]
      >- (irule rb_compile_ptr_load_for >> simp[rb_value_operand_for] >>
          gvs[rb_env_ok_for_def]) >>
      Cases_on `ty` >> simp[rb_step_return_for] >>
      rename1 `ArrayT et bd` >> Cases_on `bd` >> simp[rb_step_return_for]) >>
  gen_tac >> strip_tac >> irule rb_compile_array_membership_loop_for >>
  simp[rb_value_operand_for] >> gen_tac >> strip_tac >>
  irule rb_compile_ptr_load_for >> gvs[rb_env_ok_for_def]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_clamp:
  rb_operand_ok v ==> rb_step (K T) (compile_clamp v ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_clamp_for))
QED

Theorem rb_clamp_and_return:
  rb_operand_ok v ==> rb_step rb_operand_ok (clamp_and_return v ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_clamp_and_return_for))
QED

Theorem rb_compile_clamp_basetype:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_clamp_basetype v ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_clamp_basetype_for))
QED

Theorem rb_compile_safe_add:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_add x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_add_for))
QED

Theorem rb_compile_safe_sub:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_sub x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_sub_for))
QED

Theorem rb_compile_mul_overflow_check:
  rb_operand_ok x /\ rb_operand_ok y /\ rb_operand_ok res ==>
  rb_step (K T) (compile_mul_overflow_check x y res signed bits)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_mul_overflow_check_for))
QED

Theorem rb_compile_safe_mul:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mul x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_mul_for))
QED

Theorem rb_compile_safe_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_div x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_div_for))
QED

Theorem rb_compile_safe_decimal_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_decimal_div x y divisor ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_decimal_div_for))
QED

Theorem rb_compile_safe_mod:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mod x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_mod_for))
QED

Theorem rb_compile_safe_pow:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_pow x y ty bl el)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_safe_pow_for))
QED

Theorem rb_wrap_truncate:
  rb_operand_ok v ==> rb_step rb_operand_ok (wrap_truncate v ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_wrap_truncate_for))
QED

Theorem rb_compile_compare:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_compare op x y ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_compare_for))
QED

Theorem rb_compile_binop:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_binop op x y ty bl el)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_binop_for))
QED

Theorem rb_compile_bytestring_hash:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_bytestring_hash p)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_bytestring_hash_for))
QED

Theorem rb_emit_membership_eqs:
  !elems needle. EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step (EVERY rb_operand_ok) (emit_membership_eqs needle elems)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_membership_eqs_for))
QED

Theorem rb_fold_membership_or:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_or acc cs)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fold_membership_or_for))
QED

Theorem rb_fold_membership_and:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_and acc cs)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fold_membership_and_for))
QED

Theorem rb_compile_list_membership_in:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_in needle elems)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_list_membership_in_for))
QED

Theorem rb_compile_list_membership_notin:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_notin needle elems)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_list_membership_notin_for))
QED

Theorem rb_compile_mapping_subscript:
  rb_operand_ok slot /\ rb_operand_ok key ==>
  rb_step rb_operand_ok (compile_mapping_subscript slot key)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_mapping_subscript_for))
QED

Theorem rb_compile_keccak256_key:
  rb_operand_ok key ==> rb_step rb_operand_ok (compile_keccak256_key key bytes32)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_keccak256_key_for))
QED

Theorem rb_compile_array_membership_loop:
  rb_operand_ok needle /\ rb_operand_ok arr /\ rb_operand_ok len /\
  (!p. rb_operand_ok p ==> rb_step rb_operand_ok (loader p)) ==>
  rb_step rb_operand_ok
    (compile_array_membership_loop needle arr len sz off loader bound is_in)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_array_membership_loop_for))
QED

Theorem rb_compile_var_array_membership:
  rb_env_ok ce /\ rb_operand_ok needle /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_var_array_membership ce needle vv ty is_in)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_operand_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_var_array_membership_for))
QED

(* Operand exclusion for checked arithmetic, comparison and membership. *)
Theory runtimeLabelBuiltinArithmetic
Ancestors
  runtimeLabelBuiltinCore runtimeLabelBuiltinSystem
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_clamp:
  rb_operand_ok v ==> rb_step (K T) (compile_clamp v ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_clamp_def, LET_THM] >>
  pairarg_tac >> BETA_TAC >> Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_void]
QED

Theorem rb_clamp_and_return:
  rb_operand_ok v ==> rb_step rb_operand_ok (clamp_and_return v ty)
Proof
  strip_tac >> pure_rewrite_tac[clamp_and_return_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_clamp, rb_step_return]
QED

Theorem rb_compile_clamp_basetype:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def, rb_step_return] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_clamp_basetype_def, rb_step_return] >> strip_tac
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return, rb_step_return])
  >- (Cases_on `n < 256` >> simp[rb_clamp_and_return, rb_step_return])
  >- (rename1 `BytesT len` >> Cases_on `len` >>
      simp[compile_clamp_basetype_def, rb_step_return] >>
      rename1 `m < 32` >> Cases_on `m < 32` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_safe_add:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_add x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_add_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_safe_sub:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_sub x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_sub_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return] >>
  Cases_on `is_signed_type ty` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_mul_overflow_check:
  rb_operand_ok x /\ rb_operand_ok y /\ rb_operand_ok res ==>
  rb_step (K T) (compile_mul_overflow_check x y res signed bits)
Proof
  strip_tac >> pure_rewrite_tac[compile_mul_overflow_check_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `signed /\ bits = 256` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]) >>
  simp[rb_emit_void]
QED

Theorem rb_compile_safe_mul:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mul x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mul_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `type_bits ty > 128` >>
      simp[rb_compile_mul_overflow_check, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `is_decimal_type ty` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >> Cases_on `type_bits ty < 256 \/ is_decimal_type ty` >>
  simp[rb_clamp_and_return, rb_step_return]
QED

Theorem rb_compile_safe_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_div x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_div_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  Cases_on `type_bits ty = 256` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  Cases_on `type_bits ty < 256` >> simp[rb_clamp_and_return, rb_step_return]
QED

Theorem rb_compile_safe_decimal_div:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_decimal_div x y divisor ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_decimal_div_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_clamp_and_return]
QED

Theorem rb_compile_safe_mod:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_mod x y ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_mod_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  Cases_on `is_signed_type ty` >> simp[rb_emit_op]
QED

Theorem rb_compile_safe_pow:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_safe_pow x y ty bl el)
Proof
  strip_tac >> pure_rewrite_tac[compile_safe_pow_def, LET_THM] >> BETA_TAC >>
  Cases_on `bl` >> simp[]
  >- suspend "exponent" >>
  rename1 `bi = -1` >> Cases_on `bi = -1 \/ bi = 0 \/ bi = 1` >> simp[LET_THM]
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac
      >- (Cases_on `is_signed_type ty` >> simp[rb_step_return] >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]) >>
      gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED

Resume rb_compile_safe_pow[exponent]:
  Cases_on `el` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_clamp, rb_step_return]) >>
  rename1 `Num ei = 1` >> Cases_on `ei = 0 \/ Num ei = 1` >> simp[LET_THM]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]) >>
  Cases_on `is_signed_type ty` >> simp[LET_THM]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED

Finalise rb_compile_safe_pow

Theorem rb_wrap_truncate:
  rb_operand_ok v ==> rb_step rb_operand_ok (wrap_truncate v ty)
Proof
  strip_tac >> Cases_on `type_bits ty < 256` >> Cases_on `is_signed_type ty` >>
  simp[wrap_truncate_def, rb_emit_op, rb_step_return]
QED

Theorem rb_compile_compare:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_compare op x y ty)
Proof
  strip_tac >> Cases_on `op` >> Cases_on `is_uint256 ty` >>
  simp[compile_compare_def, rb_emit_op, LET_THM]
  >> FIRST_PROVE
     [irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op],
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]]
QED

Theorem rb_compile_binop:
  rb_operand_ok x /\ rb_operand_ok y ==>
  rb_step rb_operand_ok (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >>
  simp[compile_binop_def, rb_compile_safe_add, rb_compile_safe_sub,
       rb_compile_safe_mul, rb_compile_safe_mod, rb_compile_safe_pow,
       rb_compile_compare, rb_emit_op, LET_THM]
  >>~- ([`if is_decimal_type ty then _ else _`],
        Cases_on `is_decimal_type ty` >> simp[rb_compile_safe_decimal_div, rb_compile_safe_div])
  >>~- ([`if is_signed_type ty then emit_op _ _ else _`],
        Cases_on `is_signed_type ty` >> simp[rb_emit_op])
  >>~- ([`comp_bind (emit_op _ _) (\res. wrap_truncate res ty)`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_wrap_truncate])
  >>~- ([`comp_ignore_bind (emit_inst _ _ _) _`],
        irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return])
  >>~- ([`rb_step rb_operand_ok (comp_bind (emit_op _ _) (\v. comp_bind _ _))`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >>~- ([`rb_step rb_operand_ok (comp_bind (emit_op _ _) (\v. emit_op _ _))`],
        irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op])
  >>~- ([`rb_step rb_operand_ok (comp_bind (if is_uint256 ty then _ else _) _)`],
        irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
        reverse conj_tac >- (Cases_on `is_uint256 ty` >> simp[rb_emit_op]) >>
        simp[rb_compile_select]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_bind_emit_op, rb_emit_op]
QED

Theorem rb_compile_bytestring_hash:
  rb_operand_ok p ==> rb_step rb_operand_ok (compile_bytestring_hash p)
Proof
  strip_tac >> pure_rewrite_tac[compile_bytestring_hash_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_emit_membership_eqs:
  !elems needle. EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step (EVERY rb_operand_ok) (emit_membership_eqs needle elems)
Proof
  Induct >> simp[emit_membership_eqs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >>
  simp[rb_step_return]
QED

Theorem rb_fold_membership_or:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_or acc cs)
Proof
  Induct >> simp[fold_membership_or_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[]
QED

Theorem rb_fold_membership_and:
  !cs acc. EVERY rb_operand_ok cs /\ rb_operand_ok acc ==>
  rb_step rb_operand_ok (fold_membership_and acc cs)
Proof
  Induct >> simp[fold_membership_and_def, rb_step_return] >> rpt strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[]
QED

Theorem rb_compile_list_membership_in:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_in needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_in_def] >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return, rb_fold_membership_or]
QED

Theorem rb_compile_list_membership_notin:
  EVERY rb_operand_ok elems /\ rb_operand_ok needle ==>
  rb_step rb_operand_ok (compile_list_membership_notin needle elems)
Proof
  strip_tac >> pure_rewrite_tac[compile_list_membership_notin_def] >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_emit_membership_eqs] >>
  gen_tac >> Cases_on `x` >> simp[rb_step_return] >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_fold_membership_and]
QED

Theorem rb_compile_mapping_subscript:
  rb_operand_ok slot /\ rb_operand_ok key ==>
  rb_step rb_operand_ok (compile_mapping_subscript slot key)
Proof
  strip_tac >> pure_rewrite_tac[compile_mapping_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]
QED

Theorem rb_compile_keccak256_key:
  rb_operand_ok key ==> rb_step rb_operand_ok (compile_keccak256_key key bytes32)
Proof
  strip_tac >> Cases_on `bytes32` >>
  simp[compile_keccak256_key_def]
  >- (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_emit_op]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_op]
QED

Theorem rb_compile_array_membership_loop:
  rb_operand_ok needle /\ rb_operand_ok arr /\ rb_operand_ok len /\
  (!p. rb_operand_ok p ==> rb_step rb_operand_ok (loader p)) ==>
  rb_step rb_operand_ok
    (compile_array_membership_loop needle arr len sz off loader bound is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_array_membership_loop_def] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `bound` >> simp[rb_step_return] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  suspend "body"
QED

Resume rb_compile_array_membership_loop[body]:
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `off > 0` >> simp[rb_emit_op, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_inst] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_new_block] >>
  Cases_on `is_in` >> simp[rb_step_return, rb_emit_op]
QED

Finalise rb_compile_array_membership_loop

Theorem rb_compile_var_array_membership:
  rb_env_ok ce /\ rb_operand_ok needle /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_var_array_membership ce needle vv ty is_in)
Proof
  strip_tac >> pure_rewrite_tac[compile_var_array_membership_def, LET_THM] >>
  BETA_TAC >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `(case ty of ArrayT _ (Dynamic _) => T | _ => F)` >>
      simp[]
      >- (irule rb_compile_ptr_load >> simp[rb_value_operand] >>
          gvs[rb_env_ok_def]) >>
      Cases_on `ty` >> simp[rb_step_return] >>
      rename1 `ArrayT et bd` >> Cases_on `bd` >> simp[rb_step_return]) >>
  gen_tac >> strip_tac >> irule rb_compile_array_membership_loop >>
  simp[rb_value_operand] >> gen_tac >> strip_tac >>
  irule rb_compile_ptr_load >> gvs[rb_env_ok_def]
QED

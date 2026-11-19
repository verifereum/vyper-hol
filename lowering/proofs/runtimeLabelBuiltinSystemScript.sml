(* Operand exclusion for conversion, precompile, ABI and creation primitives. *)
Theory runtimeLabelBuiltinSystem
Ancestors
  runtimeLabelBuiltinCore
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_uint2str_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_uint2str v digits nbytes)
Proof
  strip_tac >> pure_rewrite_tac[compile_uint2str_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule rb_bind_fresh_var_for >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  suspend "body"
QED

Resume rb_compile_uint2str_for[body]:
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED

Finalise rb_compile_uint2str_for

Theorem rb_compile_ecrecover_for:
  (rb_operand_ok_for source_checks) h /\ (rb_operand_ok_for source_checks) v /\ (rb_operand_ok_for source_checks) r /\ (rb_operand_ok_for source_checks) s ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ecrecover h v r s)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecrecover_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]
QED

Theorem rb_compile_ecadd_for:
  (rb_operand_ok_for source_checks) x1 /\ (rb_operand_ok_for source_checks) y1 /\ (rb_operand_ok_for source_checks) x2 /\ (rb_operand_ok_for source_checks) y2 ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ecadd x1 y1 x2 y2)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecadd_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_ecmul_for:
  (rb_operand_ok_for source_checks) x /\ (rb_operand_ok_for source_checks) y /\ (rb_operand_ok_for source_checks) scalar ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ecmul x y scalar)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecmul_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_ecadd_points_for:
  (rb_operand_ok_for source_checks) p1 /\ (rb_operand_ok_for source_checks) p2 ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ecadd_points p1 p2)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecadd_points_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_ecmul_point_for:
  (rb_operand_ok_for source_checks) p /\ (rb_operand_ok_for source_checks) scalar ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ecmul_point p scalar)
Proof
  strip_tac >> pure_rewrite_tac[compile_ecmul_point_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_blockhash_for:
  (rb_operand_ok_for source_checks) n ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_blockhash n)
Proof
  strip_tac >> pure_rewrite_tac[compile_blockhash_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_emit_op_for]
QED

Theorem rb_compile_blobhash_for:
  (rb_operand_ok_for source_checks) n ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_blobhash n)
Proof
  simp[compile_blobhash_def, rb_emit_op_for]
QED

Theorem rb_compile_floor_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_floor v divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_floor_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select_for] >>
  simp[rb_emit_op_for]
QED

Theorem rb_compile_ceil_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ceil v divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_ceil_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_select_for] >>
  simp[rb_emit_op_for]
QED

Theorem rb_compile_as_wei_value_int_for:
  (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_as_wei_value_int v scale signed)
Proof
  strip_tac >> pure_rewrite_tac[compile_as_wei_value_int_def] >>
  Cases_on `scale = 1` >> simp[rb_step_return_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `signed` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_as_wei_value_decimal_for:
  (rb_operand_ok_for source_checks) v ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_as_wei_value_decimal v scale divisor)
Proof
  strip_tac >> pure_rewrite_tac[compile_as_wei_value_decimal_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  Cases_on `scale = 1` >> simp[rb_emit_op_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_op_for]
QED

(* The encoder antecedent is conjunct 2 of runtimeLabelABI$rb_abi_encode_for. *)
Theorem rb_lower_abi_encode_for:
  (!dst src info. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
     (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_abi_encode_to_buf dst src info)) /\
  (rb_operand_ok_for source_checks) src_op ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
Proof
  strip_tac >> pure_rewrite_tac[lower_abi_encode_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `method_id_opt` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]) >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> reverse conj_tac
  >- simp[rb_step_return_for] >>
  Cases_on `(case method_id_opt of SOME _ => 4 | NONE => 0) > 0` >>
  simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]
QED

(* The decoder antecedent is conjunct 1 of runtimeLabelABI$rb_abi_decode_for. *)
Theorem rb_lower_abi_decode_for:
  (!dst src opc bop hi info.
     (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src /\ (rb_operand_ok_for source_checks) bop /\ (rb_operand_ok_for source_checks) hi /\
     (opc = CODECOPY ==> ~SND source_checks) ==>
     (rb_step_for source_checks) (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (rb_operand_ok_for source_checks) data_op ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (lower_abi_decode data_op dec_info min_size max_size out_size)
Proof
  strip_tac >> pure_rewrite_tac[lower_abi_decode_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `min_size = max_size` >> simp[]
      >- (irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]) >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_emit_void_for]) >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_step_return_for]
QED

Theorem rb_compile_check_create_result_for:
  (rb_operand_ok_for source_checks) result ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_check_create_result result revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_check_create_result_def] >>
  Cases_on `revert_on_failure` >> simp[rb_step_return_for] >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule rb_bind_fresh_label_for >> BETA_TAC >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_new_block_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_inst_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_new_block_for, rb_step_return_for]
QED

Theorem rb_compile_create_dispatch_for:
  (rb_operand_ok_for source_checks) code_ptr /\ (rb_operand_ok_for source_checks) code_len /\ (rb_operand_ok_for source_checks) value_op /\
  (case salt_opt of NONE => T | SOME salt => (rb_operand_ok_for source_checks) salt) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_create_dispatch code_ptr code_len value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_dispatch_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op_for]) >>
  simp[rb_compile_check_create_result_for]
QED

Theorem rb_compile_create_proxy_buf_for:
  (rb_operand_ok_for source_checks) target ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_create_proxy_buf target)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_proxy_buf_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_buffer_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer_for] >>
  gen_tac >> simp[rb_buffer_ok_for_def] >> strip_tac >>
  irule rb_bind_return_for >> BETA_TAC >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_create_proxy_for:
  (rb_operand_ok_for source_checks) target /\ (rb_operand_ok_for source_checks) value_op /\
  (case salt_opt of NONE => T | SOME salt => (rb_operand_ok_for source_checks) salt) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_create_proxy target value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_proxy_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_proxy_buf_for] >>
  simp[rb_compile_create_dispatch_for]
QED

Theorem rb_compile_create_copy_for:
  (rb_operand_ok_for source_checks) target /\ (rb_operand_ok_for source_checks) value_op /\
  (case salt_opt of NONE => T | SOME salt => (rb_operand_ok_for source_checks) salt) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_create_copy target value_op salt_opt revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_copy_def, LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic_for] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac >- simp[rb_emit_void_for] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op_for]) >>
  simp[rb_compile_check_create_result_for]
QED

Theorem rb_compile_create_blueprint_check_for:
  (rb_operand_ok_for source_checks) target /\ (rb_operand_ok_for source_checks) offset ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_create_blueprint_check is_lit target offset)
Proof
  Cases_on `is_lit` >> strip_tac >>
  pure_rewrite_tac[compile_create_blueprint_check_def, COND_CLAUSES] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> simp[rb_emit_void_for, rb_step_return_for]
QED

Theorem rb_compile_create_blueprint_append_for:
  (rb_operand_ok_for source_checks) target /\ (rb_operand_ok_for source_checks) value_op /\
  (case salt_opt of NONE => T | SOME salt => (rb_operand_ok_for source_checks) salt) /\
  (rb_operand_ok_for source_checks) offset /\ (rb_operand_ok_for source_checks) code_size /\
  (rb_operand_ok_for source_checks) args_ptr /\ (rb_operand_ok_for source_checks) args_len ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_create_blueprint_append target value_op salt_opt offset
      code_size args_ptr args_len revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_append_def] >>
  irule rb_bind_emit_op_for >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_dynamic_for] >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >>
  conj_tac >- simp[rb_emit_void_for] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind_for) >> conj_tac
  >- (Cases_on `args_len = Lit 0w` >> simp[rb_step_return_for] >>
      irule rb_bind_emit_op_for >> BETA_TAC >> simp[rb_compile_copy_memory_dynamic_for]) >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- (Cases_on `salt_opt` >> gvs[rb_emit_op_for]) >>
  simp[rb_compile_check_create_result_for]
QED

Theorem rb_compile_create_blueprint_for:
  (rb_operand_ok_for source_checks) target /\ (rb_operand_ok_for source_checks) value_op /\
  (case salt_opt of NONE => T | SOME salt => (rb_operand_ok_for source_checks) salt) /\
  (rb_operand_ok_for source_checks) offset /\
  (case args_info of NONE => T | SOME (p,n) => (rb_operand_ok_for source_checks) p /\ (rb_operand_ok_for source_checks) n) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (compile_create_blueprint is_lit target value_op salt_opt offset args_info revert_on_failure)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_blueprint_check_for] >>
  gen_tac >> strip_tac >> Cases_on `args_info` >>
  gvs[LET_THM, rb_compile_create_blueprint_append_for] >>
  PairCases_on `x'` >> gvs[rb_compile_create_blueprint_append_for]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_uint2str:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_uint2str v digits nbytes)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_uint2str_for))
QED

Theorem rb_compile_ecrecover:
  rb_operand_ok h /\ rb_operand_ok v /\ rb_operand_ok r /\ rb_operand_ok s ==>
  rb_step rb_operand_ok (compile_ecrecover h v r s)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ecrecover_for))
QED

Theorem rb_compile_ecadd:
  rb_operand_ok x1 /\ rb_operand_ok y1 /\ rb_operand_ok x2 /\ rb_operand_ok y2 ==>
  rb_step rb_operand_ok (compile_ecadd x1 y1 x2 y2)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ecadd_for))
QED

Theorem rb_compile_ecmul:
  rb_operand_ok x /\ rb_operand_ok y /\ rb_operand_ok scalar ==>
  rb_step rb_operand_ok (compile_ecmul x y scalar)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ecmul_for))
QED

Theorem rb_compile_ecadd_points:
  rb_operand_ok p1 /\ rb_operand_ok p2 ==>
  rb_step rb_operand_ok (compile_ecadd_points p1 p2)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ecadd_points_for))
QED

Theorem rb_compile_ecmul_point:
  rb_operand_ok p /\ rb_operand_ok scalar ==>
  rb_step rb_operand_ok (compile_ecmul_point p scalar)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ecmul_point_for))
QED

Theorem rb_compile_blockhash:
  rb_operand_ok n ==> rb_step rb_operand_ok (compile_blockhash n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_blockhash_for))
QED

Theorem rb_compile_blobhash:
  rb_operand_ok n ==> rb_step rb_operand_ok (compile_blobhash n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_blobhash_for))
QED

Theorem rb_compile_floor:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_floor v divisor)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_floor_for))
QED

Theorem rb_compile_ceil:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_ceil v divisor)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ceil_for))
QED

Theorem rb_compile_as_wei_value_int:
  rb_operand_ok v ==> rb_step rb_operand_ok (compile_as_wei_value_int v scale signed)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_as_wei_value_int_for))
QED

Theorem rb_compile_as_wei_value_decimal:
  rb_operand_ok v ==>
  rb_step rb_operand_ok (compile_as_wei_value_decimal v scale divisor)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_as_wei_value_decimal_for))
QED

Theorem rb_lower_abi_encode:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_operand_ok src_op ==>
  rb_step rb_operand_ok (lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_lower_abi_encode_for))
QED

Theorem rb_lower_abi_decode:
  (!dst src opc bop hi info.
     rb_operand_ok dst /\ rb_operand_ok src /\ rb_operand_ok bop /\ rb_operand_ok hi ==>
     rb_step (K T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  rb_operand_ok data_op ==>
  rb_step rb_operand_ok (lower_abi_decode data_op dec_info min_size max_size out_size)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_lower_abi_decode_for))
QED

Theorem rb_compile_check_create_result:
  rb_operand_ok result ==>
  rb_step rb_operand_ok (compile_check_create_result result revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_check_create_result_for))
QED

Theorem rb_compile_create_dispatch:
  rb_operand_ok code_ptr /\ rb_operand_ok code_len /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok
    (compile_create_dispatch code_ptr code_len value_op salt_opt revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_dispatch_for))
QED

Theorem rb_compile_create_proxy_buf:
  rb_operand_ok target ==>
  rb_step rb_operand_ok (compile_create_proxy_buf target)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_proxy_buf_for))
QED

Theorem rb_compile_create_proxy:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok (compile_create_proxy target value_op salt_opt revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_proxy_for))
QED

Theorem rb_compile_create_copy:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) ==>
  rb_step rb_operand_ok (compile_create_copy target value_op salt_opt revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_copy_for))
QED

Theorem rb_compile_create_blueprint_check:
  rb_operand_ok target /\ rb_operand_ok offset ==>
  rb_step rb_operand_ok (compile_create_blueprint_check is_lit target offset)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_blueprint_check_for))
QED

Theorem rb_compile_create_blueprint_append:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) /\
  rb_operand_ok offset /\ rb_operand_ok code_size /\
  rb_operand_ok args_ptr /\ rb_operand_ok args_len ==>
  rb_step rb_operand_ok
    (compile_create_blueprint_append target value_op salt_opt offset
      code_size args_ptr args_len revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_blueprint_append_for))
QED

Theorem rb_compile_create_blueprint:
  rb_operand_ok target /\ rb_operand_ok value_op /\
  (case salt_opt of NONE => T | SOME salt => rb_operand_ok salt) /\
  rb_operand_ok offset /\
  (case args_info of NONE => T | SOME (p,n) => rb_operand_ok p /\ rb_operand_ok n) ==>
  rb_step rb_operand_ok
    (compile_create_blueprint is_lit target value_op salt_opt offset args_info revert_on_failure)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_create_blueprint_for))
QED

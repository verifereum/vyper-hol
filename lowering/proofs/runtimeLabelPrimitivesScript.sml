(* Operand exclusion for primitive allocation, pointer and bind operations. *)
Theory runtimeLabelPrimitives
Ancestors
  runtimeLabelInvariant context compileEnv emitHelper loweringShapeDefs
  venomInst list finite_map stmtLowering

Theorem rb_compile_alloc_buffer_for:
  !size. (rb_step_for source_checks) (rb_buffer_ok_for source_checks) (compile_alloc_buffer size)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >>
  simp[rb_emit_op_for, rb_step_return_for, rb_buffer_ok_for_def]
QED

Theorem rb_compile_imm_load_word_for:
  (rb_operand_ok_for source_checks) off /\
  (case imm of NONE => T | SOME op => (rb_operand_ok_for source_checks) op) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_imm_load_word ctor imm off)
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, rb_emit_op_for] >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >> simp[rb_emit_op_for]
QED

Theorem rb_compile_imm_store_word_for:
  (rb_operand_ok_for source_checks) off /\ (rb_operand_ok_for source_checks) v /\
  (case imm of NONE => T | SOME op => (rb_operand_ok_for source_checks) op) ==>
  (rb_step_for source_checks) (K T) (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def, rb_emit_void_for] >>
  strip_tac >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >>
  simp[rb_emit_op_for, rb_emit_void_for]
QED

Theorem rb_compile_ptr_load_for:
  (rb_operand_ok_for source_checks) op /\
  (case imm of NONE => T | SOME region => (rb_operand_ok_for source_checks) region) ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_ptr_load ctor imm loc op)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def, rb_compile_imm_load_word_for,
                        rb_emit_op_for]
QED

Theorem rb_compile_ptr_store_for:
  (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) v /\
  (case imm of NONE => T | SOME region => (rb_operand_ok_for source_checks) region) ==>
  (rb_step_for source_checks) (K T) (compile_ptr_store ctor imm loc dst v)
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, rb_compile_imm_store_word_for, rb_emit_void_for]
QED

Theorem rb_compile_copy_memory_for:
  !dst src n. (rb_operand_ok_for source_checks) dst /\ (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (K T) (compile_copy_memory dst src n)
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, rb_step_return_for, rb_emit_void_for]
QED

Theorem rb_compile_alloc_dynamic_for:
  !size. (rb_operand_ok_for source_checks) size ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (compile_alloc_dynamic size)
Proof
  simp[compile_alloc_dynamic_def, rb_emit_op_for]
QED

Theorem rb_vv_with_type_for:
  (rb_value_ok_for source_checks) v ==> (rb_value_ok_for source_checks) (vv_with_type ty v)
Proof
  Cases_on `v` >> simp[vv_with_type_def, rb_value_ok_for_def]
QED

Theorem rb_bind_emit_op_for:
  EVERY (rb_operand_ok_for source_checks) ops /\ source_codecopy_arity_ok source_checks opc ops /\
  (!op. (rb_operand_ok_for source_checks) op ==> (rb_step_for source_checks) Q (f op)) ==>
  (rb_step_for source_checks) Q (comp_bind (emit_op opc ops) f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >>
  simp[rb_emit_op_for]
QED

Theorem rb_bind_fresh_label_for:
  (!l. (rb_operand_ok_for source_checks) (Label l) ==> (rb_step_for source_checks) Q (f l)) ==>
  (rb_step_for source_checks) Q (comp_bind (fresh_label suffix) f)
Proof
  strip_tac >> irule rb_step_bind_for >>
  qexists_tac `\l. (rb_operand_ok_for source_checks) (Label l)` >> simp[rb_fresh_label_for]
QED

Theorem rb_bind_fresh_var_for:
  (!v. (rb_step_for source_checks) Q (f v)) ==> (rb_step_for source_checks) Q (comp_bind fresh_var f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `K T` >> simp[rb_fresh_var_for]
QED

Theorem rb_bind_new_block_for:
  (!v. (rb_step_for source_checks) Q (f v)) ==> (rb_step_for source_checks) Q (comp_bind (new_block lbl) f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `K T` >> simp[rb_new_block_for]
QED

Theorem rb_bind_return_for:
  (rb_step_for source_checks) Q (f x) ==> (rb_step_for source_checks) Q (compileEnv$comp_bind (comp_return x) f)
Proof
  simp[rb_step_for_def, comp_bind_def, comp_return_def]
QED

Theorem rb_bind_ptr_load_for:
  (rb_operand_ok_for source_checks) op /\
  (case imm of NONE => T | SOME region => (rb_operand_ok_for source_checks) region) /\
  (!v. (rb_operand_ok_for source_checks) v ==> (rb_step_for source_checks) Q (f v)) ==>
  (rb_step_for source_checks) Q (comp_bind (compile_ptr_load ctor imm loc op) f)
Proof
  strip_tac >> irule rb_step_bind_for >> qexists_tac `(rb_operand_ok_for source_checks)` >>
  simp[rb_compile_ptr_load_for]
QED

Theorem rb_bind_cond_for:
  (p ==> (rb_step_for source_checks) Q (comp_bind a f)) /\
  (~p ==> (rb_step_for source_checks) Q (comp_bind b f)) ==>
  (rb_step_for source_checks) Q (comp_bind (if p then a else b) f)
Proof
  Cases_on `p` >> simp[]
QED

Theorem rb_compile_scaled_addr_for:
  (rb_operand_ok_for source_checks) src ==>
  (rb_step_for source_checks) (rb_operand_ok_for source_checks)
    (if scale = 1 then emit_op ADD [src; Var idx]
     else comp_bind (emit_op MUL [Var idx; Lit (n2w scale)])
                    (\scaled. emit_op ADD [src; scaled]))
Proof
  strip_tac >> Cases_on `scale = 1` >> simp[rb_emit_op_for] >>
  irule rb_bind_emit_op_for >> simp[rb_emit_op_for]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_compile_alloc_buffer:
  !size. rb_step rb_buffer_ok (compile_alloc_buffer size)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_buffer_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_alloc_buffer_for))
QED

Theorem rb_compile_imm_load_word:
  rb_operand_ok off /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step rb_operand_ok (compile_imm_load_word ctor imm off)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_imm_load_word_for))
QED

Theorem rb_compile_imm_store_word:
  rb_operand_ok off /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step (K T) (compile_imm_store_word imm off v)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_imm_store_word_for))
QED

Theorem rb_compile_ptr_load:
  rb_operand_ok op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step rb_operand_ok (compile_ptr_load ctor imm loc op)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ptr_load_for))
QED

Theorem rb_compile_ptr_store:
  rb_operand_ok dst /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_ptr_store ctor imm loc dst v)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_ptr_store_for))
QED

Theorem rb_compile_copy_memory:
  !dst src n. rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step (K T) (compile_copy_memory dst src n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_copy_memory_for))
QED

Theorem rb_compile_alloc_dynamic:
  !size. rb_operand_ok size ==> rb_step rb_operand_ok (compile_alloc_dynamic size)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_alloc_dynamic_for))
QED

Theorem rb_vv_with_type:
  rb_value_ok v ==> rb_value_ok (vv_with_type ty v)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_vv_with_type_for))
QED

Theorem rb_bind_emit_op:
  EVERY rb_operand_ok ops /\
  (!op. rb_operand_ok op ==> rb_step Q (f op)) ==>
  rb_step Q (comp_bind (emit_op opc ops) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_emit_op_for))
QED

Theorem rb_bind_fresh_label:
  (!l. rb_operand_ok (Label l) ==> rb_step Q (f l)) ==>
  rb_step Q (comp_bind (fresh_label suffix) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_fresh_label_for))
QED

Theorem rb_bind_fresh_var:
  (!v. rb_step Q (f v)) ==> rb_step Q (comp_bind fresh_var f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_fresh_var_for))
QED

Theorem rb_bind_new_block:
  (!v. rb_step Q (f v)) ==> rb_step Q (comp_bind (new_block lbl) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_new_block_for))
QED

Theorem rb_bind_return:
  rb_step Q (f x) ==> rb_step Q (compileEnv$comp_bind (comp_return x) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_return_for))
QED

Theorem rb_bind_ptr_load:
  rb_operand_ok op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) /\
  (!v. rb_operand_ok v ==> rb_step Q (f v)) ==>
  rb_step Q (comp_bind (compile_ptr_load ctor imm loc op) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_ptr_load_for))
QED

Theorem rb_bind_cond:
  (p ==> rb_step Q (comp_bind a f)) /\
  (~p ==> rb_step Q (comp_bind b f)) ==>
  rb_step Q (comp_bind (if p then a else b) f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_bind_cond_for))
QED

Theorem rb_compile_scaled_addr:
  rb_operand_ok src ==>
  rb_step rb_operand_ok
    (if scale = 1 then emit_op ADD [src; Var idx]
     else comp_bind (emit_op MUL [Var idx; Lit (n2w scale)])
                    (\scaled. emit_op ADD [src; scaled]))
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_compile_scaled_addr_for))
QED

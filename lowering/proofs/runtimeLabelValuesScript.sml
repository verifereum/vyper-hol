(* Operand exclusion for the value and pointer boundary. *)
Theory runtimeLabelValues
Ancestors
  runtimeLabelInvariant context compileEnv emitHelper loweringShapeDefs
  venomInst list finite_map

Theorem rb_compile_alloc_buffer:
  !size. rb_step rb_buffer_ok (compile_alloc_buffer size)
Proof
  gen_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_emit_op, rb_step_return, rb_buffer_ok_def]
QED

Theorem rb_compile_imm_load_word:
  rb_operand_ok off /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step rb_operand_ok (compile_imm_load_word ctor imm off)
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, rb_emit_op] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> simp[rb_emit_op]
QED

Theorem rb_compile_imm_store_word:
  rb_operand_ok off /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME op => rb_operand_ok op) ==>
  rb_step (K T) (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def, rb_emit_void] >>
  strip_tac >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_emit_op, rb_emit_void]
QED

Theorem rb_compile_ptr_load:
  rb_operand_ok op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step rb_operand_ok (compile_ptr_load ctor imm loc op)
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def, rb_compile_imm_load_word,
                        rb_emit_op]
QED

Theorem rb_compile_ptr_store:
  rb_operand_ok dst /\ rb_operand_ok v /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_ptr_store ctor imm loc dst v)
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, rb_compile_imm_store_word, rb_emit_void]
QED

Theorem rb_compile_copy_memory:
  !dst src n. rb_operand_ok dst /\ rb_operand_ok src ==>
  rb_step (K T) (compile_copy_memory dst src n)
Proof
  rpt gen_tac >> Cases_on `n` >>
  simp[compile_copy_memory_def, rb_step_return, rb_emit_void]
QED

Theorem rb_compile_alloc_dynamic:
  !size. rb_operand_ok size ==> rb_step rb_operand_ok (compile_alloc_dynamic size)
Proof
  simp[compile_alloc_dynamic_def, rb_emit_op]
QED

Theorem rb_vv_with_type:
  rb_value_ok v ==> rb_value_ok (vv_with_type ty v)
Proof
  Cases_on `v` >> simp[vv_with_type_def, rb_value_ok_def]
QED

Theorem rb_bind_emit_op:
  EVERY rb_operand_ok ops /\
  (!op. rb_operand_ok op ==> rb_step Q (f op)) ==>
  rb_step Q (comp_bind (emit_op opc ops) f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_emit_op]
QED

Theorem rb_bind_fresh_label:
  (!l. rb_operand_ok (Label l) ==> rb_step Q (f l)) ==>
  rb_step Q (comp_bind (fresh_label suffix) f)
Proof
  strip_tac >> irule rb_step_bind >>
  qexists_tac `\l. rb_operand_ok (Label l)` >> simp[rb_fresh_label]
QED

Theorem rb_bind_fresh_var:
  (!v. rb_step Q (f v)) ==> rb_step Q (comp_bind fresh_var f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `K T` >> simp[rb_fresh_var]
QED

Theorem rb_bind_new_block:
  (!v. rb_step Q (f v)) ==> rb_step Q (comp_bind (new_block lbl) f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `K T` >> simp[rb_new_block]
QED

Theorem rb_bind_return:
  rb_step Q (f x) ==> rb_step Q (compileEnv$comp_bind (comp_return x) f)
Proof
  simp[rb_step_def, comp_bind_def, comp_return_def]
QED

Theorem rb_ignore:
  rb_step (K T) m /\ rb_step Q n ==>
  rb_step Q (comp_ignore_bind m n)
Proof
  metis_tac[rb_step_ignore_bind]
QED

Theorem rb_bind_ptr_load:
  rb_operand_ok op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) /\
  (!v. rb_operand_ok v ==> rb_step Q (f v)) ==>
  rb_step Q (comp_bind (compile_ptr_load ctor imm loc op) f)
Proof
  strip_tac >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_compile_ptr_load]
QED

Theorem rb_bind_cond:
  (p ==> rb_step Q (comp_bind a f)) /\
  (~p ==> rb_step Q (comp_bind b f)) ==>
  rb_step Q (comp_bind (if p then a else b) f)
Proof
  Cases_on `p` >> simp[]
QED

Theorem rb_compile_scaled_addr:
  rb_operand_ok src ==>
  rb_step rb_operand_ok
    (if scale = 1 then emit_op ADD [src; Var idx]
     else comp_bind (emit_op MUL [Var idx; Lit (n2w scale)])
                    (\scaled. emit_op ADD [src; scaled]))
Proof
  strip_tac >> Cases_on `scale = 1` >> simp[rb_emit_op] >>
  irule rb_bind_emit_op >> simp[rb_emit_op]
QED

Theorem rb_compile_word_copy_loop_base:
  rb_operand_ok src /\ rb_operand_ok dst /\ rb_operand_ok count_op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T)
    (compile_word_copy_loop_base src dst count_op loadloc storeloc ctor imm)
Proof
  strip_tac >> pure_rewrite_tac[compile_word_copy_loop_base_def, LET_THM] >> BETA_TAC >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> disch_tac) >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_inst]) >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_inst]) >>
  irule rb_ignore >> (conj_tac >- simp[rb_new_block]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_inst]) >>
  irule rb_ignore >> (conj_tac >- simp[rb_new_block]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_scaled_addr]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_bind_ptr_load >> simp[] >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_scaled_addr]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_compile_ptr_store]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_inst]) >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_inst]) >>
  simp[rb_new_block]
QED

Theorem rb_compile_word_copy_loop_op:
  rb_operand_ok src /\ rb_operand_ok dst /\ rb_operand_ok count_op ==>
  rb_step (K T) (compile_word_copy_loop_op src dst count_op loadloc storeloc ctor)
Proof
  simp[compile_word_copy_loop_op_def, rb_compile_word_copy_loop_base]
QED

Theorem rb_compile_word_copy_loop:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_word_copy_loop src dst n loadloc storeloc ctor)
Proof
  simp[compile_word_copy_loop_def, rb_compile_word_copy_loop_op]
QED

Theorem rb_compile_bytestring_word_count:
  rb_operand_ok src ==> rb_step rb_operand_ok (compile_bytestring_word_count src)
Proof
  strip_tac >> rewrite_tac[compile_bytestring_word_count_def] >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_bind_emit_op >> simp[rb_emit_op]
QED

Theorem rb_compile_lit_byte_offset:
  rb_operand_ok op ==> rb_step rb_operand_ok (compile_lit_byte_offset op off)
Proof
  strip_tac >> Cases_on `off = 0` >> simp[compile_lit_byte_offset_def, rb_step_return] >>
  Cases_on `op` >> gvs[rb_step_return, rb_emit_op]
QED

Theorem rb_compile_imm_copy_to_memory:
  !n src dst off.
  rb_operand_ok src /\ rb_operand_ok dst /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct_on `n` >- simp[compile_imm_copy_to_memory_def, rb_step_return] >>
  rpt strip_tac >> rewrite_tac[compile_imm_copy_to_memory_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_imm_load_word]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_void]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_imm_store_words:
  !n src dst off.
  rb_operand_ok src /\ rb_operand_ok dst /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_imm_store_words imm src dst n off)
Proof
  Induct_on `n` >- simp[compile_imm_store_words_def, rb_step_return] >>
  rpt strip_tac >> rewrite_tac[compile_imm_store_words_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_compile_imm_store_word]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_storage_to_memory:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_storage_to_memory src dst n)
Proof simp[compile_storage_to_memory_def, rb_compile_word_copy_loop]
QED

Theorem rb_compile_memory_to_storage:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_memory_to_storage src dst n)
Proof simp[compile_memory_to_storage_def, rb_compile_word_copy_loop]
QED

Theorem rb_compile_transient_to_memory:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_transient_to_memory src dst n)
Proof simp[compile_transient_to_memory_def, rb_compile_word_copy_loop]
QED

Theorem rb_compile_memory_to_transient:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_memory_to_transient src dst n)
Proof simp[compile_memory_to_transient_def, rb_compile_word_copy_loop]
QED

Theorem rb_compile_code_to_memory:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_code_to_memory src dst n)
Proof
  strip_tac >> Cases_on `n = 0` >>
  simp[compile_code_to_memory_def, rb_step_return] >>
  irule rb_ignore >> simp[rb_compile_word_copy_loop, rb_step_return]
QED

Theorem rb_compile_load_storage:
  rb_operand_ok slot ==>
  rb_step rb_operand_ok (compile_load_storage slot prim n alloc)
Proof
  strip_tac >> Cases_on `prim` >> simp[compile_load_storage_def, rb_emit_op] >>
  Cases_on `n = 1` >> simp[] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >-
   (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
    irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_ignore >> simp[rb_compile_storage_to_memory, rb_step_return]
QED

Theorem rb_compile_load_transient:
  rb_operand_ok slot ==>
  rb_step rb_operand_ok (compile_load_transient slot prim n alloc)
Proof
  strip_tac >> Cases_on `prim` >> simp[compile_load_transient_def, rb_emit_op] >>
  Cases_on `n = 1` >> simp[] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >-
   (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
    irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_ignore >> simp[rb_compile_transient_to_memory, rb_step_return]
QED

Theorem rb_compile_load_immutable:
  rb_operand_ok off ==>
  rb_step rb_operand_ok (compile_load_immutable off prim n alloc ctor)
Proof
  strip_tac >> Cases_on `prim` >-
   (Cases_on `ctor` >> simp[compile_load_immutable_def, rb_emit_op]) >>
  simp[compile_load_immutable_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >> irule rb_ignore >>
  simp[rb_compile_code_to_memory, rb_step_return]
QED

Theorem rb_compile_ensure_in_memory:
  rb_operand_ok ptr_op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step rb_operand_ok
    (compile_ensure_in_memory ptr_op loc mem_bytes word_count ctor imm)
Proof
  strip_tac >> Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, rb_step_return] >-
   (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
    (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
    BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
    simp[LET_THM] >> irule rb_ignore >>
    (conj_tac >-
      (Cases_on `word_count = 1` >> simp[] >-
        (irule rb_bind_emit_op >> simp[rb_emit_void]) >>
       irule rb_ignore >> simp[rb_compile_storage_to_memory, rb_step_return])) >>
    simp[rb_step_return]) >-
   (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
    (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
    BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
    simp[LET_THM] >> irule rb_ignore >>
    (conj_tac >-
      (Cases_on `word_count = 1` >> simp[] >-
        (irule rb_bind_emit_op >> simp[rb_emit_void]) >>
       irule rb_ignore >> simp[rb_compile_transient_to_memory, rb_step_return])) >>
    simp[rb_step_return]) >-
   (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
    (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
    BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
    simp[LET_THM] >> irule rb_ignore >>
    simp[rb_compile_imm_copy_to_memory, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >> irule rb_ignore >>
  (conj_tac >- simp[rb_emit_void]) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_with_byte_offset:
  rb_operand_ok op ==> rb_step rb_operand_ok (compile_with_byte_offset op off)
Proof
  Cases_on `off = 0` >> simp[compile_with_byte_offset_def, rb_step_return, rb_emit_op]
QED

Theorem rb_compile_bytestring_copy_len:
  rb_operand_ok src ==> rb_step rb_operand_ok (compile_bytestring_copy_len src)
Proof
  strip_tac >> rewrite_tac[compile_bytestring_copy_len_def] >>
  ntac 4 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  simp[rb_emit_op]
QED

Theorem rb_compile_store_bytestring:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_store_bytestring src dst)
Proof
  strip_tac >> rewrite_tac[compile_store_bytestring_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  simp[rb_compile_bytestring_copy_len, rb_emit_void]
QED

Theorem rb_compile_copy_memory_dynamic:
  rb_operand_ok src /\ rb_operand_ok dst /\ rb_operand_ok len ==>
  rb_step (K T) (compile_copy_memory_dynamic dst src len)
Proof
  simp[compile_copy_memory_dynamic_def, rb_emit_void]
QED

Theorem rb_compile_load_calldata:
  rb_operand_ok off ==>
  rb_step rb_operand_ok (compile_load_calldata off prim n alloc)
Proof
  strip_tac >> Cases_on `prim` >> simp[compile_load_calldata_def, rb_emit_op] >>
  Cases_on `n = 1` >> simp[] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >-
   (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
    irule rb_ignore >> simp[rb_emit_void, rb_step_return]) >>
  irule rb_ignore >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_store_immutable_bytestring:
  rb_operand_ok src /\ rb_operand_ok dst /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_store_immutable_bytestring imm src dst)
Proof
  strip_tac >> rewrite_tac[compile_store_immutable_bytestring_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_bytestring_word_count]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_ignore >> simp[rb_compile_word_copy_loop_base, rb_step_return]
QED

Theorem rb_compile_slot_to_memory:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_slot_to_memory src dst n loc)
Proof
  simp[compile_slot_to_memory_def, rb_compile_word_copy_loop]
QED

Theorem rb_compile_store_immutable:
  rb_operand_ok src /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T) (compile_store_immutable imm src off n)
Proof
  simp[compile_store_immutable_def, rb_compile_imm_store_words]
QED

Theorem rb_compile_bytes_data_ptr:
  rb_operand_ok op ==> rb_step rb_operand_ok (compile_bytes_data_ptr op loc)
Proof
  simp[compile_bytes_data_ptr_def, rb_emit_op]
QED

Theorem rb_compile_bytestring_length:
  rb_operand_ok op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step rb_operand_ok (compile_bytestring_length ctor imm op loc)
Proof
  simp[compile_bytestring_length_def, rb_compile_ptr_load]
QED

Theorem rb_compile_nonreentrant_lock:
  rb_step (K T) (compile_nonreentrant_lock key trans view)
Proof
  Cases_on `trans` >> rewrite_tac[compile_nonreentrant_lock_def] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_void]) >>
  Cases_on `view` >> simp[rb_emit_void, rb_step_return]
QED

Theorem rb_compile_nonreentrant_unlock:
  rb_step (K T) (compile_nonreentrant_unlock key trans view)
Proof
  Cases_on `view` >> Cases_on `trans` >>
  simp[compile_nonreentrant_unlock_def, rb_emit_void, rb_step_return]
QED

Theorem rb_compile_zero_memory_loop:
  !ptr_op i words. rb_operand_ok ptr_op ==>
  rb_step (K T) (compile_zero_memory_loop ptr_op i words)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  rewrite_tac[Once compile_zero_memory_loop_def] >>
  Cases_on `i >= words` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >-
    (Cases_on `i = 0` >> simp[rb_step_return, rb_emit_op])) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_ignore >> (conj_tac >- simp[rb_emit_void]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_zero_memory:
  rb_operand_ok ptr_op ==> rb_step (K T) (compile_zero_memory ptr_op n)
Proof
  Cases_on `n` >> simp[compile_zero_memory_def, rb_step_return,
                       rb_compile_zero_memory_loop]
QED

Theorem rb_unwrap_value:
  rb_env_ok env /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (unwrap_value env vv)
Proof
  Cases_on `vv` >>
  simp[exprLoweringTheory.unwrap_value_def, rb_value_ok_def, rb_ptr_ok_def,
       rb_step_return] >> strip_tac >>
  `case env.ce_imm_alloca of NONE => T | SOME region => rb_operand_ok region`
    by gvs[rb_env_ok_def] >>
  rename1 `rb_operand_ok pval.ptr_operand` >>
  rename1 `is_word_type ty` >>
  Cases_on `is_word_type ty` >> simp[rb_compile_ptr_load] >>
  Cases_on `pval.ptr_location` >>
  simp[rb_step_return, rb_compile_ensure_in_memory]
QED

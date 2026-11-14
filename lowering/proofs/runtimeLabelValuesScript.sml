(* Operand exclusion for compound value and memory operations. *)
Theory runtimeLabelValues
Ancestors
  runtimeLabelPrimitives runtimeLabelInvariant context compileEnv emitHelper
  loweringShapeDefs venomInst list finite_map stmtLowering

Theorem rb_compile_word_copy_loop_base:
  rb_operand_ok src /\ rb_operand_ok dst /\ rb_operand_ok count_op /\
  (case imm of NONE => T | SOME region => rb_operand_ok region) ==>
  rb_step (K T)
    (compile_word_copy_loop_base src dst count_op loadloc storeloc ctor imm)
Proof
  strip_tac >> pure_rewrite_tac[compile_word_copy_loop_base_def, LET_THM] >> BETA_TAC >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> disch_tac) >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_scaled_addr]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_bind_ptr_load >> simp[] >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_scaled_addr]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_compile_ptr_store]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_void]) >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_compile_imm_store_word]) >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_word_copy_loop, rb_step_return]
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
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_storage_to_memory, rb_step_return]
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
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_transient_to_memory, rb_step_return]
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
  simp[LET_THM] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
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
    simp[LET_THM] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
    (conj_tac >-
      (Cases_on `word_count = 1` >> simp[] >-
        (irule rb_bind_emit_op >> simp[rb_emit_void]) >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_storage_to_memory, rb_step_return])) >>
    simp[rb_step_return]) >-
   (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
    (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
    BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
    simp[LET_THM] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
    (conj_tac >-
      (Cases_on `word_count = 1` >> simp[] >-
        (irule rb_bind_emit_op >> simp[rb_emit_void]) >>
       irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_transient_to_memory, rb_step_return])) >>
    simp[rb_step_return]) >-
   (irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
    (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
    BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
    simp[LET_THM] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
    simp[rb_compile_imm_copy_to_memory, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >>
  (reverse conj_tac >- simp[rb_compile_alloc_buffer]) >>
  BETA_TAC >> gen_tac >> simp[rb_buffer_ok_def] >> disch_tac >>
  simp[LET_THM] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  (conj_tac >- simp[rb_emit_void]) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
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
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_void, rb_step_return]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_word_copy_loop_base, rb_step_return]
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_void]) >>
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
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_void]) >>
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


Theorem rb_typed_memory:
  (!env dst dty src sty. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step (K T) (compile_store_memory_typed env dst dty src sty)) /\
  (!env dst src dtys stys doff soff. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step (K T) (compile_typed_copy_fields env dst src dtys stys doff soff)) /\
  (!env dst dty src sty n. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step (K T) (compile_copy_sarray_typed env dst dty src sty n)) /\
  (!env dst dty cap src sty. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step (K T) (compile_copy_dynarray_typed env dst dty cap src sty)) /\
  (!env dst src dfs sfs doff soff. rb_operand_ok dst /\ rb_operand_ok src ==>
    rb_step (K T) (compile_struct_typed_copy env dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[compile_store_memory_typed_def, rb_step_return]
  >- simp[compile_store_memory_typed_def, rb_step_return]
  >- suspend "fields"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- simp[compile_store_memory_typed_def, rb_step_return]
  >> suspend "struct"
QED

Resume rb_typed_memory[dispatch]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def] >>
  Cases_on `is_word_type dty` >-
    (simp[] >> irule rb_bind_emit_op >> simp[rb_emit_void]) >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type sty` >-
    simp[rb_compile_store_bytestring] >>
  Cases_on `acyclic_struct_metadata env.ce_struct_fields` >>
  simp[rb_emit_void] >>
  Cases_on `dty` >> Cases_on `sty` >>
  gvs[rb_compile_copy_memory, AllCaseEqs()] >>
  Cases_on `b` >> Cases_on `b'` >> gvs[rb_compile_copy_memory]
QED

Resume rb_typed_memory[fields]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_with_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_with_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >> simp[LET_THM] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >> first_x_assum irule >> simp[]
QED

Resume rb_typed_memory[struct]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def] >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_with_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_with_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >> first_x_assum irule >> simp[]
QED

Resume rb_typed_memory[sarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def] >> simp[LET_THM] >>
  IF_CASES_TAC >- simp[rb_compile_copy_memory] >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> disch_tac) >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 4 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  (conj_tac >- (first_x_assum irule >> metis_tac[])) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule rb_bind_new_block >> BETA_TAC >> simp[rb_step_return]
QED

Resume rb_typed_memory[dynarray]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_memory_typed_def] >> simp[LET_THM] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_void])) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  IF_CASES_TAC >-
   (irule rb_bind_emit_op >> simp[rb_compile_copy_memory_dynamic]) >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> disch_tac) >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 4 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  (conj_tac >- (first_x_assum irule >> gvs[])) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule rb_bind_new_block >> BETA_TAC >> simp[rb_step_return]
QED

Finalise rb_typed_memory

Theorem rb_compile_store_memory:
  rb_operand_ok src /\ rb_operand_ok dst ==>
  rb_step (K T) (compile_store_memory env src dst dty sty)
Proof
  strip_tac >> rewrite_tac[compile_store_memory_def] >>
  Cases_on `is_word_type dty` >> simp[rb_emit_void] >>
  Cases_on `is_bytestring_type dty` >> simp[rb_compile_store_bytestring] >>
  IF_CASES_TAC >> simp[rb_compile_copy_memory, cj 1 rb_typed_memory]
QED

Theorem rb_compile_load_memory:
  rb_operand_ok op ==> rb_step rb_operand_ok (compile_load_memory op prim)
Proof
  Cases_on `prim` >> simp[compile_load_memory_def, rb_emit_op, rb_step_return]
QED

Theorem rb_compile_encode_log_topic:
  rb_operand_ok op ==> rb_step rb_operand_ok (compile_encode_log_topic op bytes)
Proof
  strip_tac >> Cases_on `bytes` >>
  simp[compile_encode_log_topic_def, rb_step_return] >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  simp[rb_emit_op]
QED

Theorem rb_slots:
  (!env src slot ty trans. rb_operand_ok src /\ rb_operand_ok slot ==>
    rb_step (K T) (compile_store_slots env src slot ty trans)) /\
  (!env src slot members moff soff trans. rb_operand_ok src /\ rb_operand_ok slot ==>
    rb_step (K T) (compile_store_slots_members env src slot members moff soff trans)) /\
  (!env src slot elem count_op trans.
    rb_operand_ok src /\ rb_operand_ok slot /\ rb_operand_ok count_op ==>
    rb_step (K T) (compile_copy_elements_to_slots env src slot elem count_op trans))
Proof
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac
  >- suspend "dispatch"
  >- simp[compile_store_slots_def, rb_step_return]
  >- suspend "members"
  >> suspend "elements"
QED

Resume rb_slots[members]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_slots_def] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  (reverse conj_tac >- simp[rb_compile_lit_byte_offset]) >>
  BETA_TAC >> gen_tac >> disch_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >> first_x_assum irule >> simp[]
QED

Resume rb_slots[elements]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_slots_def] >> simp[LET_THM] >>
  ntac 3 (irule rb_bind_fresh_label >> BETA_TAC >> gen_tac >> disch_tac) >>
  irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 2 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst]) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_new_block]) >>
  ntac 4 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  (conj_tac >- (first_x_assum irule >> simp[])) >>
  irule rb_bind_emit_op >> BETA_TAC >>
  (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac >>
  ntac 2 (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> (conj_tac >- simp[rb_emit_inst])) >>
  irule rb_bind_new_block >> BETA_TAC >> simp[rb_step_return]
QED

Resume rb_slots[dispatch]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  rewrite_tac[Once compile_store_slots_def] >> simp[LET_THM] >>
  IF_CASES_TAC >-
   (IF_CASES_TAC >-
     (irule rb_bind_emit_op >> simp[rb_emit_void]) >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_step_return] >>
    Cases_on `trans` >>
    simp[rb_compile_memory_to_storage, rb_compile_memory_to_transient]) >>
  IF_CASES_TAC >-
   (irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
    (reverse conj_tac >- simp[rb_compile_bytestring_word_count]) >>
    BETA_TAC >> gen_tac >> disch_tac >>
    irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_word_copy_loop_op, rb_step_return]) >>
  IF_CASES_TAC >- simp[rb_emit_void] >>
  Cases_on `ty` >> gvs[rb_emit_void] >>
  Cases_on `b` >> gvs[] >>
  ntac 3 (irule rb_bind_emit_op >> BETA_TAC >>
    (reverse conj_tac >- simp[]) >> gen_tac >> disch_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
  (conj_tac >- (first_x_assum irule >> simp[])) >> simp[rb_emit_void]
QED

Finalise rb_slots

Theorem rb_env_bind_local:
  rb_env_ok env /\ rb_location_ok loc ==>
  rb_env_ok (env with ce_vars updated_by (\m. m |+ (id,loc)))
Proof
  simp[rb_env_ok_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `id = k` >> gvs[] >> metis_tac[]
QED

Theorem rb_declare_local:
  rb_env_ok env ==> rb_step rb_env_ok (declare_local env id ty)
Proof
  strip_tac >> pure_rewrite_tac[declare_local_def, LET_THM] >> BETA_TAC >>
  Cases_on `env.ce_alloca_locals` >> simp[]
  >- (irule rb_bind_fresh_var >> BETA_TAC >> gen_tac >>
      irule rb_step_return >>
      simp[rb_env_ok_def, FLOOKUP_UPDATE, rb_location_ok_def] >>
      rpt strip_tac >> gvs[rb_env_ok_def] >>
      Cases_on `id = k` >> gvs[rb_location_ok_def] >> metis_tac[]) >>
  irule rb_step_return >> gvs[rb_env_ok_def] >> metis_tac[]
QED

Theorem rb_declare_stmt_local:
  rb_env_ok env ==> rb_step rb_env_ok (declare_stmt_local env s)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, rb_declare_local, rb_step_return]
QED

Theorem rb_emit_local_alloca:
  rb_step (K T) (emit_local_alloca env id)
Proof
  simp[emit_local_alloca_def] >>
  Cases_on `FLOOKUP env.ce_vars id` >> simp[rb_step_return] >>
  Cases_on `x` >> simp[rb_step_return] >>
  rename1 `PtrVar op sz` >> Cases_on `op` >>
  simp[rb_step_return, rb_emit_inst]
QED

Theorem rb_compile_return_unlock:
  rb_step (K T) (compile_return_unlock env)
Proof
  pure_rewrite_tac[compile_return_unlock_def, LET_THM] >> pairarg_tac >>
  Cases_on `is_nonreentrant` >>
  simp[rb_compile_nonreentrant_unlock, rb_step_return]
QED

Theorem rb_compile_fixed_region_with_id:
  !n. rb_step (\ib. rb_buffer_ok (SND ib)) (compile_fixed_region_with_id n)
Proof
  simp[rb_step_def, rb_state_ok_def, compile_fixed_region_with_id_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, rb_buffer_ok_def,
       state_insts_def, all_blocks_def, EVERY_APPEND, mk_inst_def]
QED

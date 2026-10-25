(* Typed immutable copies preserve values and disjoint initialized slices.
   Source reads are padded: a short literal buffer need not contain the whole
   destination capacity. No canonical padding assumption is made. *)
Theory immutableConstructorRelation
Ancestors
  valueMemoryTransport valueEncoding immutableSectionRel immutableCopyExecution
  immutableMemoryFrame immutableValue compileEnv context venomState list arithmetic
  immutableEncodingProofs immutableEncoding immutableWordExecution byte
  venomExecSemantics

Theorem immutable_word_store_representation:
  immutable_value_admissible tv v /\
  encode_immutable_value tv v = word_to_bytes (w:bytes32) T ==>
  val_in_memory tv v off (istore off w s).vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) (istore off w s).vs_memory)
Proof
  strip_tac >>
  `type_memory_size tv = 32` by
    metis_tac[encode_immutable_value_length, immutable_word_bytes_length,
              immutable_word_bytes_def] >>
  `off <= LENGTH (istore off w s).vs_memory` by
    (simp[venomExecSemanticsTheory.istore_def, immutable_mstore_capacity, MAX_DEF] >>
     rw[] >> decide_tac) >>
  `TAKE (type_memory_size tv) (DROP off (istore off w s).vs_memory) =
     encode_immutable_value tv v` by
    (asm_simp_tac bool_ss [] >> irule immutable_istore_word_slice) >>
  conj_tac
  >- (irule immutable_encoding_slice_decodes >> simp[]) >>
  irule immutable_value_bytes_slice >> simp[]
QED

Theorem immutable_compiled_word_value:
  compile_imm_store_word (SOME region) off_op value st = ((),st') /\
  eval_operand region s = SOME 0w /\ eval_operand off_op s = SOME a /\
  eval_operand value (update_var ("%" ++ toString st.cs_next_var) a s) = SOME w /\
  immutable_value_admissible tv v /\
  encode_immutable_value tv v = word_to_bytes (w:bytes32) T ==>
  ?final. run_inst_seq (emitted_insts st st') s = OK final /\
    val_in_memory tv v (w2n a) final.vs_memory /\
    immutable_value_bytes_rel tv v
      (mem_bytes_at (w2n a) (type_memory_size tv) final.vs_memory)
Proof
  strip_tac >> drule_all compile_imm_store_word_execution >> strip_tac >>
  goal_assum (drule_at Any) >>
  irule immutable_word_store_representation >> simp[]
QED

Theorem immutable_memory_bytes_full:
  off + n <= LENGTH mem ==>
  mem_bytes_at off n mem = TAKE n (DROP off mem)
Proof
  strip_tac >>
  `n <= LENGTH (DROP off mem)` by (simp[LENGTH_DROP] >> decide_tac) >>
  simp[mem_bytes_at_def, TAKE_APPEND1]
QED

Theorem immutable_write_memory_readback:
  mem_bytes_at at (LENGTH bs)
    (write_memory_with_expansion at bs s).vs_memory = bs
Proof
  `at + LENGTH bs <= LENGTH (write_memory_with_expansion at bs s).vs_memory` by
    (simp[immutable_write_memory_capacity, MAX_DEF] >> rw[] >> decide_tac) >>
  simp[immutable_memory_bytes_full, immutable_write_memory_slice]
QED

Theorem immutable_copy_memory_readback:
  mem_bytes_at dst_addr n
    (write_memory_with_expansion dst_addr
      (mem_bytes_at src_addr n src_bytes) s).vs_memory =
  mem_bytes_at src_addr n src_bytes
Proof
  mp_tac (Q.INST [`at` |-> `dst_addr`,
      `bs` |-> `mem_bytes_at src_addr n src_bytes`]
    immutable_write_memory_readback) >>
  simp[mem_bytes_at_def]
QED

Theorem immutable_copy_memory_value:
  val_in_memory tv v src_addr src_bytes /\ val_wf tv v /\
  type_memory_size tv = n ==>
  val_in_memory tv v dst_addr
    (write_memory_with_expansion dst_addr
      (mem_bytes_at src_addr n src_bytes) s).vs_memory
Proof
  strip_tac >>
  `mem_bytes_at src_addr (type_memory_size tv) src_bytes =
   mem_bytes_at dst_addr (type_memory_size tv)
     (write_memory_with_expansion dst_addr
       (mem_bytes_at src_addr n src_bytes) s).vs_memory` by
    gvs[immutable_copy_memory_readback] >>
  drule_all val_in_memory_transport >> simp[]
QED

Theorem immutable_copy_memory_bytes:
  immutable_value_bytes_rel tv v
    (mem_bytes_at src_addr n src_bytes) /\ type_memory_size tv = n ==>
  immutable_value_bytes_rel tv v
    (mem_bytes_at dst_addr n
      (write_memory_with_expansion dst_addr
        (mem_bytes_at src_addr n src_bytes) s).vs_memory)
Proof
  simp[immutable_copy_memory_readback]
QED

Theorem immutable_write_preserves_bytes:
  immutable_value_bytes_rel tv v (mem_bytes_at off (type_memory_size tv) s.vs_memory) /\
  off + type_memory_size tv <= LENGTH s.vs_memory /\
  (off + type_memory_size tv <= dst_addr \/ dst_addr + LENGTH bs <= off) ==>
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv)
      (write_memory_with_expansion dst_addr bs s).vs_memory)
Proof
  strip_tac >>
  `off + type_memory_size tv <=
     LENGTH (write_memory_with_expansion dst_addr bs s).vs_memory` by
    (simp[immutable_write_memory_capacity, MAX_DEF] >> rw[] >> decide_tac) >>
  `TAKE (type_memory_size tv)
      (DROP off (write_memory_with_expansion dst_addr bs s).vs_memory) =
   TAKE (type_memory_size tv) (DROP off s.vs_memory)` by
    (irule immutable_write_memory_disjoint >> simp[]) >>
  fs[immutable_memory_bytes_full]
QED

Theorem immutable_copy_memory_preserves_value:
  val_in_memory tv v off s.vs_memory /\ val_wf tv v /\
  off + type_memory_size tv <= LENGTH s.vs_memory /\
  (off + type_memory_size tv <= dst_addr \/ dst_addr + n <= off) ==>
  val_in_memory tv v off
    (write_memory_with_expansion dst_addr
      (mem_bytes_at src_addr n src_bytes) s).vs_memory
Proof
  strip_tac >> qabbrev_tac `bs = mem_bytes_at src_addr n src_bytes` >>
  `LENGTH bs = n` by simp[Abbr `bs`, mem_bytes_at_def] >>
  `off + type_memory_size tv <=
     LENGTH (write_memory_with_expansion dst_addr bs s).vs_memory` by
    (simp[immutable_write_memory_capacity, MAX_DEF] >> rw[] >> decide_tac) >>
  `TAKE (type_memory_size tv)
      (DROP off (write_memory_with_expansion dst_addr bs s).vs_memory) =
   TAKE (type_memory_size tv) (DROP off s.vs_memory)` by
    (irule immutable_write_memory_disjoint >> simp[]) >>
  `mem_bytes_at off (type_memory_size tv) s.vs_memory =
   mem_bytes_at off (type_memory_size tv)
     (write_memory_with_expansion dst_addr bs s).vs_memory` by
    simp[immutable_memory_bytes_full] >>
  drule_all val_in_memory_transport >> simp[]
QED

Theorem immutable_compiled_memory_value:
  (if store then compile_imm_store_words (SOME region) src_op dst_op n off
   else compile_imm_copy_to_memory ctor (SOME region) src_op dst_op n off) st = ((),st') /\
  eval_operand src_op s = SOME (n2w src_addr) /\
  eval_operand dst_op s = SOME (n2w dst_addr) /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s /\ 0 < n /\ (store \/ ctor) /\
  src_addr + off + 32*n < dimword (:256) /\
  dst_addr + off + 32*n < dimword (:256) /\
  (dst_addr + off + 32*n <= src_addr + off \/
   src_addr + off + 32*n <= dst_addr + off) /\
  val_in_memory tv v (src_addr + off) s.vs_memory /\
  val_wf tv v /\ type_memory_size tv = 32*n ==>
  ?result. immutable_execution_frame st s st' result /\
    val_in_memory tv v (dst_addr + off) result.vs_memory /\
    !old_tv old_v old_off.
      val_in_memory old_tv old_v old_off s.vs_memory /\ val_wf old_tv old_v /\
      old_off + type_memory_size old_tv <= LENGTH s.vs_memory /\
      (old_off + type_memory_size old_tv <= dst_addr + off \/
       dst_addr + off + 32*n <= old_off) ==>
      val_in_memory old_tv old_v old_off result.vs_memory
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all immutable_compile_memory_snapshot >> strip_tac >>
  rename1 `immutable_execution_frame st s st' result` >>
  qexists_tac `result` >> asm_rewrite_tac[] >>
  asm_rewrite_tac[mcopy_def, read_memory_def, GSYM mem_bytes_at_def, LET_THM] >>
  BETA_TAC >> conj_tac
  >- (irule immutable_copy_memory_value >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule immutable_copy_memory_preserves_value >> asm_rewrite_tac[]
QED

Theorem immutable_compiled_runtime_value:
  compile_imm_copy_to_memory F imm_base src_op dst_op n off st = ((),st') /\
  eval_operand src_op s = SOME (n2w src_addr) /\
  eval_operand dst_op s = SOME (n2w dst_addr) /\
  fresh_vars_wrt st s /\ 0 < n /\
  src_addr + off + 32*n < dimword (:256) /\
  dst_addr + off + 32*n < dimword (:256) /\
  val_in_memory tv v (src_addr + off) s.vs_data_section /\
  val_wf tv v /\ type_memory_size tv = 32*n ==>
  ?result. immutable_execution_frame st s st' result /\
    val_in_memory tv v (dst_addr + off) result.vs_memory
Proof
  strip_tac >> drule_all immutable_compile_runtime_snapshot >> strip_tac >>
  rename1 `immutable_execution_frame st s st' result` >>
  qexists_tac `result` >> asm_rewrite_tac[] >>
  asm_rewrite_tac[GSYM mem_bytes_at_def] >>
  irule immutable_copy_memory_value >> asm_rewrite_tac[]
QED

(* This companion to the typed-copy theorem also constrains omitted sparse
   array cells. Its source premise allows arbitrary inactive capacity bytes. *)
Theorem immutable_compiled_memory_bytes:
  (if store then compile_imm_store_words (SOME region) src_op dst_op n off
   else compile_imm_copy_to_memory ctor (SOME region) src_op dst_op n off) st = ((),st') /\
  eval_operand src_op s = SOME (n2w src_addr) /\
  eval_operand dst_op s = SOME (n2w dst_addr) /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s /\ 0 < n /\ (store \/ ctor) /\
  src_addr + off + 32*n < dimword (:256) /\
  dst_addr + off + 32*n < dimword (:256) /\
  (dst_addr + off + 32*n <= src_addr + off \/
   src_addr + off + 32*n <= dst_addr + off) /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at (src_addr + off) (32*n) s.vs_memory) ==>
  ?result. immutable_execution_frame st s st' result /\
    immutable_value_bytes_rel tv v
      (mem_bytes_at (dst_addr + off) (32*n) result.vs_memory)
Proof
  disch_then (fn th => MAP_EVERY assume_tac (CONJUNCTS th)) >>
  drule_all immutable_compile_memory_snapshot >> strip_tac >>
  rename1 `immutable_execution_frame st s st' result` >>
  qexists_tac `result` >> asm_rewrite_tac[] >>
  asm_rewrite_tac[mcopy_def, read_memory_def, GSYM mem_bytes_at_def, LET_THM] >>
  BETA_TAC >> asm_rewrite_tac[immutable_copy_memory_readback]
QED

Theorem immutable_compiled_runtime_bytes:
  compile_imm_copy_to_memory F imm_base src_op dst_op n off st = ((),st') /\
  eval_operand src_op s = SOME (n2w src_addr) /\
  eval_operand dst_op s = SOME (n2w dst_addr) /\
  fresh_vars_wrt st s /\ 0 < n /\
  src_addr + off + 32*n < dimword (:256) /\
  dst_addr + off + 32*n < dimword (:256) /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at (src_addr + off) (32*n) s.vs_data_section) ==>
  ?result. immutable_execution_frame st s st' result /\
    immutable_value_bytes_rel tv v
      (mem_bytes_at (dst_addr + off) (32*n) result.vs_memory)
Proof
  strip_tac >> drule_all immutable_compile_runtime_snapshot >> strip_tac >>
  rename1 `immutable_execution_frame st s st' result` >>
  qexists_tac `result` >> asm_rewrite_tac[] >>
  asm_rewrite_tac[GSYM mem_bytes_at_def, immutable_copy_memory_readback]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable constructor relation: " ^ name)
  end) (DB.thms "immutableConstructorRelation");

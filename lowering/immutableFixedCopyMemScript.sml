(* Existing constructor-base contracts follow from the option-generic core. *)
Theory immutableFixedCopyMem
Ancestors
  immutableFixedOptionMem

Theorem immutable_store_one_mem:
  immutable_store_one (SOME region) src dst off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  w2n (a+n2w off) + 32 <= s.vs_alloca_next /\
  w2n (b+n2w off) + 32 <= s.vs_alloca_next ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_store_one_mem_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_fixed_words_mem:
  !n off sa sb s a b.
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\
  w2n a + off + 32*n <= s.vs_alloca_next /\
  w2n b + off + 32*n <= s.vs_alloca_next /\
  w2n a + off + 32*n < dimword (:256) /\
  w2n b + off + 32*n < dimword (:256) ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_words_mem_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_store_one_code:
  immutable_store_one (SOME region) src dst off sa = ((),sb) ==>
  same_blocks sa sb /\
  ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) is
Proof
  strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_store_one_code_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_fixed_words_code:
  !n off sa sb.
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) ==>
  same_blocks sa sb /\
  ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
    EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE]) is
Proof
  rpt gen_tac >> strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_words_code_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_fixed_words_mem_cont:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  immutable_execution_frame sa s sb t /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_words_mem_cont_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_fixed_copy_mem_endpoint:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt sa s /\ 0 < n /\
  a + off + 32*n <= s.vs_alloca_next /\
  b + off + 32*n <= s.vs_alloca_next /\
  a + off + 32*n < dimword (:256) /\
  b + off + 32*n < dimword (:256) /\
  (b + off + 32*n <= a + off \/ a + off + 32*n <= b + off) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. immutable_execution_frame sa s sb t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                 vs_immutables := t.vs_immutables|> /\
    t.vs_memory = (mcopy (b+off) (a+off) (32*n) s).vs_memory /\
    mem_bytes_at (b+off) (32*n) t.vs_memory =
      mem_bytes_at (a+off) (32*n) s.vs_memory /\
    (!p k. p+k <= b+off \/ b+off+32*n <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  strip_tac >> mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_copy_mem_endpoint_option)) >> simp[] >> metis_tac[]
QED

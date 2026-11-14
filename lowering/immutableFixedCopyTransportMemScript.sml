(* The original SOME-base interfaces use the option-generic transport core. *)
Theory immutableFixedCopyTransportMem
Ancestors
  immutableFixedOptionTransportMem

Theorem immutable_fixed_words_run_transport:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  immutable_execution_frame sa (drop_fresh sa s) sb t0 /\
  run_inst_seq_mem_ok (emitted_insts sa sb) (drop_fresh sa s) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      vars_ext t0 t /\ t = t0 with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_words_run_transport_option)) >> simp[] >> metis_tac[]
QED

Theorem immutable_fixed_copy_operand_mem_endpoint:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  eval_operand region s = SOME 0w /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. region = Var x ==> not_fresh_at sa x) /\ 0 < n /\
  a + off + 32*n <= s.vs_alloca_next /\
  b + off + 32*n <= s.vs_alloca_next /\
  a + off + 32*n < dimword (:256) /\
  b + off + 32*n < dimword (:256) /\
  (b + off + 32*n <= a + off \/ a + off + 32*n <= b + off) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_data_section = s.vs_data_section /\
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
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`imm` |-> `SOME region`]
    (SPEC_ALL immutable_fixed_copy_operand_mem_endpoint_option)) >> simp[] >> metis_tac[]
QED

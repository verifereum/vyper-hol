(* Finite memory-checked execution of fixed immutable copies. *)
Theory immutableFixedCopyPathMem
Ancestors
  immutableFixedCopyTransportMem immutableFixedCopyMem fragGasSeqMem fragGasMode
  exprLoweringProps compileEnv fragExec venomState venomInst list rich_list

Theorem immutable_fixed_words_path_mem[local]:
  compile_imm_store_words (SOME region) src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule immutable_fixed_words_code >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def] >> gvs[IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, DROP_LENGTH_APPEND] >>
     `LENGTH sa.cs_current_insts -
       (LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)) = 0` by
       decide_tac >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i is ==> _` drule >> strip_tac >>
     gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (fs[EVERY_MEM] >> simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i is ==> _ \/ _ \/ _` drule >>
     strip_tac >> gvs[]) >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[gas_marked_path_def]
QED

Theorem immutable_fixed_copy_operand_mem_path:
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
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    gas_marked_path T ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all immutable_fixed_copy_operand_mem_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all immutable_fixed_words_path_mem >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

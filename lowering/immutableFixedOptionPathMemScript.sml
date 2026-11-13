(* Finite memory-checked execution of fixed immutable copies. *)
Theory immutableFixedOptionPathMem
Ancestors
  immutableFixedOptionTransportMem immutableFixedOptionMem bodyDeclMemoryCounted fragGasMode
  exprLoweringProps compileEnv fragExec venomState venomInst list rich_list

Theorem immutable_fixed_words_path_mem_option[local]:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule immutable_fixed_words_code_option >> strip_tac >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_APPEND] >>
  simp_tac bool_ss [gas_marked_path_def] >> irule body_decl_zero_gas_path >>
  simp[] >> qexists_tac `sa` >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i is ==> _` drule >>
  simp_tac bool_ss [MEM] >> rpt strip_tac >> gvs[is_terminator_def]
QED

Theorem immutable_fixed_copy_operand_mem_path_option:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. imm = SOME region ==> eval_operand region s = SOME 0w) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!region x. imm = SOME region /\ region = Var x ==> not_fresh_at sa x) /\ 0 < n /\
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
  drule_all immutable_fixed_copy_operand_mem_endpoint_option >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all immutable_fixed_words_path_mem_option >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  qexists_tac `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Unconditional safety of the jump from initialization to the loop header. *)
Theory calldataInitializerSafety
Ancestors
  decoderPrefixEdges calldataDynInit memSafeRun instMemFrontier
  venomExecSemantics venomState venomInst list rich_list unitTransformDefs
  contextCodegenRel codegenRel fragExecMem exprLoweringProps emitHelperProps
  abiDecoderContract compileEnv venomInstProps

Theorem calldata_loop_entry_all_fuel_pullback[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr fn.fn_blocks = SOME hb /\
  phi_prefix_length hb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted ==>
  ((!fuel. mem_safe_run fuel ctx fn (jump_to hdr s)) ==>
    !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst id JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `!fuel. step_inst fuel ctx (mk_inst id JMP [Label hdr] []) s =
     OK (jump_to hdr s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     simp[Once step_inst_base_def, mk_inst_def, jump_to_def]) >>
  ho_match_mp_tac (GEN_ALL decoder_edge_all_fuel_pullback) >>
  goal_assum (drule_at (Pos hd)) >>
  qexists_tac `hb` >> simp[jump_to_def] >> conj_tac
  >- (gen_tac >> pure_once_rewrite_tac[exec_block_def] >>
      asm_rewrite_tac[] >> simp[jump_to_def, mk_inst_def, is_terminator_def]) >>
  gen_tac >> pure_once_rewrite_tac[mem_safe_block_def] >>
  asm_rewrite_tac[] >> simp[mem_safe_step_non_invoke, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def]
QED

Theorem calldata_loop_prefix_all_fuel_pullback:
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) start = ((hdr,body_lbl,exit_lbl),end_st) /\
  fn_has_code start end_st fn /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted ==>
  ((!fuel. mem_safe_run fuel ctx fn (jump_to hdr s)) ==>
    !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >> drule_all calldata_loop_prefix_entry_code >> strip_tac >>
  ho_match_mp_tac (GEN_ALL calldata_loop_entry_all_fuel_pullback) >> metis_tac[]
QED

Theorem calldata_executed_init_all_fuel_pullback:
  loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st loop_st) /\
  run_inst_seq_mem_ok (emitted_insts st loop_st) initial /\
  run_inst_seq (emitted_insts st loop_st) initial = OK t /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),end_st) /\
  fn_has_code loop_st end_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)) ==>
    !fuel. mem_safe_run fuel ctx fn initial)
Proof
  strip_tac >> drule_all calldata_loop_prefix_entry_code >> strip_tac >>
  `?xs. loop_st.cs_current_insts = st.cs_current_insts ++ xs /\
    emitted_insts st loop_st = xs` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  `t.vs_current_bb = initial.vs_current_bb` by
    (irule run_inst_seq_preserves_field >> qexists_tac `xs` >>
     fs[EVERY_MEM] >> metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  `t.vs_halted = initial.vs_halted` by
    (irule run_inst_seq_preserves_field >> qexists_tac `xs` >>
     fs[EVERY_MEM] >> metis_tac[step_preserves_halted, step_inst_non_invoke]) >>
  strip_tac >>
  `!fuel. mem_safe_run fuel ctx fn
    (t with vs_inst_idx := LENGTH loop_st.cs_current_insts)` by
    (drule_at (Pos hd) calldata_loop_prefix_all_fuel_pullback >>
     disch_then (qspec_then `t with vs_inst_idx := LENGTH loop_st.cs_current_insts` mp_tac) >>
     simp[jump_to_def] >> disch_then irule >>
     qpat_x_assum `!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)` mp_tac >>
     simp[jump_to_def]) >>
  gen_tac >>
  qspecl_then [`xs`, `initial`, `fuel`, `ctx`, `fn`, `bb`] mp_tac
    mem_safe_run_inst_seq >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[] >>
  (impl_tac >- metis_tac[]) >>
  disch_then (irule o CONJUNCT1) >> qexists_tac `t` >> gvs[]
QED

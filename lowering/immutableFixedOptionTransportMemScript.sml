(* Transport fixed immutable writes to states with populated temporaries. *)
Theory immutableFixedOptionTransportMem
Ancestors
  immutableFixedOptionMem immutableStoreOptionMem immutableCopyExecution bodyMemTbExtract32MemoryTransfer
  appendStorageStageTransportPtr
  varsExt instMemFrontier memSafeRun fragExecMem fragExec
  venomExecSemantics venomState venomInst venomInstProps
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  finite_map list rich_list arithmetic

Theorem immutable_fixed_step_mem_transport[local]:
  MEM i.inst_opcode [ADD; MLOAD; ISTORE] /\ vars_ext s big /\
  ((?t. step_inst_base i s = OK t) \/
   (?a t. step_inst_base i s = Abort a t)) /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s ==>
  inst_mem_below_frontier i big /\ inst_dload_in_section i big
Proof
  Cases_on `i` >> simp_tac bool_ss [MEM, instruction_accessors] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
      exec_write2_def, AllCaseEqs()]
  >- (irule below_frontier_no_ranges >> simp[])
  >> gvs[vars_ext_def] >>
  qpat_x_assum `big = _` SUBST1_TAC >>
  gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def,
      codegenRelTheory.fixed_source_write_range_def,
      eval_operand_vars_ext]
QED

Theorem immutable_offset_output_fresh[local]:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  !x. not_fresh_at sa x ==>
    EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `off = 0`
  >- simp[compile_lit_byte_offset_def, comp_return_def, emitted_insts_def] >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL]
QED

Theorem immutable_store_one_output_fresh[local]:
  immutable_store_one imm src dst off sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  !x. not_fresh_at sa x ==>
    EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb)
Proof
  simp[immutable_store_one_def, immutable_comp_bind_cases] >> strip_tac >>
  imp_res_tac immutable_byte_offset_extends >>
  imp_res_tac immutable_offset_output_fresh >>
  imp_res_tac emitted_insts_emit_op >>
  drule immutable_store_option_code >> strip_tac >>
  conj_tac >- decide_tac >>
  rpt strip_tac >>
  `not_fresh_at st1 x /\ not_fresh_at st1' x /\ not_fresh_at st1'' x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD, LESS_EQ_TRANS] >>
  `sb.cs_current_insts = sa.cs_current_insts ++
    (emitted_insts sa st1 ++ emitted_insts st1 st1' ++
     emitted_insts st1' st1'' ++ emitted_insts st1'' sb)` by
    asm_rewrite_tac[APPEND_ASSOC] >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 st1' ++
    emitted_insts st1' st1'' ++ emitted_insts st1'' sb` by
    (qpat_x_assum `sb.cs_current_insts = sa.cs_current_insts ++ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> disch_tac >>
     CONV_TAC (LAND_CONV (REWR_CONV emitted_insts_def)) >>
     first_x_assum SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  simp[EVERY_APPEND] >> simp[mk_inst_def] >>
  qpat_x_assum `not_fresh_at st1 x`
    (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
  disch_then (qspec_then `st1.cs_next_var` mp_tac) >> simp[]
QED

Theorem immutable_fixed_words_output_fresh[local]:
  !n off sa sb.
    compile_imm_store_words imm src dst n off sa = ((),sb) ==>
    sa.cs_next_var <= sb.cs_next_var /\
    !x. not_fresh_at sa x ==>
      EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts sa sb)
Proof
  Induct
  >- simp[compile_imm_store_words_def, comp_return_def, emitted_insts_def] >>
  simp[immutable_store_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt gen_tac >> strip_tac >>
  drule immutable_store_one_output_fresh >> strip_tac >>
  drule immutable_store_one_code_option >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac >- decide_tac >>
  rpt strip_tac >>
  `not_fresh_at st1 x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule immutable_fixed_words_code_option >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa st1 ++ emitted_insts st1 sb` by
    (irule emitted_insts_append >> simp[emitted_insts_def, DROP_APPEND]) >>
  simp[EVERY_APPEND]
QED

Theorem immutable_fixed_words_run_transport_option:
  compile_imm_store_words imm src dst n off sa = ((),sb) /\
  immutable_execution_frame sa (drop_fresh sa s) sb t0 /\
  run_inst_seq_mem_ok (emitted_insts sa sb) (drop_fresh sa s) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      run_inst_seq_mem_ok (emitted_insts sa sb) s /\
      vars_ext t0 t /\ t = t0 with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule immutable_fixed_words_code_option >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; MLOAD; ISTORE])
     (emitted_insts sa sb)` by gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[EVERY_MEM, emitted_insts_def, DROP_LENGTH_APPEND] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0` by
    fs[immutable_execution_frame_def] >>
  `vars_ext (drop_fresh sa s) s` by simp[vars_ext_drop_fresh] >>
  drule_all run_inst_seq_vars_ext_ok >> strip_tac >>
  qexists_tac `t'` >> simp[] >> conj_tac
  >- (irule run_inst_seq_mem_ok_total_vars_ext >>
      reverse conj_tac
      >- (simp[] >> qexists_tac `drop_fresh sa s` >> simp[]) >>
      rpt gen_tac >> strip_tac >> irule immutable_fixed_step_mem_transport >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- fs[vars_ext_def] >>
  rpt strip_tac >> irule run_inst_seq_non_output_vars >>
  goal_assum (drule_at Any) >>
  drule immutable_fixed_words_output_fresh >> strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem immutable_fixed_copy_operand_mem_endpoint_option:
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
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?t0. immutable_execution_frame sa (drop_fresh sa s) sb t0 /\
    run_inst_seq_mem_ok (emitted_insts sa sb) (drop_fresh sa s) /\
    t0.vs_allocas = s.vs_allocas /\ t0.vs_alloca_next = s.vs_alloca_next /\
    t0 = (drop_fresh sa s) with <|vs_vars := t0.vs_vars;
      vs_memory := t0.vs_memory; vs_immutables := t0.vs_immutables|> /\
    t0.vs_memory = (mcopy (b+off) (a+off) (32*n) s).vs_memory /\
    mem_bytes_at (b+off) (32*n) t0.vs_memory =
      mem_bytes_at (a+off) (32*n) s.vs_memory /\
    (!p k. p+k <= b+off \/ b+off+32*n <= p ==>
      mem_bytes_at p k t0.vs_memory = mem_bytes_at p k s.vs_memory)` by
    (mp_tac (Q.INST [`s` |-> `drop_fresh sa s`] immutable_fixed_copy_mem_endpoint_option) >>
     simp[fresh_vars_wrt_drop_fresh, freshWritesTheory.eval_operand_drop_fresh,
          drop_fresh_def, mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  drule_all immutable_fixed_words_run_transport_option >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
  drule immutable_fixed_words_code_option >> strip_tac >>
  suspend "finish"
QED

Resume immutable_fixed_copy_operand_mem_endpoint_option[finish]:
  markerLib.RESUME_TAC >>
  `frag_exec_mem ctx sa sb (\u. u = s)
    (\u. u = (t with vs_inst_idx := LENGTH sb.cs_current_insts)) (K F)` by
    (irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
     fs[same_blocks_def, emitted_insts_def, DROP_APPEND] >>
     gvs[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >>
     strip_tac >> gvs[is_terminator_def]) >>
  `mem_cont_sim ctx func s (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule memContinuationTheory.mem_cont_sim_from_fragment >>
     disch_then (qspec_then `s` mp_tac) >> simp[]) >>
  qexists_tac `t` >>
  gvs[drop_fresh_def, emitted_insts_def, DROP_APPEND,
      venom_state_component_equality] >> gvs[]
QED

Finalise immutable_fixed_copy_operand_mem_endpoint_option

Theory bodyFullRawLogDynamicSequence
Ancestors
  fragGasSeqPtr fragExec fragExecMem instSeqComposePtr exprLoweringProps emitHelper compileEnv
  venomExecSemantics venomState instIdxIndep ptrSafeRun ptrDiscipline contextCodegenRel
  words list rich_list arithmetic venomInst instMemFrontier ghostPcTransportPtr

Theorem raw_log_dynamic_sequence_path:
  emit_op MLOAD [data_op] sm = (len_op,s1) /\
  emit_op ADD [data_op;Lit 32w] s1 = (ptr_op,s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] s2 = ((),sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm s2) s = OK t /\
  run_inst_seq_mem_ok (emitted_insts sm s2) s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm s2) s G1 tn1 /\
  (let i = mk_inst s2.cs_next_id LOG
     (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len_op;ptr_op]) [] in
   step_inst_base i t = OK v /\ inst_mem_below_frontier i t /\
   inst_dload_in_section i t /\ ptr_inst_ok D lo 0 ctx func G1 tn1 i t /\
   step_prov PG G1 i v = G1 /\ step_taint i t v tn1 = tn1) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (v with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn1) /\
  (v with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
  (v with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base i t = OK v` >>
  `run_inst_seq (emitted_insts sm s2 ++ [i]) s = OK v` by
    (drule run_inst_seq_append >> disch_then (qspec_then `[i]` mp_tac) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sm s2 ++ [i]) s` by
    (irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >>
     gvs[] >> simp[run_inst_seq_mem_ok_def]) >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm s2 ++ [i] /\
   LENGTH (emitted_insts sm s2) = 2 /\
   EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> GAS)
     (emitted_insts sm s2 ++ [i])` by
    (gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def, Abbr `i`] >>
     simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> simp[mk_inst_def, is_terminator_def]) >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  `EVERY (\j. ~is_terminator j.inst_opcode) (emitted_insts sm s2)` by
    gvs[EVERY_APPEND, EVERY_MEM] >>
  `isPREFIX (emitted_insts sm s2 ++ [i])
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qspec_then `emitted_insts sm s2` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`s`, `s.vs_inst_idx`] mp_tac) >>
     simp[exec_result_map_def] >>
     simp[venom_state_component_equality]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (`isPREFIX (emitted_insts sm s2) (DROP s.vs_inst_idx bb.bb_instructions)` by
       metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC] >>
     `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode)
        (emitted_insts sm s2)` by gvs[EVERY_APPEND, EVERY_MEM] >>
     drule_all exec_block_run_inst_seq >>
     disch_then (qspecl_then [`0`, `ctx`] mp_tac) >> simp[]) >>
  `get_instruction bb t.vs_inst_idx =
     SOME (mk_inst sm.cs_next_id MLOAD [data_op]
       [STRING #"%" (toString sm.cs_next_var)])` by
    (gvs[IS_PREFIX_APPEND] >>
     gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
         fresh_id_def, emit_def, emitted_insts_def] >>
     simp[get_instruction_def, EL_APPEND2, EL_APPEND1, APPEND_ASSOC] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `~in_revert_forward func t` by
    (simp[in_revert_forward_def, revert_forward_at_def, revert_forward_pair_def] >>
     rpt strip_tac >> gvs[mk_inst_def]) >>
  `!k. ptr_inst_ok D lo 0 ctx func G1 tn1 i (t with vs_inst_idx := k)` by
    (gen_tac >>
     `step_inst_base i (t with vs_inst_idx := k) = OK (v with vs_inst_idx := k)` by
       simp[step_inst_inst_idx_indep, Abbr `i`, mk_inst_def, is_terminator_def, exec_result_map_def] >>
     qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, about_to_revert_def,
          allocas_from_def, allocas_below_fmp_def] >>
     simp[Abbr `i`, mk_inst_def, step_inst_non_invoke,
          step_inst_inst_idx_indep, exec_result_map_def, is_terminator_def,
          allocas_from_def, allocas_below_fmp_def] >>
     rpt strip_tac >> simp[] >> metis_tac[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sm s2 ++ [i]) s G1 tn1` by
    (irule inst_seq_ptr_append_ok >> simp[] >> qexistsl [`G1`,`tn1`] >> simp[] >>
     simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
          Abbr `i`, mk_inst_def, is_terminator_def] >>
     gvs[mk_inst_def]) >>
  `EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode)
      (emitted_insts sm s2 ++ [i])` by gvs[EVERY_MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `FILTER (\j. j.inst_opcode = GAS) (emitted_insts sm s2 ++ [i]) = []` by
    (simp[FILTER_EQ_NIL] >> gvs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[] >> strip_tac >>
  drule_all exec_block_run_inst_seq >>
  disch_then (qspecl_then [`0`, `ctx`] mp_tac) >> simp[]
QED

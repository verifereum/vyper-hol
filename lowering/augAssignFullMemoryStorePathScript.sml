(* A single MSTORE has one endpoint, with pointer safety supplied per horizon. *)
Theory augAssignFullMemoryStorePath
Ancestors
  fragGasSeqPtr fragGasOriginPtr emitHelperProps exprLoweringProps fragExec
  gasOutcomeFull instMemFrontier unitTransformDefs codegenRel
  memSafeRun contextCodegenRel
  venomExecSemantics venomInst venomState list

Theorem augassign_mstore_endpoint_path:
  emit_void MSTORE [dst;value] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME a /\ eval_operand value s = SOME w /\
  w2n a + 32 <= s.vs_alloca_next /\
  i = mk_inst sa.cs_next_id MSTORE [dst;value] [] /\
  u = (mstore (w2n a) w s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  G' = step_prov PG G i (mstore (w2n a) w s) /\
  tn' = step_taint i s (mstore (w2n a) w s) tn /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn i s)
  ==>
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G',tn')) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
  (!x. lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >> fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME i` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  reverse conj_tac
  >- simp[mstore_def, lookup_var_def] >>
  rpt strip_tac >>
  `step_inst_base i s = OK (mstore (w2n a) w s)` by
    (gvs[] >> irule step_MSTORE >> simp[]) >>
  `i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
   ~is_terminator i.inst_opcode /\ inst_mem_below_frontier i s /\
   inst_dload_in_section i s` by
    simp[mk_inst_def, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, fixed_source_write_range_def,
         is_terminator_def] >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn i s` by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx),G',tn')` by
    (drule_all straight_line_origin_ptr_edge >> simp[]) >>
  `~(mstore (w2n a) w s with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[mstore_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND, arithmeticTheory.ADD1]
QED

(* A clean storage-word store has a fixed endpoint at every horizon. *)
Theory augAssignFullStore
Ancestors
  stmtAppendStorageRunPtr instSeqPtrLo fragGasSeqPtr fragGasOriginPtr
  fragExec emitHelper emitHelperProps compileEnv exprLoweringProps
  ptrDiscipline ptrSafeRun codegenRel contextCodegenRel
  unitTransformDefs instMemFrontier memSafeRun
  venomExecSemantics venomInst venomState list rich_list

Theorem storage_word_store_origin_ptr:
  emit_void (if tr then TSTORE else SSTORE) [addr;op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_call_ctx.cc_static /\
  eval_operand addr s = SOME slot /\ eval_operand op s = SOME w /\
  op_taint tn addr = {} /\ op_taint tn op = {} ==>
  !D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK ((if tr then tstore slot w s else sstore slot w s)
             with vs_inst_idx := LENGTH sb.cs_current_insts), G,
       if tr then tn with t_trans := key_update tn.t_trans slot {}
       else tn with t_stor := key_update tn.t_stor slot {})
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >> fs[same_blocks_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [addr;op] [])`
    by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE)
    [addr;op] []` >>
  qabbrev_tac `u = if tr then tstore slot w s else sstore slot w s` >>
  qabbrev_tac `un = if tr then tn with t_trans := key_update tn.t_trans slot {}
                   else tn with t_stor := key_update tn.t_stor slot {}` >>
  `step_inst_base inst s = OK u` by
    (Cases_on `tr` >>
     simp[Abbr `inst`, Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_write2_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    fs[run_inst_seq_def, Abbr `inst`] >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
   u.vs_requests = s.vs_requests` by
    (Cases_on `tr` >> simp[Abbr `u`, sstore_def, tstore_def]) >>
  drule_all emit_storage_store_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `D`] assume_tac) >>
  qpat_x_assum `emitted_insts sa sb = _` SUBST_ALL_TAC >>
  `inst_seq_ptr D lo ctx func PG G tn [inst] s G un` by
    (irule inst_seq_ptr_zero_to_lo >> simp[Abbr `un`] >>
     qexists_tac `D` >> fs[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s /\
   step_prov PG G inst u = G /\ step_taint inst s u tn = un` by
    gvs[inst_seq_ptr_def] >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
   ~is_terminator inst.inst_opcode /\ inst_mem_below_frontier inst s /\
   inst_dload_in_section inst s` by
    (Cases_on `tr` >>
     simp[Abbr `inst`, mk_inst_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, is_terminator_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G,un)` by
    (mp_tac (Q.INST [`i` |-> `inst`, `u` |-> `u`, `D` |-> `D`, `lo` |-> `lo`,
       `PG` |-> `PG`, `explicit` |-> `explicit`] straight_line_origin_ptr_edge) >>
     simp[]) >>
  `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    (Cases_on `tr` >> simp[Abbr `u`, sstore_def, tstore_def]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G,un)` by
    metis_tac[gas_origin_ptr_path_rules, APPEND] >>
  gvs[Abbr `u`, Abbr `un`]
QED

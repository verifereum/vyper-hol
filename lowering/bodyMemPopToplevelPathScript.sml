(* Memory checks for the storage pop fragment, including exiting ASSERT. *)
Theory bodyMemPopToplevelPath
Ancestors
  exprSimPopStorage fragExecMem instMemFrontier
  exprLoweringProps memSafeRun venomInst list
  bodyDeclMemoryCounted bodyDeclMemoryCore fragGasPathMem
  venomExecSemantics venomState fragGasSeqAbort fragGasMode
  instIdxIndep venomInstProofs fragExec rich_list

Theorem dynarray_pop_storage_mem_ok:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  Cases_on `tr` >>
  simp[emitted_insts_def, DROP_APPEND, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def]
QED

Theorem dynarray_pop_storage_opcodes:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  Cases_on `tr` >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]
QED

(* Compiler shape and concrete S1 execution packaged at the body cursor. *)
Theorem dynarray_pop_storage_path_mem:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    alloca_history func t /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
    t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand r t = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz) /\
    t = ((if tr then tstore slot (tload slot s - 1w) s
          else sstore slot (sload slot s - 1w) s)
          with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>)
Proof
  strip_tac >>
  drule dynarray_pop_storage_mem_ok >> disch_then (qspec_then `s` assume_tac) >>
  drule dynarray_pop_storage_opcodes >> strip_tac >>
  drule dynarray_pop_storage_shape >> strip_tac >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `same_blocks sa sb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    simp[same_blocks_def, emitted_insts_def, DROP_APPEND] >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (qpat_x_assum `sb.cs_current_insts = _ ++ emitted_insts _ _` kall_tac >>
     simp[emitted_insts_def, DROP_APPEND]) >>
  drule_all body_decl_cursor_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (qpat_x_assum `EVERY _ (emitted_insts _ _)` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >>
  `u.vs_alloca_next = s.vs_alloca_next /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u = _ with vs_vars := _` mp_tac >>
     Cases_on `tr` >> simp[tstore_def, sstore_def, LET_THM] >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[eval_operand_def, lookup_var_def] >>
  reverse conj_tac
  >- (qpat_x_assum `u = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
      simp[]) >>
  fs[EVERY_MEM, lookup_var_def] >> metis_tac[]
QED

(* Zero GAS sites on an aborting straight-line memory-checked prefix. *)
Theorem run_inst_seq_abort_zero_path_mem:
  !code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_marked_path T ctx func s 0
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >- (rename1 `step_inst_base h s = OK u` >>
      `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def, run_inst_seq_mem_ok_inst_idx] >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `j` >>
      drule_at (Pat `step_inst_base _ _ = OK _`) gas_marked_path_step >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  drule gas_marked_path_abort >> simp[] >> metis_tac[]
QED

Theorem dynarray_pop_storage_empty_path_mem:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a t. gas_path_mem ctx func s 0 (Abort a t)
Proof
  strip_tac >>
  drule dynarray_pop_storage_mem_ok >> disch_then (qspec_then `s` assume_tac) >>
  drule dynarray_pop_storage_opcodes >> strip_tac >>
  drule dynarray_pop_storage_shape >> strip_tac >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_pop_storage_run_empty >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = Abort a s'` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  drule_all run_inst_seq_abort_zero_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  fs[gas_marked_path_def] >> metis_tac[]
QED

(* Concrete endpoint for a memory-safe emitted word operation. *)
Theory bodyMemEmitOpFrame
Ancestors
  bodyDeclMemoryCounted bodyDeclMemoryCore allocaFootprint
  instMemFrontier memSafeRun fragGasPathMem stmtSimProps
  emitHelperProps freshWrites exprOperandVar
  exprLoweringProps fragGasMode compileEnv loweringStateRelDefs
  venomExecSemantics venomExecProofs venomInst venomState
  list finite_map

Theorem emit_op_word_path_frame_mem:
  !opc args sa op sb w s0 ctx func cenv cx es.
    emit_op opc args sa = (op,sb) /\
    (opc = ADD \/ opc = SLOAD \/ opc = TLOAD) /\
    step_inst_base
      (mk_inst sa.cs_next_id opc args [STRING #"%" (toString sa.cs_next_var)])
      s0 = OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s0) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
    alloca_history func s0 ==>
    ?t. gas_marked_path T ctx func s0 0 (OK t) /\
      eval_operand op t = SOME w /\
      stmt_state_rel ctx func cenv cx es t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      local_ptrs_reserved cenv sb /\ alloca_history func t /\
      (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
      t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
      sa.cs_next_var <= sb.cs_next_var /\
      (?out. op = Var out /\ not_fresh_at sb out) /\
      t = (update_var (STRING #"%" (toString sa.cs_next_var)) w s0
        with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    simp[is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (drule emit_op_mem_ok >> disch_then irule >>
     simp[below_frontier_no_ranges, mk_inst_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK (update_var out w s0)` by
    gvs[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >> simp[mk_inst_def, is_terminator_def]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def] >>
  gvs[update_var_def] >>
  simp[Abbr `out`, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

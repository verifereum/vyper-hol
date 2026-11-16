(* Horizon-uniform ordinary Env read boundary. *)
Theory bodyFullBuiltinEnvReadsStep
Ancestors
  bodyFullGhostFrame fragGasSeqPtr fragGasOriginPtr allocaHistoryFragment
  exprLoweringProps emitHelperProps exprSimProps
  exprLowering compileEnv vyperContext valueEncoding valueEncodingProofs
  loweringStateRelDefs venomExecSemantics venomInst venomState
  ptrSafeRun ptrDiscipline instMemFrontier memSafeRun
  words list finite_map

Theorem env_reads_step_full:
  item <> PrevHash /\ item <> MsgGas /\
  compile_env_var item sa = (op,sb) /\
  evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) ==>
  ?t G' tn'. !H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK t,G',tn') /\
    stmt_state_rel H ctx func cenv cx es t /\
    eval_operand op t = SOME (val_to_w256 v) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_memory = s0.vs_memory /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    tn'.t_mem = tn0.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s0 /\ FLOOKUP G' x = FLOOKUP G0 x /\
      op_taint tn' (Var x) = op_taint tn0 (Var x)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t
Proof
  strip_tac >> Cases_on `item` >>
  gvs[compile_env_var_def] >>
  (qmatch_asmsub_abbrev_tac `emit_op opc [] sa` >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc [] [out]` >>
  qabbrev_tac `u = update_var out (val_to_w256 v) s0` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s0.vs_inst_idx`,
    `step_prov PG G0 inst u`, `step_taint inst s0 u tn0`] >>
  gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `step_inst_base inst s0 = OK u` by
    (simp[Abbr `inst`, Abbr `opc`, Abbr `u`, step_inst_base_opcode_eqs,
          exec_read0_def, mk_inst_def] >>
     gvs[evaluate_builtin_def, stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
         val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G0 tn0 inst s0 /\
   inst_mem_below_frontier inst s0 /\ inst_dload_in_section inst s0` by
    (simp[Abbr `inst`, Abbr `opc`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          inst_dload_in_section_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     rpt strip_tac >> gvs[Abbr `u`, update_var_def, bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def,
        fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s0.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >>
     simp[Abbr `inst`, Abbr `out`]) >>
  conj_tac
  >- (`inst.inst_opcode <> GAS` by simp[Abbr `inst`, Abbr `opc`, mk_inst_def] >>
      `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0)
        (if inst.inst_opcode = GAS then [(func.fn_name, inst.inst_id) IN explicit] else [])
        (OK (u with vs_inst_idx := SUC s0.vs_inst_idx),
         step_prov PG G0 inst u, step_taint inst s0 u tn0)` by
        (irule straight_line_origin_ptr_edge >>
         gvs[Abbr `inst`, Abbr `opc`, mk_inst_def, is_terminator_def]) >>
      pop_assum mp_tac >> simp[] >> strip_tac >>
      `~(u with vs_inst_idx := SUC s0.vs_inst_idx).vs_halted` by
        simp[Abbr `u`, update_var_def] >>
      drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
      drule (cj 2 gas_origin_ptr_path_rules) >>
      disch_then (qspecl_then [`[]`, `OK (u with vs_inst_idx := SUC s0.vs_inst_idx)`,
        `step_prov PG G0 inst u`, `step_taint inst s0 u tn0`] mp_tac) >>
      gvs[] >> metis_tac[]) >>
  `~not_fresh_at sa out` by simp[Abbr `out`, not_fresh_at_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by metis_tac[] >>
  `not_local_ptr cenv es.scopes out` by metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (simp[Abbr `u`] >> irule stmt_state_rel_update_var >> simp[]) >>
  conj_tac >- metis_tac[stmt_state_rel_inst_idx] >>
  `alloca_inv s0` by gvs[stmt_state_rel_def] >>
  `alloca_history func (u with vs_inst_idx := SUC s0.vs_inst_idx)` by
    (`~is_terminator inst.inst_opcode` by
       simp[Abbr `inst`, Abbr `opc`, mk_inst_def, is_terminator_def] >>
     `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all allocaHistoryTheory.alloca_history_base_step >> simp[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x (u with vs_inst_idx := SUC s0.vs_inst_idx) = lookup_var x s0 /\
    FLOOKUP (step_prov PG G0 inst u) x = FLOOKUP G0 x /\
    op_taint (step_taint inst s0 u tn0) (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     simp[Abbr `inst`, Abbr `opc`, mk_inst_def, step_prov_def, out_prov_def,
          set_prov_def, step_taint_def, op_taint_def, set_var_taint_def,
          out_taint_def, Abbr `u`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  reverse (rpt conj_tac)
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`] >>
      simp[Abbr `u`, update_var_def] >>
      simp[Abbr `inst`, Abbr `opc`, mk_inst_def, step_taint_def,
           mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
           new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
           codegenRelTheory.source_memory_write_ranges_def,
           FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[Abbr `u`, Abbr `out`, update_var_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, Abbr `inst`, Abbr `opc`, mk_inst_def,
       step_prov_def, out_prov_def, set_prov_def, op_prov_def,
       step_taint_def, op_taint_def, out_taint_def, set_var_taint_def,
       mem_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def, range_bytes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       FLOOKUP_DRESTRICT] >>
  simp[FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[])
QED

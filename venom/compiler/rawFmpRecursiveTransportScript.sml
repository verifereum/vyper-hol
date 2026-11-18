Theory rawFmpRecursiveTransport
Ancestors
  rawFmpTransportDefs rawReachableFmp ctxLookupAgreeHelpers unitShapeDefs instIdxIndep
  venomExecSemantics venomExecProofs venomInst venomState list

Theorem setup_callee_fmp_update:
  setup_callee fn args
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  OPTION_MAP (\cs. cs with <|vs_fmp := p; vs_initial_fmp := i;
                            vs_call_entry_fmp := p|>)
    (setup_callee fn args s)
Proof
  simp[setup_callee_def] >> Cases_on `NULL fn.fn_blocks` >>
  simp[venom_state_component_equality]
QED

Theorem bind_outputs_fmp_update:
  bind_outputs outs vals
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
  OPTION_MAP (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                           vs_call_entry_fmp := e|>) (bind_outputs outs vals s)
Proof
  `!kvs s. FOLDL (\t (k,v). update_var k v t)
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) kvs =
    (FOLDL (\t (k,v). update_var k v t) s kvs)
      with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>` by
    (Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
     first_x_assum (qspec_then `update_var h0 h1 s` mp_tac) >>
     simp[update_var_def]) >>
  simp[bind_outputs_def] >> Cases_on `LENGTH outs = LENGTH vals` >> simp[]
QED

Theorem run_defs_fmp_update_under_base:
  (!op s p i e.
    eval_operand op
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
    eval_operand op s) /\
  (!insts s p i e.
    eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
                       vs_call_entry_fmp := e|>) insts =
    exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>)
      (eval_phis s insts)) /\
  (!inst s p i e.
    raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> INVOKE ==>
    step_inst_base inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
    exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>)
      (step_inst_base inst s)) ==>
  ((!fuel ctx inst s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
    raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
      (step_inst fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
   (!fuel ctx bb s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      bb.bb_instructions ==>
    raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
      (exec_block fuel ctx bb
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
   (!fuel ctx fn s. !p i e.
    EVERY (\fn. EVERY (\inst. raw_opcode_ok inst.inst_opcode /\
                              inst.inst_opcode <> DALLOCA) (fn_insts fn))
      ctx.ctx_functions /\
    EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
      (fn_insts fn) ==>
    raw_fmp_result_rel p i e (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))))
Proof
  strip_tac >> ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_fmp_update_under_base[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[step_inst_non_invoke] >>
  `step_inst_base inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
    exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>)
      (step_inst_base inst s)` by metis_tac[] >>
  simp[] >> irule (SRULE [] raw_fmp_result_rel_uniform)
QED
Resume run_defs_fmp_update_under_base[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[GSYM exec_block_def] >>
  once_rewrite_tac[exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA` by
    gvs[get_instruction_def, EVERY_EL] >>
  `raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
     (step_inst fuel ctx inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))`
    by metis_tac[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
  >- (Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      Cases_on `v.vs_halted` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!p i e. ?ce. _`
    (qspecl_then [`p`, `i`, `e`] strip_assume_tac) >>
  simp[] >> metis_tac[]
QED
Resume run_defs_fmp_update_under_base[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[run_blocks_def] >>
  Cases_on `fuel` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
     bb.bb_instructions` by
    (irule EVERY_fn_block >> qexists_tac `fn` >>
     metis_tac[lookup_block_MEM]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> gvs[exec_result_map_def] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `raw_fmp_result_rel p i e
    (exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (exec_block n ctx bb
      (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
                 vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))`
    by simp[] >>
  Cases_on `exec_block n ctx bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[]
  >- (Cases_on `v.vs_halted` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!p i e. ?ce. _`
    (qspecl_then [`p`, `i`, `e`] strip_assume_tac) >>
  simp[] >> metis_tac[]
QED
Resume run_defs_fmp_update_under_base[invoke]:
  `!ops. eval_operands ops
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
      eval_operands ops s` by
    (gen_tac >> irule eval_operands_agree >> simp[]) >>
  once_rewrite_tac[step_inst_def] >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  rename1 `eval_operands x1 s = SOME args` >>
  simp[SRULE [] setup_callee_fmp_update] >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `EVERY (\inst. raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA)
     (fn_insts callee)` by
    (gvs[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `raw_fmp_result_rel p i p (run_blocks fuel ctx callee cs)
     (run_blocks fuel ctx callee
       (cs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>))`
    by metis_tac[] >>
  Cases_on `run_blocks fuel ctx callee cs` >> gvs[]
  >- (qpat_x_assum `!p i e. ?ce. _`
        (qspecl_then [`p`, `i`, `p`] strip_assume_tac) >>
      simp[] >> metis_tac[])
  >- (qpat_x_assum `!p i e. ?ce. _`
        (qspecl_then [`p`, `i`, `p`] strip_assume_tac) >>
      simp[] >> metis_tac[]) >>
  rename1 `run_blocks fuel ctx callee cs = IntRet ret rs` >>
  `EVERY (\inst. inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET)
     (fn_insts callee)` by
    (gvs[EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `ret.iret_adopt_fmp = NONE` by metis_tac[run_defs_no_adopt_fmp] >>
  simp[adopt_return_fmp_def] >>
  `merge_callee_state
     (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
     (rs with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>) =
    (merge_callee_state s rs) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>` by
    simp[merge_callee_state_def, venom_state_component_equality] >>
  gvs[] >> simp[SRULE [] bind_outputs_fmp_update] >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (merge_callee_state s rs)` >> simp[]
QED
Finalise run_defs_fmp_update_under_base

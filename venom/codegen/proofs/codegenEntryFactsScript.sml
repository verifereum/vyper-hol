(* Static placement and entry-state facts, independent of completed function simulation. *)
Theory codegenEntryFacts
Ancestors
  codegenEntryRel frameRel codegenRel contextCodegenRel
  codegen asmSem venomExecSemantics venomState
  unitShapeDefs stackPlanGen stackOpSim fnPlanPlaceFnRegion
  callLayoutDefs fmpWfDefs venomWf venomInst
  venomExecProps venomRetProps fmpLowerProps
  fcgDefs fcgAnalysisProps fcgPostorder relation list rich_list

val _ = Parse.hide "cp";

Theorem codegen_assembly_first_region:
  generate_context_plan unit.cu_context = SOME cp /\
  codegen_assembly rpolicy unit = SOME prog /\
  cp.cp_regions = r :: rs ==>
  asm_block_at prog 0 (execute_plan cp.cp_initial_fmp r.sr_plan)
Proof
  strip_tac >>
  qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
  simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >>
  gvs[context_plan_ops_def, execute_plan_append, asm_block_at_def] >>
  rw[EL_APPEND1]
QED

Theorem no_param_insts_find_retpc[local]:
  !insts. no_param_insts insts ==>
          FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts = NONE
Proof
  Induct >> simp[FIND_thm, no_param_insts_def] >> rw[] >>
  strip_tac >> gvs[is_param_opcode_def]
QED

Theorem canonical_after_fmp_retpc[local]:
  !k insts. canonical_after_fmp k insts /\
    IS_SOME (FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts) ==>
    EXISTS (\inst. inst.inst_opcode = RETPC_PARAM) (get_params insts)
Proof
  rpt gen_tac >> Cases_on `insts` >>
  simp[canonical_after_fmp_def, FIND_thm, get_params_def] >>
  Cases_on `h.inst_opcode = RETPC_PARAM` >> simp[is_param_opcode_def] >>
  strip_tac >> imp_res_tac no_param_insts_find_retpc >> gvs[FIND_thm]
QED

Theorem canonical_entry_params_retpc[local]:
  !insts k. canonical_entry_params_from k insts /\
    IS_SOME (FIND (\inst. inst.inst_opcode = RETPC_PARAM) insts) ==>
    EXISTS (\inst. inst.inst_opcode = RETPC_PARAM) (get_params insts)
Proof
  Induct >> simp[FIND_thm, get_params_def] >> rpt gen_tac >>
  simp[Once canonical_entry_params_from_def] >>
  Cases_on `h.inst_opcode = PARAM` >> simp[is_param_opcode_def]
  >- (strip_tac >> first_x_assum irule >> metis_tac[]) >>
  Cases_on `h.inst_opcode = FMP_PARAM` >> simp[is_param_opcode_def]
  >- metis_tac[canonical_after_fmp_retpc] >>
  Cases_on `h.inst_opcode = RETPC_PARAM` >> simp[is_param_opcode_def] >>
  strip_tac >> imp_res_tac no_param_insts_find_retpc >> gvs[FIND_thm]
QED

Theorem retpc_param_has_retpc[local]:
  canonical_param_prefix func /\ IS_SOME (fn_retpc_param func) ==>
  fn_has_retpc func
Proof
  simp[canonical_param_prefix_def, fn_retpc_param_def, fn_entry_insts_def,
       entry_block_def, fn_has_retpc_def] >>
  Cases_on `func.fn_blocks` >> simp[FIND_thm] >>
  metis_tac[canonical_entry_params_retpc]
QED

Theorem fmp_lowered_wf_invoke_targets[local]:
  fmp_lowered_context_wf ctx ==> wf_invoke_targets ctx
Proof
  rw[fmp_lowered_context_wf_def, wf_invoke_targets_def] >>
  res_tac >> gvs[invoke_layout_wf_def] >>
  imp_res_tac lookup_function_mem >> gvs[ctx_fn_names_def]
QED

Theorem entry_not_reachable_callee[local]:
  ctx_wf ctx /\ wf_invoke_targets ctx /\ reachable_call_graph_acyclic ctx /\
  ctx.ctx_entry = SOME entry /\ MEM entry (ctx_fn_names ctx) /\
  MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label entry :: args ==>
  ~MEM f.fn_name (fcg_analyze ctx).fcg_reachable
Proof
  rpt strip_tac >>
  `lookup_function f.fn_name ctx.ctx_functions = SOME f`
    by (irule fmp_lookup_function_self >>
        gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `fn_directly_calls ctx f.fn_name entry`
    by (simp[fn_directly_calls_def] >> metis_tac[]) >>
  `fcg_path ctx entry f.fn_name`
    by (drule fcg_analyze_reachable_sound >>
        disch_then (qspec_then `f.fn_name` mp_tac) >>
        simp[fcg_is_reachable_def]) >>
  `TC (fn_directly_calls ctx) entry entry`
    by (irule EXTEND_RTC_TC_RIGHT1 >> qexists_tac `f.fn_name` >>
        fs[fcg_path_def]) >>
  `fcg_is_reachable (fcg_analyze ctx) entry`
    by (irule fcg_analyze_reachable_complete >>
        simp[fcg_path_def, RTC_REFL]) >>
  mp_tac (Q.INST [`fcg` |-> `fcg_analyze ctx`, `name` |-> `entry`]
            reachable_fcg_acyclic_no_reachable_cycle) >>
  simp[GSYM reachable_call_graph_acyclic_def]
QED

Theorem codegen_invoke_targets_retpc:
  unit_shape_ok unit /\ codegen_context_obligations Inv unit.cu_context cp ==>
  !f inst callee_name args callee.
    MEM f unit.cu_context.ctx_functions /\
    MEM f.fn_name (fcg_analyze unit.cu_context).fcg_reachable /\
    MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee_name :: args /\
    lookup_function callee_name unit.cu_context.ctx_functions = SOME callee ==>
    fn_has_retpc callee
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?fe rest. unit.cu_context.ctx_functions = fe :: rest /\
             unit.cu_context.ctx_entry = SOME fe.fn_name`
    by gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `ctx_wf unit.cu_context /\ codegen_ready unit.cu_context /\
   fmp_lowered_context_wf unit.cu_context /\
   reachable_call_graph_acyclic unit.cu_context`
    by fs[codegen_context_obligations_def] >>
  `wf_invoke_targets unit.cu_context`
    by metis_tac[fmp_lowered_wf_invoke_targets] >>
  `MEM fe.fn_name (ctx_fn_names unit.cu_context)`
    by simp[ctx_fn_names_def] >>
  Cases_on `fe.fn_name = callee_name`
  >- (qpat_x_assum `fe.fn_name = callee_name`
        (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
      drule_all entry_not_reachable_callee >> simp[]) >>
  `MEM callee rest`
    by (qpat_x_assum `lookup_function _ _ = _` mp_tac >>
        simp[lookup_function_def, FIND_thm] >> metis_tac[FIND_MEM]) >>
  irule retpc_param_has_retpc >>
  gvs[codegen_ready_def, codegen_ready_fn_def, EVERY_MEM]
QED

Theorem entry_fn_entry_state_rel_tail:
  initial_ctx_rel_tail tail cp prog ctx vs es /\
  ctx.ctx_functions = fe :: rest /\
  get_params (HD fe.fn_blocks).bb_instructions = [] /\
  fn_entry_label fe = SOME lbl ==>
  fn_entry_state_rel cp fe
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (entry_asm_state vs es) ra []
Proof
  rw[initial_ctx_rel_tail_def, initial_ctx_rel_def] >>
  gvs[initial_state_rel_def, stack_params_rel_def, initial_codegen_state_rel_def,
      fn_entry_label_def, entry_block_def, LENGTH_NIL_SYM] >>
  simp[fn_entry_state_rel_def, entry_asm_state_def, fn_has_retpc_def,
       shared_state_rel_def, venom_asm_terminal_rel_def]
QED

(*
 * The Venom-to-assembly half of codegen_correct (S7): the context's run
 * from its entry is simulated by the generated assembly, started in the
 * entry assembly state of the EVM frame.
 *
 * TOP-LEVEL:
 *   codegen_entry_asm_sim - run_context against asm_steps from
 *                           entry_asm_state
 *)

Theory codegenEntrySim
Ancestors
  codegenEntryRel venomToAsmProps frameRel codegenRel contextCodegenRel
  codegen asmSem venomExecSemantics venomState
  unitShapeDefs stackPlanGen stackOpSim fnPlanPlaceFnRegion
  callLayoutDefs fmpWfDefs venomWf venomInst
  venomExecProps venomRetProps fmpLowerProps
  fcgDefs fcgAnalysisProps fcgPostorder relation list rich_list

(* venomRetProps' ancestors bring in verifereum's cp constant. *)
val _ = Parse.hide "cp";

(* The first region's code opens the program: codegen_assembly emits the
   regions in order, with nothing before them. *)
Theorem codegen_assembly_first_region[local]:
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

(* codegen_ready's return-PC clause (fn_retpc_param) gives frameRel's
   fn_has_retpc. *)
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

(* A reachable function that INVOKEs the entry closes a reachable cycle. *)
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

(* gen_fn_simulation's INVOKE premise: a reachable caller never calls the
   entry, and every other function takes a return PC. *)
Theorem codegen_invoke_targets_retpc[local]:
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

(* The entry function has no return instruction: entry_fn_no_ret rules out
   RET, and codegen readiness the raw FMP returns. *)
Theorem entry_no_ret_opcodes[local]:
  entry_fn_no_ret func /\ codegen_ready_fn func ==>
  EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts func)
Proof
  rw[entry_fn_no_ret_def, codegen_ready_fn_def, EVERY_MEM, fn_insts_def] >>
  `!bbs. MEM inst (fn_insts_blocks bbs) ==>
         ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions`
    by (Induct >> rw[fn_insts_blocks_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> res_tac >>
  gvs[codegen_ready_inst_def, is_pre_codegen_opcode_def,
      is_unlowered_fmp_opcode_def] >>
  rpt strip_tac >> gvs[is_raw_fmp_opcode_def]
QED

(* entry_asm_state meets the entry relation of the first function, with no
   return address and nothing below the (empty) parameter block. *)
Theorem entry_fn_entry_state_rel[local]:
  initial_ctx_rel_tail gas_tail cp prog ctx vs es /\
  ctx.ctx_functions = fe :: rest /\
  get_params (HD fe.fn_blocks).bb_instructions = [] /\
  fn_entry_label fe = SOME lbl ==>
  fn_entry_state_rel cp fe
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (entry_asm_state vs es) ra []
Proof
  rw[codegenEntryRelTheory.initial_ctx_rel_tail_def] >>
  gvs[initial_state_rel_def, stack_params_rel_def, initial_codegen_state_rel_def,
      fn_entry_label_def, entry_block_def, LENGTH_NIL_SYM] >>
  simp[fn_entry_state_rel_def, entry_asm_state_def, fn_has_retpc_def,
       shared_state_rel_def, venom_asm_terminal_rel_def]
QED

(* Why it should hold: run_context runs the entry function (the first
   function: initial_ctx_rel and the planner's layout put its region at
   assembly index 0) with run_function, so this is gen_fn_simulation for
   it, with no return address (entry_fn_no_ret, from
   codegen_context_obligations, also rules out IntRet).  entry_asm_state
   meets fn_entry_state_rel: initial_ctx_rel gives the empty variable map,
   the parameter count (stack_params_rel with no variables: none, and
   an empty stack), the memory relation and the shared fields.  The
   remaining gen_fn_simulation premises come from codegen_context_obligations,
   codegen_reachability_package and initial_ctx_rel's label agreement. *)
Theorem codegen_entry_asm_sim_tail:
  !fuel rpolicy unit cp prog Inv vs es gas_tail.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel_tail gas_tail cp prog unit.cu_context vs es
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmHalt as' /\
         venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >>
  `?fe rest. unit.cu_context.ctx_functions = fe :: rest /\
             unit.cu_context.ctx_entry = SOME fe.fn_name`
    by gvs[unit_shape_ok_def, entry_fn_first_def] >>
  `lookup_function fe.fn_name unit.cu_context.ctx_functions = SOME fe`
    by simp[lookup_function_def, FIND_thm] >>
  `entry_fn_no_ret fe /\ get_params (HD fe.fn_blocks).bb_instructions = []`
    by gvs[unit_shape_ok_def] >>
  `ctx_wf unit.cu_context /\ codegen_ready unit.cu_context`
    by fs[codegen_context_obligations_def] >>
  `EVERY (\inst. ~MEM inst.inst_opcode [RET; RETFMP; DRET]) (fn_insts fe)`
    by (irule entry_no_ret_opcodes >> gvs[codegen_ready_def]) >>
  conj_tac
  >- (rpt gen_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
      gvs[]) >>
  `?lbl. fn_entry_label fe = SOME lbl /\ reachability_closed Inv unit.cu_context /\
         fn_entry_inv Inv unit.cu_context fe
           (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                       vs_inst_idx := 0 |>)`
    by gvs[codegen_reachability_package_def] >>
  `run_context fuel unit.cu_context vs =
   run_blocks fuel unit.cu_context fe
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)`
    by simp[run_context_def, run_function_def, lookup_function_def, FIND_thm] >>
  `0 < LENGTH cp.cp_regions`
    by metis_tac[context_region_leading_label, listTheory.LENGTH,
                 prim_recTheory.LESS_0, listTheory.EL] >>
  `?r rs. cp.cp_regions = r :: rs` by (Cases_on `cp.cp_regions` >> gvs[]) >>
  `MEM fe.fn_name (fcg_analyze unit.cu_context).fcg_reachable`
    by (mp_tac (Q.SPECL [`unit.cu_context`, `fe.fn_name`, `fe.fn_name`]
                  fcg_analyze_reachable_complete) >>
        simp[fcg_is_reachable_def, fcg_path_def, ctx_fn_names_def]) >>
  mp_tac codegen_invoke_targets_retpc >> impl_tac >- simp[] >> strip_tac >>
  `!l. FLOOKUP vs.vs_labels l =
       OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)`
    by gvs[initial_ctx_rel_def, codegenEntryRelTheory.initial_ctx_rel_tail_def] >>
  `~vs.vs_call_ctx.cc_static`
    by gvs[initial_ctx_rel_def, codegenEntryRelTheory.initial_ctx_rel_tail_def, initial_state_rel_def, msg_ctx_rel_def] >>
  `asm_block_at prog 0 (execute_plan cp.cp_initial_fmp r.sr_plan)`
    by metis_tac[codegen_assembly_first_region] >>
  `fn_entry_state_rel cp fe
     (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
     (entry_asm_state vs es) 0w []`
    by (irule entry_fn_entry_state_rel >> metis_tac[]) >>
  mp_tac (Q.SPECL [`fuel`, `rpolicy`, `unit`, `cp`, `prog`, `unit.cu_context`,
                   `SND (compute_label_offsets prog)`, `build_offset_to_pc prog`,
                   `0`, `r`, `fe`,
                   `vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                               vs_inst_idx := 0 |>`,
                   `entry_asm_state vs es`, `Inv`, `0w`, `0`, `[]`]
            gen_fn_simulation) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[entry_asm_state_def, fn_has_retpc_def]) >>
  strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  res_tac >> metis_tac[]
QED

Theorem codegen_entry_asm_sim:
  !fuel rpolicy unit cp prog Inv vs es.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmHalt as' /\
         venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
Proof
  rpt strip_tac >>
  `initial_ctx_rel_tail [] cp prog unit.cu_context vs es` by
    fs[initial_ctx_rel_def] >>
  drule_all codegen_entry_asm_sim_tail >> simp[]
QED

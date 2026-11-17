(* Relocated, fixed-own-code symbolic boundary assembly. *)
Theory symFrameBoundaryOwn
Ancestors
  symFrameBoundaryNumeric symFrameBoundaryPhiPackaging symFrameBoundaryEntryPackaging
  symFrameBoundaryPairing
  fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary
  codegenSymRel asmSymBridge asmSymSem frameRel contextCodegenRel codegenRel
  unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics
  venomState venomInst dfgDefs symShuffleSim reorderStages codegenSymOwnRel

Theorem sym_phi_run_prefix_frame_own:
  !allow_own own todo done base fn bb pred entry source final ra lo m ps cs top rest body
    block_len dfg cfg halt ops last prog o2pc cp ctx ret srest env ss labs0.
  code_labels_agree prog lo /\
  o2pc = build_offset_to_pc prog /\ asm_static_wf prog /\
  phi_run_context fn bb pred entry source final /\
  collect_phis bb.bb_instructions = done ++ todo /\
  phi_run_config fn ra lo base pred entry source m done todo ps
    (cs with as_stack := top) /\
  cs.as_stack = top ++ rest /\
  block_len = LENGTH done + LENGTH (todo ++ body) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halt 0 block_len (LENGTH done) (LENGTH todo) (todo ++ body) ps = SOME (ops,last) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM fn ctx.ctx_functions /\ label_flow_own_ok ctx /\
  (!b. last.ps_alloc.sa_spill_base <= b /\ b < last.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ closure_spill_byte ctx cp fn.fn_name b) /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
  ?endpoint out.
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs =
      AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
    endpoint.as_pc = cs.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    phi_run_config fn ra lo base pred entry source m (done ++ todo) [] last endpoint /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK out /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 last
      (endpoint with as_stack := endpoint.as_stack ++ rest) out
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss` >>
  `sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = cs.as_pc` by
    gvs[sym_frame_inv_own_def, asm_sym_rel_own_def] >>
  `asm_block_at prog (cs with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp ops)` by simp[] >>
  `ss.sym_base.as_pc = (cs with as_stack := top).as_pc` by simp[] >>
  drule_all paired_phi_run_prefix_legacy_own >>
  disch_then (qspecl_then [`o2pc`, `env`] strip_assume_tac) >>
  drule_all sym_frame_inv_local_same_count_own >> strip_tac >>
  qexistsl [`st'`, `out`] >> simp[sym_steps_mode_ok]
QED

Theorem allocator_interval_own_spill:
  !ctx cp fn r ps b.
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    ps.ps_alloc.sa_spill_base <= b /\ b < ps.ps_alloc.sa_next_offset ==>
    context_spill_byte cp b /\ closure_spill_byte ctx cp fn.fn_name b
Proof
  rpt strip_tac >>
  `r.sr_spill_base <= b /\ b < r.sr_spill_end` by decide_tac >>
  metis_tac[contextCodegenRelPropsTheory.context_spill_byte_of_region,
            genFrameSimTheory.closure_spill_byte_own]
QED

Theorem sym_clean_stack_plan_frame_sim_own:
  !allow_own own ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0 env ret srest labs0 ss.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops) /\
    asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss
    ==>
    ?as2 ss2.
      asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled) /\
      sym_steps_mode allow_own prog env own (LENGTH (execute_plan cp.cp_initial_fmp clean_ops)) ss = SymOK ss2 /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps2 as2 ss2
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  drule_all fnFrameCleanStackTheory.clean_stack_plan_frame_sim_reloc >> strip_tac >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  `sym_kinds_ok cplan fn ret srest ps ss` by fs[sym_frame_inv_own_def] >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan cplan.cp_initial_fmp clean_ops)` by
    gvs[sym_frame_inv_own_def, asm_sym_rel_own_def] >>
  `!b. ps2.ps_alloc.sa_spill_base <= b /\ b < ps2.ps_alloc.sa_next_offset ==>
    context_spill_byte cplan b /\ closure_spill_byte ctx cplan fn.fn_name b` by
    (gen_tac >> strip_tac >> drule_all allocator_interval_own_spill >> simp[]) >>
  drule_all sym_clean_stack_plan_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexistsl [`as2`, `out`] >>
  irule sym_clean_stack_plan_frame_of_runs_own >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem sym_entry_prefix_asm_own:
  !allow_own own ctx cp lo o2pc prog liveness fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs a ra rest vp env ret srest ss.
    code_labels_agree prog lo /\
    o2pc = build_offset_to_pc prog /\ liveness = liveness_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs a ra rest /\
    vp = (entry_bind_pairs
      (entry_param_pairs vs (get_params (HD fn.fn_blocks).bb_instructions)) vs
      with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) /\
    asm_block_at prog a.as_pc (execute_plan cp.cp_initial_fmp
      (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    asm_static_wf prog /\ asm_sym_rel_own lo prog env own a ss /\
    ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
    ?a' ss'.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan cp.cp_initial_fmp
          (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) a = AsmOK a' /\
      a'.as_pc = a.as_pc + LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest a.as_memory ps1 vp a' /\
      sym_steps_mode allow_own prog env own
        (LENGTH (execute_plan cp.cp_initial_fmp
          (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))) ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest ss.sym_mem_labels ps1 a' ss'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_entry_state_rel cplan fn vs a ra rest` >>
  qmatch_asmsub_abbrev_tac `LENGTH params < dimword (:256)` >>
  qabbrev_tac `installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params` >>
  `sym_kinds_ok cplan fn ret srest installed ss` by
    metis_tac[Abbr `installed`, Abbr `params`, fn_entry_state_rel_def, entry_installed_sym_kinds] >>
  `sym_frame_inv_own lo prog env own ctx cplan fn ret srest ss.sym_mem_labels installed a ss` by
    simp[sym_frame_inv_own_def] >>
  `r.sr_spill_base <= ps1.ps_alloc.sa_spill_base` by
    (drule allocMonoTheory.prepare_params_plan_spill_base >>
     gvs[init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]) >>
  `!b. ps1.ps_alloc.sa_spill_base <= b /\ b < ps1.ps_alloc.sa_next_offset ==>
    context_spill_byte cplan b /\ closure_spill_byte ctx cplan fn.fn_name b` by
    (rpt strip_tac >> metis_tac[allocator_interval_own_spill]) >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan cplan.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))` by gvs[asm_sym_rel_own_def] >>
  `params = get_params (HD fn.fn_blocks).bb_instructions /\
   installed = ps0 with ps_stack := MAP (\i. Var (HD i.inst_outputs)) params` by
    simp[Abbr `params`, Abbr `installed`] >>
  drule_all sym_label_prepare_numeric >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  fs[Abbr `params`] >> drule_all entry_prefix_asm_exact_reloc >>
  disch_then (qspecl_then [`ctx`, `lo`] strip_assume_tac) >>
  `sym_frame_inv_own lo prog env own ctx cplan fn ret srest ss.sym_mem_labels ps1 a' out` by
    (irule sym_frame_inv_same_count_own >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl [`a'`, `out`] >> simp[sym_steps_mode_ok] >> metis_tac[]
QED

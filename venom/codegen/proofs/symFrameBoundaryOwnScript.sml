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

Theorem block_phi_plan_split:
  !liveness dfg cfg fn lbl halt np bl phis body ps ops last prog pc fmp r.
  generate_block_insts_plan liveness dfg cfg fn lbl halt np bl 0
    (phis ++ body) ps = SOME (ops,last) /\
  r.sr_spill_base <= last.ps_alloc.sa_spill_base /\
  last.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
    off < dimword(:256)) /\
  asm_block_at prog pc (execute_plan fmp ops) ==>
  ?pre mid post.
    ops = pre ++ post /\
    generate_block_insts_prefix liveness dfg cfg fn lbl halt np bl 0
      (LENGTH phis) (phis ++ body) ps = SOME (pre,mid) /\
    generate_block_insts_plan liveness dfg cfg fn lbl halt np bl
      (LENGTH phis) body mid = SOME (post,last) /\
    r.sr_spill_base <= mid.ps_alloc.sa_spill_base /\
    mid.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) pre /\
    asm_block_at prog pc (execute_plan fmp pre)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generate_block_insts_plan _ _ _ _ _ _ _ _ _ (phis ++ suffix) _ = _` >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qspecl_then [`LENGTH phis`, `phis ++ suffix`] mp_tac
    fnPlanPrefixTheory.generate_block_insts_plan_split >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => CONV_TAC (LAND_CONV (REWR_CONV (SPEC_ALL th)))) >>
  simp_tac (srw_ss()) [listTheory.DROP_APPEND] >> strip_tac >>
  drule allocMonoTheory.generate_block_insts_plan_spill_base >> strip_tac >>
  drule allocMonoTheory.generate_block_insts_plan_next_offset >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append] >>
  simp[listTheory.EVERY_MEM] >> Cases >> simp[] >> metis_tac[listTheory.MEM_APPEND]
QED

Theorem phi_hits_run_context:
  !fn bb pred ps vs final dfg.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
  bb <> HD fn.fn_blocks /\ vs.vs_prev_bb = SOME pred /\
  eval_phis vs bb.bb_instructions = OK final /\
  (!inst op. MEM inst (collect_phis bb.bb_instructions) /\
     is_var_operand op /\ MEM op inst.inst_operands /\ MEM op ps.ps_stack ==>
     resolve_phi pred inst.inst_operands = SOME op) /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
     ~(MEM op ps.ps_stack /\ ?inst.
       MEM inst (collect_phis bb.bb_instructions) /\
       resolve_phi pred inst.inst_operands = SOME op) /\
     (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
     ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) ==>
  phi_run_context fn bb pred ps vs final
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  rewrite_tac[fnFrameStepsPhiTheory.phi_run_context_def] >>
  simp[fnFrameStepsPhiTheory.phi_eval_collect] >>
  rpt gen_tac >> disch_tac >>
  irule fnFrameStepsPhiTheory.phi_entry_outputs_absent >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem phi_run_final_frame:
  !ctx cp lo fn ra rest mem0 ps vs st last final endpoint bb base pred k r.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  phi_run_context fn bb pred ps vs final /\
  phi_run_config fn ra lo base pred ps vs st.as_memory
    (collect_phis bb.bb_instructions) [] last endpoint /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= last.ps_alloc.sa_spill_base /\
  last.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  fn_frame_inv ctx cp lo fn ra rest mem0 last (final with vs_inst_idx := k)
    (endpoint with as_stack := endpoint.as_stack ++ rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameStepsPhiTheory.phi_run_final >> strip_tac >>
  irule fnFrameStepsPhiTheory.phi_local_frame_transport >>
  gvs[fnFrameStepsPhiTheory.phi_run_context_def] >> metis_tac[]
QED

Theorem phi_frame_run_init:
  !ctx cp lo fn ra rest mem0 ps vs st base pred phis.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generated_plan_state_wf_marked base ps ==>
  ?top. st.as_stack = top ++ rest /\
    phi_run_config fn ra lo base pred ps vs st.as_memory [] phis ps
      (st with as_stack := top)
Proof
  rpt gen_tac >> strip_tac >>
  drule fnFrameTerminalPrepTheory.fn_frame_inv_local_state >> strip_tac >>
  qexists `top` >> simp[] >> irule fnFrameStepsPhiTheory.phi_run_init >>
  gvs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def]
QED

Theorem sym_phi_prefix_hits_frame_sim_exact_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg fn bb pred base ps vs as s_phi phis
   body ops ps3 r ra rest mem0 env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    (!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
      MEM op ps.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op) /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
        resolve_phi pred inst.inst_operands = SOME op) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
      (phis ++ body) ps = SOME (ops,ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (LENGTH phis) (phis ++ body) ps = SOME (phi_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (LENGTH phis) body ps1 = SOME (body_ops,ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        operand_val (frame_view fn ra s_phi) lo at =
        operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp phi_ops)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  rename1 `generated_plan_state_wf_marked bound ps` >>
  rename1 `non_param_insts bb = phis ++ suffix` >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  drule_all fnPlanPrefixTheory.nonentry_block_no_params >> strip_tac >>
  `phis = collect_phis bb.bb_instructions` by
    metis_tac[fnFrameStepsPhiTheory.phi_prefix_is_collect_phis] >>
  `phi_run_context fn bb pred ps vs s_phi` by
    (irule phi_hits_run_context >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all block_phi_plan_split >> strip_tac >>
  drule_all phi_frame_run_init >>
  disch_then (qspecl_then [`pred`, `phis`] strip_assume_tac) >>
  `!b. mid.ps_alloc.sa_spill_base <= b /\ b < mid.ps_alloc.sa_next_offset ==>
    context_spill_byte cplan b /\ closure_spill_byte ctx cplan fn.fn_name b` by
    metis_tac[allocator_interval_own_spill] >>
  `collect_phis bb.bb_instructions = [] ++ phis` by simp[] >>
  `LENGTH bb.bb_instructions = LENGTH [] + LENGTH (phis ++ suffix)` by
    metis_tac[listTheory.LENGTH, arithmeticTheory.ADD] >>
  `generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) (LENGTH []) (LENGTH phis)
    (phis ++ suffix) ps = SOME (pre,mid)` by metis_tac[listTheory.LENGTH] >>
  `?endpoint out.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (endpoint with as_stack := endpoint.as_stack ++ rest) /\
    endpoint.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pre) /\
    phi_run_config fn ra lo bound pred ps vs st.as_memory ([] ++ phis) [] mid endpoint /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK out /\
    sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 mid
      (endpoint with as_stack := endpoint.as_stack ++ rest) out` by
    (irule (INST_TYPE [``:'a`` |-> ``:cfg_analysis``] sym_phi_run_prefix_frame_own) >>
     goal_assum (drule_at Any) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexists `bb` >> qexists `LENGTH bb.bb_instructions` >>
     qexists `suffix` >> qexists `cfg` >> qexists `dfg` >>
     qexists `s_phi` >> qexists `bb_is_halting bb` >>
     qexists `ps` >> qexists `top` >>
     metis_tac [listTheory.LENGTH]) >>
  `phi_run_config fn ra lo bound pred ps vs st.as_memory
     (collect_phis bb.bb_instructions) [] mid endpoint` by
    metis_tac[listTheory.APPEND] >>
  drule_all phi_run_final_frame >>
  disch_then (qspec_then `LENGTH phis` assume_tac) >>
  `!at. MEM at mid.ps_stack \/ at IN FDOM mid.ps_spilled ==>
     operand_val (frame_view fn ra s_phi) lo at =
     operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)` by
    (rpt gen_tac >> disch_tac >>
     irule fnFrameStepsPhiTheory.phi_run_final_alias >>
     goal_assum (drule_at Any) >>
     qpat_assum `phi_run_config _ _ _ _ _ _ _ _ (collect_phis _) [] mid endpoint`
       (irule_at Any) >> metis_tac[]) >>
  qexistsl [`pre`, `mid`, `post`,
    `LENGTH (execute_plan cplan.cp_initial_fmp pre)`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`, `out`] >>
  pure_rewrite_tac [asmSemTheory.asm_state_accfupds] >>
  rpt conj_tac >> metis_tac[]
QED

Theorem sym_phi_prefix_hits_frame_sim_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg fn bb pred base ps vs as s_phi phis
   body ops ps3 r ra rest mem0 env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    (!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
      MEM op ps.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op) /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
        resolve_phi pred inst.inst_operands = SOME op) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword(:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
      operand_val (frame_view fn ra vs) lo at =
      operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
      (phis ++ body) ps = SOME (ops,ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
        (LENGTH phis) (phis ++ body) ps = SOME (phi_ops,ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (LENGTH phis) body ps1 = SOME (body_ops,ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        operand_val (frame_view fn ra s_phi) lo at =
        operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sym_phi_prefix_hits_frame_sim_exact_own >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_phi_prefix_frame_sim_exact_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\ ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\ non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1 (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp phi_ops)
Proof
  rpt gen_tac >> strip_tac >>
  `!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
     MEM op ps.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op` by
    metis_tac[fnFrameStepsPhiTheory.phi_join_entry_hits] >>
  `!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
     ~(MEM op ps.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
       resolve_phi pred inst.inst_operands = SOME op) /\
     (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
     ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (match_mp_tac fnFrameStepsPhiTheory.phi_join_entry_fresh >> metis_tac[]) >>
  match_mp_tac sym_phi_prefix_hits_frame_sim_exact_own >>
  qpat_assum `generated_plan_state_wf_marked bound ps` (irule_at Any) >>
  qexistsl [`vs`, `r`, `pred`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_phi_prefix_frame_sim_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb pred
   ps_l h promised ps base vs as s_phi phis body ops ps3 r ra rest mem0
   env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands) (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\ ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==> off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\ non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
    asm_static_wf prog /\ sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp phi_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1 (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_phi_prefix_frame_sim_exact_own >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_single_pred_prefix_frame_sim_exact_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0 env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\ ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/ MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\ non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1 (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss' /\
      n = LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `MEM bb.bb_label (cfg_succs_of cfg pred)` by
    (qpat_x_assum `lineage_entry _ _ _ _ _ _ _ _` mp_tac >>
     simp[fnPlanLineageTheory.lineage_entry_def] >> strip_tac) >>
  `ps2.ps_alloc.sa_spill_base = ps3.ps_alloc.sa_spill_base /\
   ps2.ps_alloc.sa_next_offset <= ps3.ps_alloc.sa_next_offset` by
    (drule allocMonoTheory.generate_block_insts_plan_spill_base >>
     drule allocMonoTheory.generate_block_insts_plan_next_offset >> simp[]) >>
  qpat_x_assum `asm_block_at _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append]) >>
  `r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
   ps2.ps_alloc.sa_next_offset <= r.sr_spill_end` by simp[] >>
  `!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
    off < dimword (:256)` by metis_tac[listTheory.MEM_APPEND] >>
  `!off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
    off < dimword (:256)` by metis_tac[listTheory.MEM_APPEND] >>
  drule_all sym_clean_stack_plan_frame_sim_own >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  `!inst op. MEM inst phis /\ is_var_operand op /\ MEM op inst.inst_operands /\
     MEM op ps2.ps_stack ==> resolve_phi pred inst.inst_operands = SOME op` by
    metis_tac[fnFrameSinglePredTheory.single_pred_phi_operand_hits] >>
  `normalize_operand dfg [] dead_stack_marker = dead_stack_marker` by
    simp[stackPlanGenTheory.dead_stack_marker_def, normalize_operand_def] >>
  `!op v. (MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled) /\
     ~(MEM op ps2.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
       resolve_phi pred inst.inst_operands = SOME op) /\
     (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
     ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[operand_distinct, stackPlanGenTheory.dead_stack_marker_def] >>
  `!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)` by metis_tac[] >>
  rename1 `non_param_insts bb = phis ++ suffix` >>
  `asm_block_at prog as2.as_pc (execute_plan cplan.cp_initial_fmp ops)` by metis_tac[] >>
  `?phi_ops ps1 body_ops n as' ss'.
     ops = phi_ops ++ body_ops /\
     generate_block_insts_prefix liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
       (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions) 0
       (LENGTH phis) (phis ++ suffix) ps2 = SOME (phi_ops,ps1) /\
     generate_block_insts_plan liveness dfg cfg fn bb.bb_label (bb_is_halting bb)
       (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
       (LENGTH phis) suffix ps1 = SOME (body_ops,ps3) /\
     asm_steps lo o2pc prog n as2 = AsmOK as' /\
     as'.as_pc = as2.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp phi_ops) /\
     fn_frame_inv ctx cplan lo fn ra rest mem0 ps1 (s_phi with vs_inst_idx := LENGTH phis) as' /\
     (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
       operand_val (frame_view fn ra s_phi) lo at =
       operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
     sym_steps_mode allow_own prog env own n ss2 = SymOK ss' /\
     sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps1 as' ss' /\
     n = LENGTH (execute_plan cplan.cp_initial_fmp phi_ops)` by
    (match_mp_tac sym_phi_prefix_hits_frame_sim_exact_own >>
     qpat_assum `generated_plan_state_wf_marked bound ps2` (irule_at Any) >>
     qexistsl [`vs`, `r`, `pred`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`phi_ops`, `ps1`, `body_ops`,
    `LENGTH (execute_plan cplan.cp_initial_fmp clean_ops) + n`, `as'`, `ss'`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (once_rewrite_tac[stackOpSimTheory.asm_steps_add] >> gvs[])) >>
  (conj_tac >- (rewrite_tac[stackOpSimTheory.execute_plan_append,
    listTheory.LENGTH_APPEND] >> metis_tac[arithmeticTheory.ADD_ASSOC])) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (once_rewrite_tac[sym_steps_mode_add] >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[stackOpSimTheory.execute_plan_append]
QED

Theorem sym_single_pred_prefix_frame_sim_own:
  !allow_own own ctx cp lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised ps base vs as s_phi clean_ops ps2 phis body ops ps3
   r ra rest mem0 env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    LENGTH (cfg_preds_of cfg bb.bb_label) = 1 /\ vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps_l /\
    ps = ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |> /\
    generated_plan_state_wf_marked base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\ ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/ MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\ non_param_insts bb = phis ++ body /\
    LENGTH phis = phi_prefix_length bb.bb_instructions /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (phis ++ body) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp (clean_ops ++ ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    ?phi_ops ps1 body_ops n as' ss'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (LENGTH phis) (phis ++ body) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (LENGTH phis) body ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps1 (s_phi with vs_inst_idx := LENGTH phis) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >> drule_all sym_single_pred_prefix_frame_sim_exact_own >>
  disch_then (qspec_then `allow_own` strip_assume_tac) >>
  qexistsl [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`, `ss'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_entry_prefix_frame_sim_own:
  !allow_own own fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv env ret srest ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\ ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
    asm_static_wf prog /\ asm_sym_rel_own lo prog env own as ss /\
    ss.sym_stack = (if fn_has_retpc fn then [Lab ret 0] else []) ++
      MAP Val (REVERSE vs.vs_params) ++ srest /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
    ?n as' vs_p ss'.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp
        (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\ vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at)) /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
      sym_frame_inv_own lo prog env own ctx cp fn ret srest ss.sym_mem_labels ps1 as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `vp = entry_bind_pairs
    (entry_param_pairs vs (get_params (HD fn.fn_blocks).bb_instructions)) vs
    with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` >>
  `vp = entry_bind_pairs
    (entry_param_pairs vs (get_params (HD fn.fn_blocks).bb_instructions)) vs
    with vs_inst_idx := LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by simp[Abbr `vp`] >>
  drule_all sym_entry_prefix_asm_own >>
  disch_then (qspecl_then [`allow_own`, `ctx`] strip_assume_tac) >>
  drule entry_prefix_inv >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspec_then `LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` mp_tac) >>
  disch_then (assume_tac o SIMP_RULE bool_ss [listTheory.TAKE_LENGTH_ID, arithmeticTheory.LESS_EQ_REFL]) >>
  `exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
   exec_block fuel ctx (HD fn.fn_blocks) vp` by
    (simp[Abbr `vp`] >> metis_tac[fnFrameBoundaryEntryParamsTheory.bounded_entry_param_skip]) >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
    normalize_operand dfg [] at = at` by metis_tac[entry_plan_normalize] >>
  qexistsl [`LENGTH (execute_plan cp'.cp_initial_fmp
    (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))`, `a'`, `vp`, `ss'`] >>
  gvs[Abbr `vp`, fnFrameBoundaryEntryParamsTheory.entry_bind_pairs_normal] >>
  rpt strip_tac >> simp[]
QED

(* Relocated successor entry and paired symbolic jump prefixes. *)
Theory symBodyJumpOwn
Ancestors
  symBodyJumpPointwise symFrameControlOwn symFnSimSpec fnBlockBodyClasses fnBlockBodySteps
  fnBlockBodyHelpers contextCodegenRelProps fnBlockPlanStaticRegion
  fnPlanLineageEntryProduction codegenSymRel codegenSymOwnRel fnAliasStep
  frameRel contextCodegenRel codegenRel unitShapeDefs venomExecSemantics
  venomState venomInst asmSymBridge asmSymSem

Theorem body_step_entry_inv_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst vs = OK vs1 /\
  ~vs1.vs_halted ==>
  fn_entry_inv Inv ctx fn vs1
Proof
  strip_tac >> drule_all body_inv_inst_reloc >> strip_tac >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  pure_rewrite_tac [fn_entry_inv_def] >> rpt strip_tac >>
  irule reachability_closed_block >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem body_jump_entry_lineage_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  MEM t (cfg_succs_of cfg bb.bb_label) /\
  dfs_block_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) t ps_tdfs ==>
  lineage_entry liveness dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label t
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>)
Proof
  strip_tac >> drule body_inv_facts_reloc >> strip_tac >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  `ps_dfs_after.ps_spilled = ps_tdfs.ps_spilled` by
    (irule dfs_edge_spilled >> simp[] >> metis_tac[]) >>
  pure_rewrite_tac [fnPlanLineageTheory.lineage_entry_def] >>
  qexistsl [`ps_l`, `bb`, `ps_dfs`, `block_ops`, `ps_dfs_after`, `h`,
               `promised`, `ps_after`, `ps_tdfs`] >> simp[] >>
  qexistsl [`prefixL`, `prefixD`, `core`] >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem body_jump_entry_frame_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  ps_tdfs.ps_alloc.sa_spill_base = spill_base /\
  ps_tdfs.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 ==>
  fn_frame_inv ctx cpl lo fn ra rest mem0
    (ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>) vs1 as1
Proof
  strip_tac >> drule body_inv_facts_reloc >> strip_tac >>
  qhdtm_assum `body_inv_reloc`
    (strip_assume_tac o REWRITE_RULE [body_inv_reloc_def]) >>
  irule fn_frame_inv_same_slots >>
  conj_tac >- (qexists `r` >> simp[]) >>
  qexists `ps_after` >> simp[]
QED

Theorem body_jump_entry_reloc_kernel:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc ==>
  ?tbb ps_tdfs tops tafter pe.
    pe = ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |> /\
    ~vs1.vs_halted /\ vs1.vs_labels = vs.vs_labels /\
    vs1.vs_call_ctx = vs.vs_call_ctx /\ vs1.vs_current_bb = t /\
    vs1.vs_prev_bb = SOME bb.bb_label /\ tbb.bb_label = t /\
    lookup_block vs1.vs_current_bb fn.fn_blocks = SOME tbb /\
    tbb <> HD fn.fn_blocks /\ fn_reachable fn tbb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label tbb.bb_label pe /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs1.vs_current_bb ps_tdfs /\
    generate_block_plan liveness dfg cfg fn tbb ps_tdfs = SOME (tops,tafter) /\
    asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 pe vs1 as1 /\
    fn_entry_inv Inv ctx fn vs1 /\
    (!at. MEM at pe.ps_stack \/ at IN FDOM pe.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at))
Proof
  strip_tac >> drule_all body_succ_placed_reloc >> strip_tac >>
  `toff = off /\ tpc = as1.as_pc` by metis_tac[optionTheory.SOME_11] >>
  `~vs1.vs_halted` by gvs[fn_frame_inv_def] >>
  drule_all body_step_entry_inv_reloc_kernel >> strip_tac >>
  drule_all body_jump_entry_lineage_reloc_kernel >> strip_tac >>
  drule_all body_jump_entry_frame_reloc_kernel >> strip_tac >>
  drule body_inv_facts_reloc >> strip_tac >>
  qexistsl [`tbb`, `ps_tdfs`, `tops`, `tafter`,
    `ps_tdfs with <| ps_stack := ps_after.ps_stack;
                     ps_spilled := ps_after.ps_spilled |>`] >>
  simp[] >> gvs[jump_to_def] >> gvs[]
QED

Theorem body_succ_sym_label_reloc_kernel:
  (!bb fn liveness dfg cfg ps ops ps' prog pc initial_fmp.
    bb <> HD fn.fn_blocks /\
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
    asm_block_at prog pc (execute_plan initial_fmp ops) ==>
    MEM (AsmLabel bb.bb_label) prog) /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\ MEM t (get_successors inst) ==>
  ?off pc. FLOOKUP lo t = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc /\ MEM (AsmLabel t) prog
Proof
  strip_tac >> drule_all body_succ_placed_reloc >> strip_tac >>
  metis_tac[]
QED

Theorem sym_body_jmp_prefix_own_kernel:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  (?target. inst.inst_operands = [Label target] /\ inst.inst_outputs = [] /\
    is_terminator inst.inst_opcode /\ MEM target (get_successors inst)) /\
  (!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog) /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> irule sym_body_jmp_prefix_pointwise >> simp[] >> metis_tac[]
QED

Theorem sym_body_jnz_prefix_own_kernel:
  gen_fn_frame_sim_at_simple_reloc fuel /\ sym_fn_frame_sim_at_own allow_own fuel /\
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  inst.inst_opcode = JNZ /\ step_inst fuel ctx inst vs = OK vs1 /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  (?c l1 l2. inst.inst_operands = [c; Label l1; Label l2] /\
    inst.inst_outputs = [] /\ ~is_label_operand c /\
    is_terminator inst.inst_opcode /\ MEM c (compute_operands inst) /\
    MEM l1 (get_successors inst) /\ MEM l2 (get_successors inst)) /\
  (!c l1 l2. inst.inst_operands = [c; Label l1; Label l2] ==>
    eval_operand c vs = eval_operand c (frame_view fn ra vs)) /\
  (!t. MEM t (get_successors inst) ==> MEM (AsmLabel t) prog) /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps as ss ==>
  ?n as1 ss1 t off.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
    (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
    is_terminator inst.inst_opcode /\ MEM t (get_successors inst) /\
    vs1 = jump_to t vs /\
    FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc
Proof
  strip_tac >> irule sym_body_jnz_prefix_pointwise >> simp[] >> metis_tac[]
QED

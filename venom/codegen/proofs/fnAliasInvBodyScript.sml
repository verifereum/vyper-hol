Theory fnAliasInvBody
Ancestors
  fnAliasStep fnBlockPlanStatic fnBlockPlanStaticBodyPrefix
  venomExecProps venomExecSemantics venomWf venomInst stackPlanGen livenessTransferProofs
  removeUnusedSsaProofs list rich_list

(* The lower invariant discharges the static premises of alias transport,
   including the pending inventory at a final jump. *)
Theorem regional_body_alias_step:
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  k < LENGTH bb.bb_instructions /\ inst = EL k bb.bb_instructions /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb k ps /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn inst
    nl halting next_term bb.bb_label ps = SOME (ops,qs) /\
  step_inst fuel ctx inst vs = OK vs1 ==>
  !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo
      (normalize_operand (dfg_build_function fn) [] at)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[]) >>
  `!target target_bb targets. inst.inst_opcode = JMP /\
    inst.inst_operands = [Label target] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    targets = MAP Var (input_vars_from bb.bb_label target_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) target 0)) ==>
    pending_inventory_wf targets ps` by
    (rpt strip_tac >>
     `k = PRE (LENGTH bb.bb_instructions)` by
       (gvs[bb_well_formed_def] >>
        first_x_assum irule >> simp[is_terminator_def]) >>
     `inst = LAST bb.bb_instructions` by
       metis_tac[LAST_EL, bb_well_formed_def] >>
     `fn_cfg_edge fn bb.bb_label target` by
       (simp[fn_cfg_edge_def] >> qexists_tac `bb` >>
        Cases_on `bb.bb_instructions` >- gvs[bb_well_formed_def] >>
        simp[bb_succs_def] >>
        qpat_x_assum `inst = LAST _` (fn th => rewrite_tac[GSYM th]) >>
        simp[get_successors_def, is_terminator_def, venomStateTheory.get_label_def]) >>
     drule_all regional_jmp_target_static >> simp[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)` by
    metis_tac[regional_body_lower_inv_operand_lookup] >>
  `!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v inst.inst_outputs` by
    metis_tac[regional_body_lower_inv_output_roots] >>
  gen_tac >> disch_tac >> irule alias_step_preserve >> simp[] >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

(* The executor and planner consume the same remaining instruction suffix.
   The relative planner index i corresponds to the absolute index i+np. *)
Theorem regional_body_alias_suffix:
  !insts i np ps ops qs vs vs1 fuel ctx lo fn ra bb sb cfg halting.
  codegen_ready_fn fn /\ retpc_shape_ok fn /\
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  DROP (i + np) bb.bb_instructions = insts /\
  vs.vs_inst_idx = i + np /\
  EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode) insts /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (i+np) ps /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn
    bb.bb_label halting np (LENGTH bb.bb_instructions) i insts ps = SOME (ops,qs) /\
  exec_block fuel ctx bb vs = OK vs1 ==>
  !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo
      (normalize_operand (dfg_build_function fn) [] at)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`LENGTH bb.bb_instructions <= vs.vs_inst_idx` by
        gvs[DROP_EQ_NIL] >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def, get_instruction_def]) >>
  `i + np < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `EL (i+np) bb.bb_instructions = h /\
   DROP (SUC (i+np)) bb.bb_instructions = insts` by
    metis_tac[DROP_CONS_EL, CONS_11] >>
  `bb_well_formed bb` by
    (qpat_x_assum `!i np ps ops qs vs vs1 fuel ctx lo fn ra bb sb cfg halting. _` kall_tac >>
     gvs[codegen_ready_fn_def, wf_function_def] >> metis_tac[lookup_block_mem]) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac (std_ss ++ boolSimps.LET_ss) [Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp_tac std_ss [Once exec_block_def, get_instruction_def] >>
  qpat_assum `vs.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `i + np < _` (fn th => rewrite_tac[th]) >>
  qpat_assum `EL (i+np) _ = h` (fn th => rewrite_tac[th]) >>
  simp_tac std_ss [AllCaseEqs()] >> strip_tac >>
  fs[NoAsms, EVERY_DEF] >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
    operand_val (frame_view fn ra s'') lo at =
    operand_val (frame_view fn ra s'') lo
      (normalize_operand (dfg_build_function fn) [] at)` by
    (qpat_x_assum `!i np ps ops qs vs vs1 fuel ctx lo fn ra bb sb cfg halting. _` kall_tac >>
     gen_tac >> disch_tac >> irule regional_body_alias_step >> simp[] >>
     metis_tac[]) >>
  cheat
QED

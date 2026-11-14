(* Instruction dispatch at the height-only planner boundary. *)
Theory staticAbortInst
Ancestors
  staticAbortPlanBoundary staticAbortChunk fnBlockPlanStatic unitShapeDefs
  staticAbortDefs venomWf opcodeClass list arithmetic stackPlanGen venomInst
  staticAbortEmit staticAbortStraight asmIR staticAbortPlacement planExec
  asmSem words stackOpSim staticAbortTrace fnBlockBodySteps prefixExec
  fnPlanPrefix fnPlanPlace

Theorem static_abort_regular_net_io:
  inst_wf inst /\ inst_shape_ok inst /\ codegen_ready_inst inst /\
  ~is_terminator inst.inst_opcode /\
  ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> PHI /\
  ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                        SSTORE;TSTORE;LOG] /\
  LENGTH (compute_operands inst) <= m /\
  h + LENGTH (compute_operands inst) = m + LENGTH inst.inst_outputs ==>
  ?a b. static_abort_emit_io inst a b /\ a <= m /\ h + a = m + b
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inst_wf_def, inst_shape_ok_def, codegen_ready_inst_def,
       is_terminator_def, is_param_opcode_def, is_pre_codegen_opcode_def,
       is_read0_opcode_def] >>
  simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, static_abort_emit_io_def,
       venom_to_evm_name_def] >>
  pure_rewrite_tac[static_abort_straight_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``LENGTH``, ``REVERSE``,
    ``label_positions_ok``]) >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem static_abort_generated_emit_labels:
  !unit cplan rpolicy prog pc emit inst.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  asm_block_at prog pc (execute_plan cplan.cp_initial_fmp emit) ==>
  static_abort_emit_labels (SND (compute_label_offsets prog))
    (build_offset_to_pc prog) prog cplan.cp_initial_fmp pc inst emit
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`rpolicy`, `unit`, `cplan`, `prog`, `unit.cu_context`,
    `SND (compute_label_offsets prog)`, `build_offset_to_pc prog`]
    mp_tac revert_postamble_placed >> simp[] >> strip_tac >>
  drule_all fnPlanPlaceRevertPostambleTheory.codegen_revert_slice >> strip_tac >>
  simp[static_abort_emit_labels_def] >> rpt strip_tac >> gvs[execute_plan_def, exec_stack_op_def] >>
  drule_all assert_unreachable_end_placed >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem static_abort_regular_inst_progress:
  !unit cplan rpolicy prog lv dfg cfg fn inst nl halt term lbl ps ops qs s top rest.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  inst_wf inst /\ inst_shape_ok inst /\ codegen_ready_inst inst /\
  ~is_terminator inst.inst_opcode /\ ~is_param_opcode inst.inst_opcode /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> NOP /\
  ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                        SSTORE;TSTORE;LOG] /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  s.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
  asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  (?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    static_abort_normal (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog q s t /\
    t.as_pc = s.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    LENGTH t.as_stack = LENGTH qs.ps_stack + LENGTH rest /\
    t.as_call_ctx = s.as_call_ctx) \/
  (?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q s t)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> OFFSET /\
   ~is_pre_codegen_opcode inst.inst_opcode /\ LENGTH (compute_operands inst) <= 16` by
    (conj_tac >- (strip_tac >> gvs[is_terminator_def]) >>
     gvs[inst_shape_ok_def, codegen_ready_inst_def]) >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs)` by
    gvs[generate_inst_plan_def] >>
  drule_all regular_plan_admin_decomposition >> strip_tac >>
  drule_all static_abort_regular_net_io >> strip_tac >>
  `asm_block_at prog (s.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp pre))
    (execute_plan cplan.cp_initial_fmp emit)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     simp[execute_plan_append, asm_block_at_append]) >>
  drule_all static_abort_generated_emit_labels >>
  disch_then (qspec_then `inst` assume_tac) >>
  drule_all static_abort_chunk_progress >> simp[]
QED

Theorem static_abort_regular_inst_terminal:
  !unit cplan rpolicy prog lv dfg cfg fn inst nl halt term lbl ps ops qs s top rest.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  inst_wf inst /\ codegen_ready_inst inst /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  s.as_call_ctx.cc_static /\
  s.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
  asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q s t
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI /\
   inst.inst_opcode <> OFFSET /\ inst.inst_opcode <> NOP /\
   ~is_param_opcode inst.inst_opcode /\
   ~is_pre_codegen_opcode inst.inst_opcode /\ LENGTH (compute_operands inst) <= 16` by
    (fs[] >> gvs[codegen_ready_inst_def, is_param_opcode_def]) >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs)` by
    (gvs[generate_inst_plan_def] >> fs[]) >>
  drule_all regular_plan_admin_decomposition >> strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics ps6` >>
  `(inst.inst_opcode = LOG ==> topics <= 4) /\
   (if inst.inst_opcode = LOG then 2 + topics else 2) <= m` by
    (fs[] >> gvs[Abbr `topics`, inst_wf_def, codegen_ready_inst_def,
      compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
      AllCaseEqs()]) >>
  drule_all static_abort_chunk_terminal >> simp[]
QED

Theorem static_abort_inst_progress:
  !unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after height promised block_ops ps_after k ps inst nl term
   ops qs s top rest.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\i. EVERY (\op. op <> dead_stack_marker)
    i.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <| ps_cleanup_height := height; ps_cleanup_promised := promised |>) =
    SOME (block_ops,ps_after) /\
  block_plan_state lv dfg cfg fn bb
    (ps_l with <| ps_cleanup_height := height; ps_cleanup_promised := promised |>) k ps /\
  phi_prefix_length bb.bb_instructions <= k /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = inst /\
  nl = live_vars_at lv bb.bb_label (k + 1) /\
  term = (k + 1 < LENGTH bb.bb_instructions /\
          is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode) /\
  inst_shape_ok inst /\ codegen_ready_inst inst /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                        SSTORE;TSTORE;LOG] /\
  generate_inst_plan lv dfg cfg fn inst nl (bb_is_halting bb) term bb.bb_label ps =
    SOME (ops,qs) /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  s.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
  asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  (?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    static_abort_normal (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
      prog q s t /\
    t.as_pc = s.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    LENGTH t.as_stack = LENGTH qs.ps_stack + LENGTH rest /\
    t.as_call_ctx = s.as_call_ctx) \/
  (?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q s t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all block_plan_state_static >> strip_tac >>
  Cases_on `inst.inst_opcode = NOP`
  >- (fs[generate_inst_plan_def, codegen_ready_inst_def, is_param_opcode_def,
         is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
         is_unlowered_internal_call_opcode_def] >>
      gvs[] >> disj1_tac >> qexistsl [`0`, `s`] >> simp[execute_plan_def]) >>
  `inst.inst_opcode <> PHI` by
    (`bb_well_formed bb` by
      (fs[codegen_ready_fn_def, wf_function_def] >>
       metis_tac[livenessTransferProofsTheory.lookup_block_mem]) >>
     qspecl_then [`bb.bb_instructions`, `k`] mp_tac phi_prefix_not_phi >>
     (impl_tac >- metis_tac[bb_well_formed_def]) >> simp[]) >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] static_abort_regular_inst_progress) >>
  rpt (first_assum (irule_at Any)) >>
  goal_assum (drule_at Any) >>
  qexistsl [`term`, `lv`, `bb.bb_label`, `bb_is_halting bb`, `fn`, `dfg`, `cfg`] >>
  simp[]
QED

Theorem static_abort_inst_terminal:
  !unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end lbl bb
   ps_l ps_dfs ps_dfs_after height promised block_ops ps_after k ps inst nl term
   ops qs s top rest.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
    SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\i. EVERY (\op. op <> dead_stack_marker)
    i.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <| ps_cleanup_height := height; ps_cleanup_promised := promised |>) =
    SOME (block_ops,ps_after) /\
  block_plan_state lv dfg cfg fn bb
    (ps_l with <| ps_cleanup_height := height; ps_cleanup_promised := promised |>) k ps /\
  phi_prefix_length bb.bb_instructions <= k /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = inst /\
  nl = live_vars_at lv bb.bb_label (k + 1) /\
  term = (k + 1 < LENGTH bb.bb_instructions /\
          is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode) /\
  inst_shape_ok inst /\ codegen_ready_inst inst /\
  MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
  generate_inst_plan lv dfg cfg fn inst nl (bb_is_halting bb) term bb.bb_label ps =
    SOME (ops,qs) /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  s.as_call_ctx.cc_static /\
  s.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
  asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q s t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all block_plan_state_static >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``] static_abort_regular_inst_terminal) >>
  rpt (first_assum (irule_at Any)) >>
  goal_assum (drule_at Any) >>
  qexistsl [`term`, `lv`, `bb.bb_label`, `bb_is_halting bb`, `fn`, `dfg`, `cfg`] >>
  simp[]
QED

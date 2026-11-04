(* Checked interface probes for abort-frame preparation. *)
Theory fnFrameTerminalAbort
Ancestors
  fnFrameTerminalPrep generatedPrefixSim planSpillBounds mixedPrefixSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst
  asmFrame asmSem codegenRel frameRel contextCodegenRel genBlockSim
  preparedPrefixSim genFrameSim frameViewFacts frameViewMemory
  venomState regularMemorySim venomWf venomEffects asmIR allocMono
  list stackOpSim planExec emitSim blockSimHelpers venomMemProps

(* A transient spill is covered by the output high-water mark even though
   the live spill map is empty again after restoration. *)
Theorem abort_escape_output_allocator_probe:
  !lv dfg cfg fn ih nt lbl.
  (SND (THE (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 REVERT [Var "size"; Lit 32w] [])
    ["size"] ih nt lbl terminal_escape_ps))).ps_alloc.sa_next_offset = 32 /\
  (apply_prefix_ops 0 FEMPTY
    [SOPush (Lit 32w); SOSpill 0; SODup 16; SORestore 0; SOSwap 1]
    terminal_escape_ps).ps_alloc.sa_next_offset = 32
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT [Lit 0w] []) [] ih nt lbl (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]
Proof
  rpt gen_tac >> EVAL_TAC >> simp[]
QED

Theorem abort_assert_unreachable_prefix_probe:
  !lv dfg cfg fn ih nt lbl.
  ?endlabel.
  OPTION_MAP FST (generate_inst_plan lv dfg cfg fn
    (mk_inst 0 ASSERT_UNREACHABLE [Lit 0w] []) [] ih nt lbl
    (init_plan_state 0)) =
  SOME [SOPush (Lit 0w); SOPushLabel endlabel; SOEmit "JUMPI";
        SOEmit "INVALID"; SOLabel endlabel]
Proof
  rpt gen_tac >> qexists `"reachable_1"` >> EVAL_TAC >> simp[]
QED

(* Consume the actual prefix simulation at its allocator boundary.  The
   memory clause already accounts for transient stores, not just live slots. *)
Theorem prepared_local_run_frame_context:
  st.as_stack = top ++ rest /\
  asm_steps lo o2pc prog n (st with as_stack := top) = AsmOK mid /\
  venom_asm_rel lo arranged
    (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  asm_steps lo o2pc prog n st =
    AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
  context_memory_rel cplan vs.vs_memory mid.as_memory
Proof
  strip_tac >> conj_tac
  >- (drule asm_steps_frame >>
      disch_then (qspec_then `rest` mp_tac) >>
      `st with as_stack := top ++ rest = st` by
        simp[asm_state_component_equality] >> simp[]) >>
  irule context_memory_rel_local_prefix >>
  qexistsl [`arranged.ps_alloc`, `st.as_memory`, `r`] >>
  gvs[venom_asm_rel_def]
QED

Theorem selected_prefix_prepared_frame_sim:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := st.as_memory)
    (st with as_stack := top) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp (iops ++ rops)) /\
  st.as_stack = top ++ rest /\
  context_memory_rel cplan vs.vs_memory st.as_memory /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset ==>
  plan_state_residual_wf spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  strip_tac >>
  `asm_block_at prog (st with as_stack := top).as_pc
     (execute_plan initial_fmp (iops ++ rops))` by simp[] >>
  drule_all selected_prefix_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  simp[] >> qexists `st'` >> simp[] >>
  drule_all prepared_local_run_frame_context >> simp[]
QED

(* Any declared source-memory read range, not just REVERT's range. *)
Theorem context_source_payload_agree:
  source_memory_reads_disjoint cplan inst vs /\
  context_memory_rel cplan vs.vs_memory m /\
  MEM (off,n) (source_memory_read_ranges inst vs) ==>
  TAKE n (DROP off m ++ REPLICATE n 0w) =
  TAKE n (DROP off vs.vs_memory ++ REPLICATE n 0w)
Proof
  strip_tac >> irule padded_memory_read_cong >> rpt strip_tac >>
  drule context_reads_agree >> simp[] >> disch_then irule >>
  simp[source_memory_read_byte_def] >>
  qexists `(off,n)` >> simp[byte_in_memory_range_def]
QED

Theorem abort_operands_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [REVERT; INVALID; ASSERT; ASSERT_UNREACHABLE; CREATE; CREATE2; RETURNDATACOPY] ==>
  eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) =
  eval_operands inst.inst_operands vs
Proof
  strip_tac >> irule eval_operands_frame_view >> gen_tac >> disch_tac >>
  irule ordinary_operand_not_retpc >>
  simp[] >> qexists `inst` >> gvs[]
QED

Theorem revert_context_payload_agree:
  inst.inst_opcode = REVERT /\ inst.inst_operands = [off_op; size_op] /\
  eval_operand off_op vs = SOME off /\ eval_operand size_op vs = SOME sz /\
  source_memory_reads_disjoint cplan inst vs /\
  context_memory_rel cplan vs.vs_memory m ==>
  TAKE (w2n sz) (DROP (w2n off) m ++ REPLICATE (w2n sz) 0w) =
  TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w)
Proof
  strip_tac >> irule context_source_payload_agree >>
  qexistsl [`cplan`, `inst`] >>
  simp[source_memory_read_ranges_def, memory_range_of_operands_def]
QED

Theorem terminal_rel_frame_view_stack:
  venom_asm_terminal_rel (frame_view fn ra vs) (st with as_stack := stk) <=>
  venom_asm_terminal_rel vs st
Proof
  simp[venom_asm_terminal_rel_def, frame_view_def]
QED

(* General terminal step: payload agreement is the only memory requirement. *)
Theorem terminal_revert_step_payload:
  asm_block_at prog st.as_pc [AsmOp "REVERT"] /\
  st.as_stack = off :: sz :: tail /\
  venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++ REPLICATE (w2n sz) 0w) =
  TAKE (w2n sz) (DROP (w2n off) st.as_memory ++ REPLICATE (w2n sz) 0w) ==>
  ?out.
    asm_steps lo o2pc prog 1 st = AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz) (DROP (w2n off) vs.vs_memory ++
          REPLICATE (w2n sz) 0w)) vs)) out
Proof
  strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  drule asm_step_revert_eq >>
  disch_then (qspecl_then [`lo`, `o2pc`] assume_tac) >>
  gvs[asm_block_at_def] >>
  gvs[venom_asm_terminal_rel_def, revert_state_def, set_returndata_def] >>
  Cases_on `w2n sz = 0` >>
  gvs[asm_returndata_read_byte, venom_returndata_read_byte]
QED

Theorem gen_inst_revert_frame_sim:
  !inst cplan vs fn r final base ps nl lo ra dfg ops ctx rest mem0 st
    lv cfg halting term label prog fuel a vs' o2pc.
  inst.inst_opcode = REVERT /\
  source_memory_reads_disjoint cplan inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH (SND
    (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  prefix_spill_wf cplan.cp_initial_fmp lo (FRONT ops) ps /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops, final) /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n out. a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel vs' out
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_inst_revert_abort >> strip_tac >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps =
    (ops,final)` by
    gvs[generate_inst_plan_def, is_param_opcode_def] >>
  `venom_to_evm_name inst.inst_opcode = SOME "REVERT"` by
    simp[venom_to_evm_name_def] >>
  drule_all regular_plan_selected_prefix >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  gvs[is_commutative_def] >>
  `r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    gvs[release_dead_spills_spill_base, release_dead_spills_next_offset] >>
  suspend "decomposed"
QED

Resume gen_inst_revert_frame_sim[decomposed]:
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (fs[stack_get_depth_def] >> drule stack_find_el >>
         drule planWfTheory.stack_find_bound >>
         metis_tac[MEM_EL, MEM_REVERSE]) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[finite_mapTheory.FLOOKUP_DEF]) >>
  rename1 `generated_plan_state_wf spillbase ps` >>
  `residual_budget_wf spillbase [] ps` by
    metis_tac[generated_plan_state_wf_residual_nil] >>
  `plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[generated_plan_state_wf_def] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (simp[] >> irule regular_prefix_segment_address_bounds >>
     qexistsl_tac [`cplan.cp_initial_fmp`, `lo`, `"REVERT"`,
       `iops ++ rops ++ [SOEmit "REVERT"]`, `[]`, `ps`] >>
     gvs[APPEND_ASSOC]) >>
  `asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)))
     [AsmOp "REVERT"]` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     simp[execute_plan_append, execute_plan_def, exec_stack_op_def, asm_block_at_append]) >>
  drule fn_frame_inv_local_state >> strip_tac >>
  `context_memory_rel cplan vs.vs_memory st.as_memory` by
    fs[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
        operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `plan_state_residual_wf spillbase (compute_operands inst)
     (LENGTH (compute_operands inst)) arranged /\
   arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
     compute_operands inst /\
   ?mid. asm_steps lo o2pc prog
     (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
       AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
     venom_asm_rel lo arranged
       (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
     context_memory_rel cplan vs.vs_memory mid.as_memory /\
     mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (irule selected_prefix_prepared_frame_sim >>
     simp[] >> rpt conj_tac
     >- (qexistsl_tac [`arranged`, `r`] >> simp[]) >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     simp[sortingTheory.PERM_REFL] >> metis_tac[]) >>
  suspend "prepared"
QED

Resume gen_inst_revert_frame_sim[prepared]:
  `eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := st.as_memory) =
    SOME [off_val; sz_val]` by
    (drule abort_operands_frame_view >> simp[eval_operands_def]) >>
  `mid.as_stack = [off_val; sz_val] ++ DROP (LENGTH inst.inst_operands) mid.as_stack` by
    (irule arranged_eval_operands_stack >>
     conj_tac
     >- (gvs[compute_operands_def, EVERY_MEM, MEM_REVERSE] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
     qexists `stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack` >>
     gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
       eval_operand_with_memory] >>
     metis_tac[]) >>
  `venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest)` by
    (qpat_x_assum `venom_asm_rel lo arranged _ mid` mp_tac >>
     simp[venom_asm_rel_def, venom_asm_terminal_rel_def, frame_view_def]) >>
  `TAKE (w2n sz_val) (DROP (w2n off_val) mid.as_memory ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++ REPLICATE (w2n sz_val) 0w)` by
    (irule revert_context_payload_agree >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `?out. asm_steps lo o2pc prog 1 (mid with as_stack := mid.as_stack ++ rest) = AsmRevert out /\
    venom_asm_terminal_rel
      (revert_state (set_returndata
        (TAKE (w2n sz_val) (DROP (w2n off_val) vs.vs_memory ++ REPLICATE (w2n sz_val) 0w)) vs)) out` by
    (irule terminal_revert_step_payload >>
     simp[] >> conj_tac
     >- (qexists `DROP (LENGTH inst.inst_operands) mid.as_stack ++ rest` >>
         metis_tac[APPEND_ASSOC, APPEND]) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 1`, `out`] >>
  simp[] >> irule asm_steps_compose_revert >> goal_assum (drule_at Any) >> simp[]
QED

Finalise gen_inst_revert_frame_sim

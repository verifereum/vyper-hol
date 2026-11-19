(* Structural assertion preparation, independent of the successful suffix. *)
Theory symInstAssertPrepareOwn
Ancestors symInstPiecesFacts symInstPrefixOwn
  symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim fnFrameDeepInst

(* Parser abbreviation for the existing structural bridge, not a definition. *)
val assert_prepare_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", assert_prepare_bridge_core_tm);

Theorem sym_assert_unreachable_frame_prepare_mode_core:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = ASSERT_UNREACHABLE /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  bridge_core lo code_ok cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\ qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
  ~is_param_opcode inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  MEM inst (fn_insts fn) /\ fn_shape_ok fn /\ dfg = dfg_build_function fn /\
  source_memory_reads_disjoint cplan inst vs /\ context_source_memory_writes_disjoint cplan inst vs /\
  step_inst fuel ctx inst vs = OK vsout /\
  emit_input_plan ASSERT_UNREACHABLE [cond] nl ps = (iops,prepared) /\
  reorder_plan dfg [cond] prepared = (rops,arranged) /\
  fresh_label "reachable" (arranged with ps_stack := stack_pop 1 arranged.ps_stack) = (lbl,p3) /\
  qs = release_dead_spills nl p3 /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT_UNREACHABLE [cond] nl ps)).ps_stack /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] /\ is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  ops = iops ++ rops ++ [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] /\
  asm_static_wf prog /\ asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?mid ready localtop.
    arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := cs.as_memory) mid /\
    sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    bridge_core lo code_ok mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    asm_block_at prog ready.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]
Proof
  strip_tac >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (drule allocMonoTheory.fresh_label_spill_base >> simp[] >> strip_tac >>
     gvs[allocMonoTheory.release_dead_spills_spill_base,
       allocMonoTheory.release_dead_spills_next_offset] >>
     metis_tac[allocMonoTheory.emit_input_plan_spill_base,
       allocMonoTheory.reorder_plan_spill_base]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  `emit_input_plan inst.inst_opcode [cond] nl ps = (iops,prepared)` by simp[] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (SPEC_ALL sym_frame_selected_prefix_paired_mode_conditional)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `labs0`, `qs`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  rename1 `venom_asm_rel lo arranged _ mid` >>
  rename1 `sym_steps_mode allow_own prog env own _ ss = SymOK ready` >>
  rename1 `ready.sym_stack = localtop ++ srest` >>
  qexistsl [`mid`, `ready`, `localtop`] >> simp[] >>
  gvs[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
    planExecTheory.exec_stack_op_def, stackOpSimTheory.asm_block_at_append] >>
  rename1 `ready.sym_base = mid with <|as_stack := []; as_memory := midmem; as_code := []|>` >>
  conj_tac >- (qexists `midmem` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i l d j. FLOOKUP ready.sym_mem_labels i = SOME (l,d,j) ==> _` drule >>
  simp[]
QED

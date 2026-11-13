(*
 * gen_jnz_frame_sim_deep: genFrameSim's gen_jnz_frame_sim for JNZ, with
 * operands at any stack depth, repeated dead_stack_marker slots
 * (generated_plan_state_wf_marked) and only an address bound on the
 * plan's spill and restore offsets.  fnFrameDeep collects it with the
 * other instruction frame lemmas the block induction composes.
 *
 * TOP-LEVEL:
 *   gen_jnz_frame_sim_deep
 *)

Theory fnFrameDeepJnz
Ancestors
  deepResidualSim deepResidualBudget fnPlanPrefix genFrameSim frameRel
  contextCodegenRel codegenRel blockSimHelpers unitShapeDefs genBlockSim
  mixedPrefixSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  cfgDefs list rich_list finite_map stackOpSim stackModel

(* gen_jnz_frame_sim with any-depth ownership, generated_plan_state_wf_marked and an
   address bound on spill and restore offsets. *)
Theorem gen_jnz_frame_sim_deep_exact:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?iops ps1 rops ps2 w as'.
        emit_input_plan JNZ [cond_op] next_liveness ps = (iops, ps1) /\
        reorder_plan dfg [cond_op] ps1 = (rops, ps2) /\
        ops = iops ++ rops ++
          [SOPushLabel if_nz; SOEmit "JUMPI"; SOPushLabel if_z; SOEmit "JUMP"] /\
        ps' = release_dead_spills next_liveness
          (ps2 with ps_stack := stack_pop 1 ps2.ps_stack) /\
        eval_operand cond_op vs = SOME w /\
        asm_steps lo o2pc prog
          (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) +
           (if w = 0w then 4 else 2)) as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `MEM r cplan.cp_regions` >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  `!l. cond_op <> Label l` by
    (rpt strip_tac >> qpat_x_assum `~is_label_operand _` mp_tac >>
     asm_rewrite_tac[is_label_operand_def]) >>
  drule_all jnz_plan_decompose >> strip_tac >>
  qpat_x_assum `ops = _` SUBST_ALL_TAC >>
  `?top. as.as_stack = top ++ rest /\
    context_venom_asm_rel cplan lo ps (frame_view fn ra vs)
      (as with as_stack := top)` by
    (fs[fn_frame_inv_def] >> metis_tac[]) >>
  qabbrev_tac `v = frame_view fn ra vs with vs_memory := as.as_memory` >>
  `venom_asm_rel lo ps v (as with as_stack := top)` by
    (drule context_venom_asm_rel_local >> simp[Abbr `v`]) >>
  `!op. operand_val v lo op = operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[Abbr `v`, operand_val_def]) >>
  (* The marked core: bring the condition to the top, at any depth. *)
  `residual_budget_wf_marked spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (drule generated_plan_state_wf_marked_residual_nil >>
     fs[generated_plan_state_wf_marked_def]) >>
  `!op. MEM op [cond_op] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (simp[] >> strip_tac >>
     qpat_x_assum `is_var_operand cond_op ==> _` drule >> strip_tac
     >- (Cases_on `stack_get_depth cond_op ps.ps_stack` >> gvs[] >>
         drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = cond_op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `cond_op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `!l. MEM (Label l) [cond_op] ==> IS_SOME (FLOOKUP lo l)` by
    (rpt strip_tac >> gvs[]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    fs[EVERY_APPEND] >>
  `asm_block_at prog (as with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[execute_plan_append, asm_block_at_append] >>
  `PERM [cond_op] [cond_op] /\ LENGTH [cond_op] <= 16 /\
   LENGTH [cond_op] <= LENGTH ps1.ps_stack` by gvs[] >>
  `EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond_op]` by
    (simp[] >> metis_tac[]) >>
  `!op at. MEM op [cond_op] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond_op]) /\
    operand_equiv dfg op at ==>
    operand_val v lo op = operand_val v lo at` by
    (simp[] >> metis_tac[]) >>
  `JNZ <> INVOKE` by simp[] >>
  drule_all selected_prefix_prepared_sim_marked >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  rename1 `venom_asm_rel lo ps2 v mid` >>
  `?pre. ps2.ps_stack = pre ++ [cond_op]` by metis_tac[] >>
  `?w tail. mid.as_stack = w::tail /\ operand_val v lo cond_op = SOME w` by
    (qpat_x_assum `venom_asm_rel lo ps2 v mid` mp_tac >>
     qpat_x_assum `ps2.ps_stack = pre ++ _` mp_tac >>
     qpat_x_assum `cond_op <> dead_stack_marker` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, plan_stack_rel_def] >> rpt strip_tac >>
     Cases_on `mid.as_stack` >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[REVERSE_APPEND]) >>
  `venom_asm_rel lo ps' v (mid with as_stack := tail)` by
    (qpat_x_assum `ps' = _` SUBST1_TAC >> irule jnz_consume_rel >>
     metis_tac[]) >>
  `asm_block_at prog mid.as_pc
    [AsmPushLabel if_nz; AsmOp "JUMPI"; AsmPushLabel if_z; AsmOp "JUMP"]` by
    (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
     simp[execute_plan_append, asm_block_at_append] >>
     simp[execute_plan_def, exec_stack_op_def]) >>
  drule_all jnz_suffix >> strip_tac >>
  (* The jump, and the frame invariant again. *)
  qabbrev_tac `dest = if w = 0w then pc_z else pc_nz` >>
  qabbrev_tac `label = if w = 0w then if_z else if_nz` >>
  qabbrev_tac `out = mid with <|as_stack := tail; as_pc := dest|>` >>
  `venom_asm_rel lo ps' v out` by
    (qunabbrev_tac `out` >>
     `mid with <|as_stack := tail; as_pc := dest|> =
      (mid with as_stack := tail) with as_pc := dest` by
        simp[asmSemTheory.asm_state_component_equality] >>
     pop_assum SUBST1_TAC >> pure_rewrite_tac[venom_asm_rel_pc] >>
     first_assum ACCEPT_TAC) >>
  `asm_steps lo o2pc prog
    (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
     (if w = 0w then SUC (SUC (SUC (SUC 0))) else SUC (SUC 0)))
    (as with as_stack := top) = AsmOK out` by
    (irule asm_steps_compose_ok >> qexists `mid` >>
     simp[Abbr `out`, Abbr `dest`]) >>
  `asm_steps lo o2pc prog
       (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
        (if w = 0w then 4 else 2)) as =
       AsmOK (out with as_stack := out.as_stack ++ rest) /\
     fn_frame_inv ctx cplan lo fn ra rest mem0 ps' (jump_to label vs)
       (out with as_stack := out.as_stack ++ rest)` by
    (qunabbrev_tac `v` >> drule_all frame_jump_lift >> simp[]) >>
  `eval_operand cond_op vs = SOME w` by metis_tac[] >>
  gen_tac >> strip_tac >>
  `vs' = jump_to label vs` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def] >>
     Cases_on `w = 0w` >> simp[Abbr `label`] >> metis_tac[]) >>
  qexistsl_tac [`iops`, `ps1`, `rops`, `ps2`, `w`,
    `out with as_stack := out.as_stack ++ rest`] >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  Cases_on `w = 0w` >>
  fs[Abbr `out`, Abbr `dest`, Abbr `label`]
QED

(* Preserve the existential-count interface as a projection of the exact run. *)
Theorem gen_jnz_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z))
Proof
  rpt strip_tac >> drule_all gen_jnz_frame_sim_deep_exact >>
  metis_tac[]
QED

(* Named instruction composition shared by canonical and relocated execution. *)
Theory symInstNamedOwn
Ancestors symInstPiecesFacts symInstPrefixOwn symEmitOwn symEmitDischargeOwn
  symEmitNamedOwn asmSymModeOwn asmSymForwardOwn asmSymOwnStep
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst

(* Syntax for the already existing structural bridge, not a new constant. *)
val named_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", named_bridge_core_tm);

Theorem sym_named_all_steps_suffix_mode:
  venom_to_evm_name opc = SOME name /\
  (opc = CODESIZE ==> allow_own) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own 1
    (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  strip_tac >> Cases_on `opc = CODESIZE`
  >- (gvs[asmIRTheory.venom_to_evm_name_def] >>
      `asm_block_at p (ss with sym_stack := ss.sym_stack ++ tail).sym_base.as_pc
         [AsmOp "CODESIZE"]` by simp[] >>
      imp_res_tac sym_steps_mode_single >>
      gvs[asmSymOwnCodeTheory.sym_step_own_def,
          asmSymOwnCodeTheory.sym_step_op_own_def,
          asmSymSemTheory.sym_set_stack_def,
          asmSymSemTheory.sym_state_component_equality]) >>
  drule_all named_suffix_dispatch_names >> strip_tac >>
  irule sym_named_steps_ok_stack_suffix_mode >> simp[] >>
  qexists_tac `name` >> gvs[listTheory.MEM]
QED

Theorem sym_named_restore_stack_core:
  venom_to_evm_name opc = SOME name /\
  (opc = CODESIZE ==> allow_own) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp name] /\
  asm_op_arity name <= LENGTH ss.sym_stack /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail /\
  sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\
  bridge_core lo code_ok cs' ss' /\
  ss'.sym_mem_labels = ss.sym_mem_labels /\
  sym_kinds_ok cplan fn ret [] qs ss' ==>
  ?full. sym_steps_mode allow_own p env own 1
      (ss with sym_stack := ss.sym_stack ++ stail) = SymOK full /\
    bridge_core lo code_ok (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail qs full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bridge_core lo code_ok (cs' with as_stack := cs'.as_stack ++ wtail)
    (ss' with sym_stack := ss'.sym_stack ++ stail)` by
    (irule asm_sym_rel_restore_stack_core >> simp[] >> metis_tac[]) >>
  `sym_steps_mode allow_own p env own 1
     (ss with sym_stack := ss.sym_stack ++ stail) =
     SymOK (ss' with sym_stack := ss'.sym_stack ++ stail)` by
    (irule sym_named_all_steps_suffix_mode >> simp[] >> metis_tac[]) >>
  qexists_tac `ss' with sym_stack := ss'.sym_stack ++ stail` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  simp[sym_kinds_ok_restore_stack]
QED

val named_run_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", named_run_bridge_core_tm);

Theorem sym_named_inst_symbolic_run_mode_core:
  !allow_own own code_ok fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss name.
    (!n cs ss ss'. bridge_core lo code_ok cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        bridge_core lo code_ok cs' ss') /\
    (!localps localqs cs localss cs' vsout selected residual m.
      bridge_core lo code_ok cs localss /\
      sym_kinds_ok cp fn ret [] localps localss /\
      asm_block_at prog cs.as_pc [AsmOp name] /\
      asm_step lo (build_offset_to_pc prog) (AsmOp name) cs = AsmOK cs' /\
      asm_steps lo (build_offset_to_pc prog) prog 1 cs = AsmOK cs' /\
      (selected = compute_operands inst \/
       (is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) /\
        selected = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
          [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
           EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])) /\
      localps.ps_stack = residual ++ selected /\
      EVERY (\op. op <> dead_stack_marker) selected /\
      (!op. MEM op selected ==>
        eval_operand op (frame_view fn ra vs with vs_memory := m) =
        operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
      venom_asm_rel lo localps (frame_view fn ra vs with vs_memory := m) cs /\
      venom_asm_rel lo localqs vsout cs' /\
      localqs = localps with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
        (stack_pop (LENGTH selected) localps.ps_stack) inst.inst_outputs ==>
      ?outss. sym_steps_mode allow_own prog env own 1 localss = SymOK outss /\
        bridge_core lo code_ok cs' outss /\
        outss.sym_mem_labels = localss.sym_mem_labels /\
        sym_kinds_ok cp fn ret [] localqs outss) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (inst.inst_opcode = CODESIZE ==> allow_own) /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\ inst_wf inst /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\ operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\ vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    asm_static_wf prog /\
    bridge_core lo code_ok as ss /\ sym_kinds_ok cp fn ret srest ps ss /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
    (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?ss'. sym_steps_mode allow_own prog env own
          (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK ss' /\
        sym_kinds_ok cp fn ret srest ps' ss' /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `MEM r cplan.cp_regions` >>
  gen_tac >> strip_tac >>
  drule_all frame_inst_local_setup >> strip_tac >>
  `~is_pre_codegen_opcode inst.inst_opcode` by
    metis_tac[stackPlanGenTheory.generate_inst_plan_pre_codegen_none, optionTheory.NOT_SOME_NONE] >>
  `generate_regular_inst_plan liveness dfg cfg fn inst next_liveness
     is_halting next_is_term bb_label ps = (ops,ps')` by
    (`inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\ inst.inst_opcode <> NOP` by
       metis_tac[asmIRTheory.venom_to_evm_name_def, optionTheory.NOT_SOME_NONE] >>
     qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def]) >>
  `n2w cplan.cp_initial_fmp = vs.vs_initial_fmp` by
    fs[frameRelTheory.fn_frame_inv_def] >>
  drule_at (Pat `step_inst _ _ _ _ = _`)
    (SRULE [venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update, genFrameSimTheory.frame_view_control_fields]
     deepInstSimTheory.regular_inst_prepared_emit_marked) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  rename1 `generated_plan_state_wf_marked sb ps` >>
  disch_then (qspecl_then [`o2pc`, `prog`, `sb`, `name`, `cplan.cp_initial_fmp`] mp_tac) >>
  simp[venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update, genFrameSimTheory.frame_view_control_fields] >>
  (impl_tac >- (conj_tac >- metis_tac[] >>
    fs[listTheory.EVERY_MEM] >> metis_tac[])) >>
  strip_tac >> suspend "prefix"
QED

Resume sym_named_inst_symbolic_run_mode_core[prefix]:
  markerLib.RESUME_TAC >>
  `PERM (compute_operands inst) selected` by
    metis_tac[generatedPrefixSimTheory.regular_plan_selected_perm] >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> IS_SOME _ \/ _` mp_tac >>
     simp[fnPlanLineageInventoryTheory.stack_get_depth_is_some,
       finite_mapTheory.FLOOKUP_DEF, COND_RAND]) >>
  qmatch_asmsub_abbrev_tac `generated_plan_state_wf_marked sb
    (arranged with ps_stack := estack)` >>
  qabbrev_tac `emitted = arranged with ps_stack := estack` >>
  `emitted = arranged with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) arranged.ps_stack) inst.inst_outputs` by
    simp[Abbr `emitted`, Abbr `estack`] >>
  `((if inst.inst_outputs = [] \/ is_halting then ([],emitted)
     else popmany_plan (MAP Var (FILTER (\out. ~MEM out next_liveness) inst.inst_outputs)) emitted)
       = (popops,popped)) /\
   ((if FILTER (\out. MEM out next_liveness) inst.inst_outputs = [] then ([],popped)
     else optimistic_swap_plan (dfg_build_function fn) inst next_liveness next_is_term popped)
       = (optops,tail))` by
    (qpat_x_assum `if _ then popops = _ /\ _ else _` mp_tac >>
     qpat_x_assum `if _ then optops = _ /\ _ else _` mp_tac >>
     qpat_x_assum `LENGTH inst.inst_outputs <= 1` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `inst.inst_outputs = []` >> simp[COND_EXPAND] >> metis_tac[]) >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by
    (qpat_x_assum `LENGTH _ <= LENGTH (SND _) .ps_stack` mp_tac >> simp[]) >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`) sym_regular_prefix_applicability >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  disch_then (drule_at (Pat `emitted = _`)) >>
  disch_then (drule_at (Pat `_ = (popops,popped)`)) >>
  disch_then (drule_at (Pat `_ = (optops,tail)`)) >>
  disch_then (drule_at (Pat `_ = release_dead_spills _ _`)) >>
  simp[] >> strip_tac >> suspend "prefix_run"
QED

Resume sym_named_inst_symbolic_run_mode_core[prefix_run]:
  markerLib.RESUME_TAC >>
  `ssa_form fn` by metis_tac[stackPlanGenTheory.codegen_ready_fn_def] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >> simp[listTheory.EVERY_APPEND]) >>
  `ss.sym_base.as_pc = as.as_pc` by
    (irule (cj 1 asmSymBridgeTheory.asm_sym_rel_core_pc) >> metis_tac[]) >>
  `asm_block_at prog ss.sym_base.as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
     simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append]) >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`) sym_selected_prefix_sim_marked >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >> simp[] >>
  disch_then (qspecl_then [`sb`, `r`, `env`] mp_tac) >> simp[] >>
  (impl_tac >-
    (qpat_x_assum `EVERY _ (compute_operands inst)` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[])) >> strip_tac >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  drule_all sym_prepared_prefix_endpoint_mode_conditional >> disch_then assume_tac >>
  qpat_assum `venom_asm_rel lo arranged _ mid`
    (mp_then (Pat `venom_asm_rel _ _ _ _`) mp_tac sym_prepared_emit_localize_core) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`rest`, `code_ok`] mp_tac) >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `localtop` (map_every assume_tac o CONJUNCTS)) >>
  suspend "emission"
QED

Resume sym_named_inst_symbolic_run_mode_core[emission]:
  markerLib.RESUME_TAC >>
  `!op. MEM op selected <=> MEM op (compute_operands inst)` by
    metis_tac[sortingTheory.PERM_MEM_EQ] >>
  `EVERY (\op. op <> dead_stack_marker) selected` by
    (qpat_x_assum `EVERY _ (compute_operands inst)` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := as.as_memory) =
    operand_val (frame_view fn ra vs with vs_memory := as.as_memory) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
      genFrameSimTheory.operand_val_memory_update] >>
  qpat_x_assum `!localps localqs cs localss cs' vsout selected residual m. _`
    (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (drule_at (Pat `asm_steps _ _ _ 1 _ = _`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (qspecl_then [`selected`,
    `stack_pop (LENGTH selected) arranged.ps_stack`, `as.as_memory`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
     simp[IgnAsm `arranged.ps_stack = _`, IgnAsm `emitted = _`, IgnAsm `ops = _`] >>
     qpat_x_assum `arranged.ps_stack = _` mp_tac >>
     simp[listTheory.APPEND_ASSOC, IgnAsm `emitted = _`, IgnAsm `ops = _`])) >>
  disch_then (qx_choose_then `outss` (map_every assume_tac o CONJUNCTS)) >>
  suspend "restore"
QED

Resume sym_named_inst_symbolic_run_mode_core[restore]:
  markerLib.RESUME_TAC >>
  `asm_op_arity name <= LENGTH localtop` by
    (Cases_on `inst.inst_opcode = CODESIZE`
     >- (qpat_x_assum `venom_to_evm_name _ = _` mp_tac >>
         simp[asmIRTheory.venom_to_evm_name_def] >> strip_tac >>
         simp[asmSymSemTheory.asm_op_arity_def, asmSymSemTheory.asm_op_arity_table_def]) >>
     drule_all named_suffix_emission_arity >> strip_tac >>
     qpat_assum `venom_asm_rel lo arranged _ mid`
       (mp_then (Pat `venom_asm_rel _ _ _ _`) mp_tac prepared_suffix_concrete_height) >>
     disch_then (qspecl_then [`selected`, `stack_pop (LENGTH selected) arranged.ps_stack`] mp_tac) >>
     (impl_tac >- (qpat_x_assum `arranged.ps_stack = _` mp_tac >>
       simp[listTheory.APPEND_ASSOC, IgnAsm `emitted = _`, IgnAsm `ops = _`])) >>
     simp[IgnAsm `arranged.ps_stack = _`, IgnAsm `emitted = _`, IgnAsm `ops = _`]) >>
  qpat_assum `LIST_REL _ srest rest`
    (mp_then (Pat `LIST_REL _ _ _`) mp_tac sym_named_restore_stack_core) >>
  disch_then (drule_at (Pat `sym_steps_mode _ _ _ _ 1 _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (qspecl_then [`inst.inst_opcode`, `name`, `after_emit`, `code_ok`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (simp[IgnAsm `arranged.ps_stack = _`, IgnAsm `emitted = _`, IgnAsm `ops = _`] >>
       metis_tac[asmSymBridgeTheory.asm_sym_rel_core_pc]) >>
     conj_tac >- simp[] >>
     conj_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `full` (map_every assume_tac o CONJUNCTS)) >>
  suspend "postfix"
QED

Resume sym_named_inst_symbolic_run_mode_core[postfix]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `generated_plan_state_wf_marked sb emitted`)
    sym_regular_postfix_applicability >>
  disch_then (drule_at (Pat `_ = (popops,popped)`)) >>
  disch_then (drule_at (Pat `_ = (optops,tail)`)) >>
  disch_then (drule_at (Pat `ps' = release_dead_spills _ _`)) >>
  disch_then (drule_at (Pat `MEM r cplan.cp_regions`)) >>
  disch_then (qspecl_then [`fn.fn_name`, `ctx`] mp_tac) >>
  simp[IgnAsm `arranged.ps_stack = _`, IgnAsm `emitted = _`, IgnAsm `ops = _`] >>
  strip_tac >>
  `!out. inst.inst_outputs = [out] ==>
    stack_get_depth (Var out) emitted.ps_stack = SOME 0` by
    (rpt strip_tac >> simp[Abbr `emitted`, Abbr `estack`,
       IgnAsm `arranged.ps_stack = _`] >> metis_tac[]) >>
  `!off. MEM (SOSpill off) (popops ++ optops) ==> off < dimword (:256)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >>
     qpat_x_assum `ops = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `full.sym_base.as_pc = after_emit.as_pc` by
    (qpat_x_assum `?m. full.sym_base = _ /\ _` strip_assume_tac >> simp[]) >>
  drule_at (Pat `sym_kinds_ok _ _ _ _ emitted full`)
    sym_regular_generated_postfix_sim_marked >>
  disch_then (drule_at (Pat `_ = (popops,popped)`)) >>
  disch_then (drule_at (Pat `_ = (optops,tail)`)) >>
  disch_then (drule_at (Pat `qs = release_dead_spills _ _`)) >>
  disch_then (qspecl_then [`prog`, `cplan.cp_initial_fmp`, `env`,
    `closure_spill_byte ctx cplan fn.fn_name`] mp_tac) >>
  simp[IgnAsm `arranged.ps_stack = _`, IgnAsm `emitted = _`, IgnAsm `ops = _`] >>
  (impl_tac >- metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  rename1 `sym_steps prog env (LENGTH (execute_plan _ (popops ++ optops))) full = SymOK final` >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  `execute_plan cplan.cp_initial_fmp [SOEmit name] = [AsmOp name]` by
    simp[NoAsms, planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
  qexists_tac `final` >> (conj_tac
  >- (`sym_steps_mode allow_own prog env own
        (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
         (1 + LENGTH (execute_plan cplan.cp_initial_fmp (popops ++ optops)))) ss = SymOK final` suffices_by
        (pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
         qpat_x_assum `execute_plan _ [SOEmit name] = _` (fn th => rewrite_tac[th]) >>
         rewrite_tac[listTheory.LENGTH, arithmeticTheory.ADD_ASSOC, arithmeticTheory.ONE]) >>
      once_rewrite_tac[sym_steps_mode_add] >>
      qpat_x_assum `sym_steps_mode _ _ _ _ _ ss = SymOK ss'` (fn th => rewrite_tac[th]) >>
      once_rewrite_tac[sym_steps_mode_add] >>
      qpat_x_assum `sym_steps_mode _ _ _ _ 1 _ = SymOK full` mp_tac >>
      simp[NoAsms] >>
      qpat_x_assum `ss'.sym_stack = _` (fn th => rewrite_tac[GSYM th]) >>
      simp_tac (srw_ss()) [] >> strip_tac >> asm_rewrite_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b` by
    metis_tac[symInstKindsTheory.spill_region_labels_outside_closure] >>
  metis_tac[])
QED

Finalise sym_named_inst_symbolic_run_mode_core

Theorem sym_named_inst_symbolic_run_own:
  !allow_own own fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss name.
    o2pc = build_offset_to_pc prog /\ code_labels_agree prog lo /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (inst.inst_opcode = CODESIZE ==> allow_own) /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\ inst_wf inst /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\ operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\ vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    (!dst x sz w off. inst.inst_opcode = CODECOPY /\
      inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
      eval_operand (Var x) vs = SOME w /\ FLOOKUP lo "code_end" = SOME off ==>
      w2n (w - n2w off) < dimword (:256) DIV 2) /\
    sym_data_label prog env "code_end" /\
    (MEM (Label "runtime_begin") inst.inst_operands ==>
     sym_data_label prog env "runtime_begin") /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss /\
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?ss'. sym_steps_mode allow_own prog env own
          (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK ss' /\
        sym_kinds_ok cp fn ret srest ps' ss' /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `sym_frame_inv_own _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_own_def] >> strip_tac >>
  gen_tac >> strip_tac >>
  drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)
    sym_named_inst_symbolic_run_mode_core >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`allow_own`, `own`, `\code. asm_data_env_lo_ok lo prog env own /\ code = own`] mp_tac) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `venom_to_evm_name _ = _`)) >>
  disch_then (qspecl_then [`o2pc`, `env`, `labs0`] mp_tac) >>
  simp[asmSymBridgeTheory.asm_sym_rel_core_own] >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule_all asm_sym_steps_mode_sim >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `ssa_form fn` by fs[codegen_ready_fn_def] >>
          `~is_pre_codegen_opcode inst.inst_opcode` by
            metis_tac[generate_inst_plan_pre_codegen_none, optionTheory.NOT_SOME_NONE] >>
          qpat_assum `localps.ps_stack = _` (fn th => rewrite_tac[GSYM th]) >>
          drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`) sym_named_source_emit_mode >>
          disch_then (drule_at (Pat `asm_step _ _ _ _ = _`)) >>
          disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
          disch_then (drule_at (Pat `venom_asm_rel _ _ (frame_view _ _ _ with vs_memory := _) _`)) >>
          disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
          disch_then (drule_at (Pat `asm_sym_rel_own _ _ _ _ _ _`)) >>
          disch_then (drule_at (Pat `_.ps_stack = _ ++ _`)) >>
          disch_then (qspec_then `allow_own` mp_tac) >>
          simp[]) >>
      gvs[]) >> simp[]
QED

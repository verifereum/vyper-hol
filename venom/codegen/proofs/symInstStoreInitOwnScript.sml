(* Fixed store, initial-FMP and BUMP instruction composition. *)
Theory symInstStoreInitOwn
Ancestors symInstPiecesFacts symInstPrefixOwn symInstPhiOwn symEmitOwn
  symEmitStoreOwn symEmitSim asmSymModeOwn symPostfixSim fnFrameDeepInst
  symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice planExec
  codegenSymRel asmSymSem doSwapSim genBlockSim

Theorem sym_istore_prepared_run_mode_core:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) localtop cs.as_stack /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] ==>
  ?full. sym_steps_mode allow_own p env own 2 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 2 ps.ps_stack)) full
Proof
  strip_tac >>
  `?w off tail. localtop = Val w :: Val off :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n off) 32 b)` by
    (mp_tac (Q.INST [`ss` |-> `ss with sym_stack := localtop`, `srest` |-> `[]`, `vlo` |-> `lo`]
       sym_istore_prepared_safe_core) >> simp[] >>
     disch_then drule_all >> simp[]) >>
  `ss.sym_stack = Val w :: Val off :: (tail ++ srest)` by simp[] >>
  drule_all (Q.SPECL [`allow_own`, `own`] sym_istore_success_run_mode) >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >> irule sym_kinds_ok_release_dead_spills >>
  irule sym_emit_kinds_pop >> qexistsl [`2`, `ps`, `ss`] >> simp[]
QED

val store_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", store_bridge_core_tm);

Theorem sym_initial_fmp_generated_cleanup_mode_core:
  (!n cs ss ss'. B cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\ B cs' ss') /\
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_outputs = [x] /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  emitted = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled /\
  (if halt then ([],emitted)
   else popmany_plan (if MEM x nl then [] else [Var x]) emitted) = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8)) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  B cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts))) ==>
  ?final. sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts)))) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. ~R b ==> FLOOKUP final.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `execute_plan initial_fmp [SOInitialFmp] = [AsmPush (encode_num_bytes initial_fmp)]` by
    simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append] >>
  asm_rewrite_tac[stackOpSimTheory.asm_block_at_append, listTheory.LENGTH] >> strip_tac >>
  drule (Q.SPECL [`allow_own`, `own`] sym_initial_fmp_run_mode) >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] assume_tac) >>
  `?cs'. asm_steps lo (build_offset_to_pc p) p 1 cs = AsmOK cs' /\
     B cs' (ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
       sym_stack := Val (n2w initial_fmp) :: ss.sym_stack|>)` by metis_tac[] >>
  drule_at (Pat `asm_steps _ _ _ _ _ = _`) symEmitFrameOwnTheory.sym_initial_fmp_source_emit_mode_conditional >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `B cs ss`)) >>
  disch_then (drule_at (Pat `MEM inst (fn_insts fn)`)) >>
  simp[] >> disch_then (qspecl_then [`own`, `initial_fmp`, `env`, `allow_own`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  rename1 `sym_steps_mode allow_own p env own 1 ss = SymOK mid` >>
  `mid.sym_base.as_pc = ss.sym_base.as_pc + 1 /\ mid.sym_mem_labels = ss.sym_mem_labels` by
    (drule (Q.SPECL [`allow_own`, `own`] sym_initial_fmp_run_mode) >>
     disch_then (qspecl_then [`own`, `env`, `allow_own`] mp_tac) >>
     simp[] >> strip_tac >> gvs[asmSemTheory.asm_next_def]) >>
  `(!out. inst.inst_outputs = [out] ==> stack_get_depth (Var out) emitted.ps_stack = SOME 0) /\
    LENGTH inst.inst_outputs <= 1` by
    simp[stack_get_depth_def, stack_push_def, listTheory.REVERSE_SNOC, stack_find_def] >>
  `(if inst.inst_outputs = [] \/ halt then ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted) = (pops,ps8) /\
   (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
    else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9)` by
    (Cases_on `MEM x nl` >> gvs[]) >>
  `sym_kinds_ok cplan fn ret srest emitted mid /\
   asm_block_at p mid.sym_base.as_pc (execute_plan initial_fmp (pops ++ opts))` by
    gvs[] >>
  drule_all (Q.INST [`inst` |-> `inst`, `is_halting` |-> `halt`, `next_term` |-> `term`]
    sym_regular_generated_postfix_sim_marked) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  rename1 `sym_steps p env (LENGTH (execute_plan initial_fmp (pops ++ opts))) mid = SymOK final` >>
  qexists `final` >> conj_tac
  >- (`sym_steps_mode allow_own p env own (1 + LENGTH (execute_plan initial_fmp (pops ++ opts))) ss = SymOK final`
        suffices_by
        simp[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
          planExecTheory.exec_stack_op_def, arithmeticTheory.ADD1] >>
      simp[Once sym_steps_mode_add, sym_steps_mode_ok]) >> gvs[]
QED

Theorem sym_initial_fmp_generated_cleanup_own:
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_outputs = [x] /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  emitted = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled /\
  (if halt then ([],emitted)
   else popmany_plan (if MEM x nl then [] else [Var x]) emitted) = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8)) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  asm_static_wf p /\ code_labels_agree p lo /\ asm_sym_rel_own lo p env own cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts))) ==>
  ?final. sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts)))) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. ~R b ==> FLOOKUP final.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel_own lo p env own cs' ss'` by metis_tac[asm_sym_steps_mode_sim] >>
  drule_all (Q.INST [`B` |-> `asm_sym_rel_own lo p env own`]
    sym_initial_fmp_generated_cleanup_mode_core) >> simp[]
QED

Theorem sym_initial_fmp_inst_symbolic_run_mode_core:
  (!n cs ss ss'. B cs ss /\ sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\ B cs' ss') /\
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_operands = [] /\ inst.inst_outputs = [x] /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  EVERY (\op. EVERY (\out. case op of Var v => v <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var v => v <> out | _ => T) inst.inst_outputs) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\ qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  B cs ss /\ ss.sym_base.as_pc = cs.as_pc /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> drule_all initial_fmp_plan_decompose >> strip_tac >>
  qmatch_asmsub_abbrev_tac `popmany_plan _ emitted` >>
  `deepResidualBudget$plan_state_residual_wf_marked sb [] 0 ps` by
    (drule deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil >>
     simp[deepResidualBudgetTheory.plan_state_residual_wf_marked_def,
       deepResidualBudgetTheory.residual_budget_wf_marked_def]) >>
  `generated_plan_state_wf_marked sb emitted` by
    (irule deepResidualSimTheory.materialised_emit_resources_marked >>
     qexistsl [`0`, `inst.inst_outputs`, `ps`, `[]`] >>
     simp[Abbr `emitted`, stack_pop_def]) >>
  `(if inst.inst_outputs = [] \/ halt then ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted) = (pops,ps8) /\
   (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
    else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9)` by
    (Cases_on `MEM x nl` >> gvs[]) >>
  drule_at (Pat `generated_plan_state_wf_marked sb emitted`) sym_regular_postfix_applicability >>
  disch_then (drule_at (Pat `_ = (pops,ps8)`)) >>
  disch_then (drule_at (Pat `_ = (opts,ps9)`)) >>
  disch_then (drule_at (Pat `qs = release_dead_spills _ _`)) >>
  disch_then (drule_at (Pat `MEM r cplan.cp_regions`)) >>
  disch_then (qspecl_then [`fn.fn_name`, `ctx`] mp_tac) >> simp[] >> strip_tac >>
  `!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >> simp[listTheory.EVERY_MEM] >>
     rpt strip_tac >> qpat_x_assum `!s. _` (qspec_then `SOSpill off` mp_tac) >> simp[]) >>
  `ssa_form fn /\ spill_alloc_layout_wf emitted.ps_alloc emitted.ps_spilled /\
   asm_block_at prog ss.sym_base.as_pc
     (execute_plan cplan.cp_initial_fmp ([SOInitialFmp] ++ (pops ++ opts)))` by
    (gvs[codegen_ready_fn_def, fnPlanPrefixTheory.generated_plan_state_wf_marked_def]) >>
  `!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan fn.fn_name b /\ context_spill_byte cplan b` by
    (rewrite_tac[listTheory.MEM_APPEND] >> first_assum MATCH_ACCEPT_TAC) >>
  `emitted = ps with ps_stack := stack_push (Var x) ps.ps_stack` by simp[Abbr `emitted`] >>
  drule_all (Q.INST [`R` |-> `closure_spill_byte ctx cplan fn.fn_name`]
    sym_initial_fmp_generated_cleanup_mode_core) >>
  strip_tac >> qexists `final` >>
  conj_tac >- (qpat_x_assum `sym_steps_mode _ _ _ _ _ _ = SymOK final` mp_tac >> simp[]) >>
  conj_tac >- (qpat_x_assum `sym_kinds_ok _ _ _ _ _ final` mp_tac >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!b. ~closure_spill_byte _ _ _ b ==> _` (drule_then SUBST1_TAC) >>
  first_assum irule >> simp[]
QED

Theorem sym_initial_fmp_inst_symbolic_run_own:
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_operands = [] /\ inst.inst_outputs = [x] /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  EVERY (\op. EVERY (\out. case op of Var v => v <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var v => v <> out | _ => T) inst.inst_outputs) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\ qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_static_wf prog /\ code_labels_agree prog lo /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss'` by metis_tac[asm_sym_steps_mode_sim] >>
  `asm_sym_rel_own lo prog env own cs ss /\ ss.sym_base.as_pc = cs.as_pc /\
   sym_kinds_ok cplan fn ret srest ps ss /\
   (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b)` by
    (fs[sym_frame_inv_own_def] >> metis_tac[asmSymForwardOwnTheory.asm_sym_rel_own_pc]) >>
  drule_all (Q.INST [`B` |-> `asm_sym_rel_own lo prog env own`]
    sym_initial_fmp_inst_symbolic_run_mode_core) >> simp[]
QED

Theorem sym_istore_inst_symbolic_run_mode_core:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = ISTORE /\ inst_wf inst /\ inst.inst_operands = [dst; value] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\ qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  LENGTH [dst; value] <= LENGTH (SND (emit_input_plan ISTORE [dst; value] nl ps)).ps_stack /\
  (!op. MEM op [dst; value] /\ is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [dst; value] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [dst; value] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [dst; value] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [dst; value]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [dst; value] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> drule_all istore_plan_decompose >> strip_tac >>
  rename1 `emit_input_plan ISTORE [dst; value] nl ps = (iops,prepared)` >>
  rename1 `reorder_plan _ [dst; value] prepared = (rops,arranged)` >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
   arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (gvs[allocMonoTheory.release_dead_spills_spill_base,
      allocMonoTheory.release_dead_spills_next_offset] >>
     metis_tac[allocMonoTheory.emit_input_plan_spill_base,
       allocMonoTheory.reorder_plan_spill_base]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
   asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[listTheory.EVERY_APPEND, stackOpSimTheory.execute_plan_append,
      stackOpSimTheory.asm_block_at_append] >>
  `emit_input_plan inst.inst_opcode [dst; value] nl ps = (iops,prepared)` by simp[] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (Q.INST [`initial_fmp` |-> `cplan.cp_initial_fmp`, `labs0` |-> `labs0`]
      (SPEC_ALL sym_frame_selected_prefix_paired_mode_conditional))) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`sb`, `r`, `labs0`, `qs`] mp_tac) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (conj_tac >- (qexists `m` >> simp[]) >>
         rpt strip_tac >>
         qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = _ ==> _`
           (qspecl_then [`i`, `l`, `d`, `j`] mp_tac) >> simp[]) >>
     conj_tac >- (qpat_x_assum `LENGTH [dst; value] <= _` mp_tac >> simp[]) >>
     qpat_x_assum `!op at. _ /\ _ /\ operand_equiv dfg op at ==> _` mp_tac >> simp[])) >> strip_tac >>
  `asm_block_at prog ready.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"]` by
    gvs[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
      planExecTheory.exec_stack_op_def, stackOpSimTheory.asm_block_at_append] >>
  drule_at (Pat `venom_asm_rel _ arranged _ mid`)
    (Q.INST [`own` |-> `own`, `env` |-> `env`, `nl` |-> `nl`, `allow_own` |-> `allow_own`]
      (SPEC_ALL sym_istore_prepared_run_mode_core)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ ready`)) >>
  disch_then (drule_at (Pat `inst.inst_opcode = ISTORE`)) >>
  disch_then (drule_at (Pat `asm_block_at _ ready.sym_base.as_pc _`)) >>
  disch_then (drule_at (Pat `LIST_REL _ localtop mid.as_stack`)) >>
  disch_then (drule_at (Pat `MEM fn ctx.ctx_functions`)) >>
  simp[] >> disch_then (qspec_then `stack_pop 2 arranged.ps_stack` mp_tac) >>
  disch_then (qspecl_then [`own`, `nl`, `env`, `allow_own`] mp_tac) >>
  (impl_tac >-
    (simp[venomMemPropsTheory.eval_operand_with_memory,
      genFrameSimTheory.operand_val_memory_update] >>
     rpt conj_tac
     >- (qpat_x_assum `EVERY _ [dst; value]` mp_tac >> simp[] >> rpt strip_tac >> simp[])
     >- (qpat_x_assum `EVERY _ [dst; value]` mp_tac >> simp[] >> rpt strip_tac >> simp[]) >>
     qpat_x_assum `!op. MEM op [dst; value] ==> _` mp_tac >> simp[])) >> strip_tac >>
  qexists `full` >> conj_tac
  >- (`sym_steps_mode allow_own prog env own
        (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) + 2) ss = SymOK full`
       suffices_by
       simp[stackOpSimTheory.execute_plan_append, planExecTheory.execute_plan_def,
         planExecTheory.exec_stack_op_def] >>
      simp[Once sym_steps_mode_add]) >>
  conj_tac >-
    (qpat_x_assum `qs = _` (fn th => pure_rewrite_tac [th]) >>
     qpat_x_assum `sym_kinds_ok _ _ _ _ _ full` mp_tac >>
     qpat_x_assum `arranged.ps_stack = _` (fn th => pure_once_rewrite_tac [GSYM th]) >>
     simp[NoAsms]) >>
  rpt strip_tac >>
  `FLOOKUP full.sym_mem_labels b = FLOOKUP ready.sym_mem_labels b` by simp[] >>
  `FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b` by simp[] >>
  `FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b` by simp[] >> simp[]
QED

Theorem sym_istore_inst_symbolic_run_own:
  inst.inst_opcode = ISTORE /\ inst_wf inst /\ inst.inst_operands = [dst; value] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\ ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\ qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  LENGTH [dst; value] <= LENGTH (SND (emit_input_plan ISTORE [dst; value] nl ps)).ps_stack /\
  (!op. MEM op [dst; value] /\ is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [dst; value] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [dst; value] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [dst; value] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [dst; value]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [dst; value] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ asm_static_wf prog /\
  code_labels_agree prog lo /\
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps_mode allow_own prog env own (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `!n cs ss ss'. bridge_core lo
      (\code. asm_data_env_lo_ok lo prog env own /\ code = own) cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      bridge_core lo (\code. asm_data_env_lo_ok lo prog env own /\ code = own) cs' ss'` by
    (simp[asmSymBridgeTheory.asm_sym_rel_core_own] >> metis_tac[asm_sym_steps_mode_sim]) >>
  `bridge_core lo (\code. asm_data_env_lo_ok lo prog env own /\ code = own) cs ss /\
   sym_kinds_ok cplan fn ret srest ps ss /\
   (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
   (fn_has_retpc fn ==> MEM (AsmLabel ret) prog)` by
    fs[asmSymBridgeTheory.asm_sym_rel_core_own, sym_frame_inv_own_def] >>
  drule (CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO))
    (SPEC_ALL sym_istore_inst_symbolic_run_mode_core)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `MEM r cplan.cp_regions`)) >>
  disch_then (qspecl_then [`value`, `labs0`, `dst`] mp_tac) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (qpat_x_assum `!op at. _ /\ _ /\ operand_equiv dfg op at ==> _` mp_tac >> simp[]) >>
     conj_tac >- (qexists `m` >> simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!i l d j. FLOOKUP ss.sym_mem_labels i = _ ==> _`
       (qspecl_then [`i`, `l`, `d`, `j`] mp_tac) >> simp[])) >> simp[]
QED

Theorem sym_istore_prepared_run_own:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel_own lo p env own cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "SWAP1"; AsmOp "MSTORE"] ==>
  ?full. sym_steps_mode allow_own p env own 2 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 2 ps.ps_stack)) full
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) localtop cs.as_stack` by
    fs[asmSymBridgeTheory.asm_sym_rel_own_def] >>
  drule_all sym_istore_prepared_run_mode_core >> simp[]
QED

Theorem sym_bump_prepared_local_emit_mode_core:
  (!cs ss. R cs ss ==> ss.sym_base.as_pc = cs.as_pc) /\
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  R cs ss /\ sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps vs cs /\ ps.ps_stack = residual ++ [base_op; size_op] /\
  base_op <> dead_stack_marker /\ size_op <> dead_stack_marker /\
  operand_val vs lo base_op = SOME base_val /\ operand_val vs lo size_op = SOME sz /\
  EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> ptr /\ x <> next | _ => T) /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?cs' ss'. asm_steps lo (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    venom_asm_rel lo qs (update_var next (base_val + sz) (update_var ptr base_val vs)) cs' /\
    cs'.as_pc = cs.as_pc + 2 /\
    sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret [] qs ss' /\
    qs.ps_stack = residual ++ [Var ptr; Var next]
Proof
  strip_tac >>
  `asm_block_at p cs.as_pc (execute_plan 0 bump_emit_ops)` by
    (gvs[stackPlanGenTheory.bump_emit_ops_def, planExecTheory.execute_plan_def,
      planExecTheory.exec_stack_op_def, planExecTheory.dup_name_def] >> metis_tac[]) >>
  drule_at (Pat `venom_asm_rel _ _ _ _`) emitSimTheory.bump_emit_sim >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`build_offset_to_pc p`, `ptr`, `next`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  drule_at (Pat `asm_steps _ _ _ _ _ = _`) sym_bump_source_emit_mode_conditional >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `R cs ss`)) >>
  disch_then (drule_at (Pat `MEM inst (fn_insts fn)`)) >>
  simp[] >> disch_then (qspecl_then [`own`, `env`, `ctx`, `allow_own`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  goal_assum (drule_at Any) >>
  simp[stackModelTheory.stack_push_def, stackModelTheory.stack_pop_def,
    listTheory.SNOC_APPEND, rich_listTheory.BUTLASTN_APPEND2, listTheory.TAKE_APPEND1]
QED

Theorem sym_bump_prepared_local_emit_own:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ code_labels_agree p lo /\ asm_sym_rel_own lo p env own cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps vs cs /\ ps.ps_stack = residual ++ [base_op; size_op] /\
  base_op <> dead_stack_marker /\ size_op <> dead_stack_marker /\
  operand_val vs lo base_op = SOME base_val /\ operand_val vs lo size_op = SOME sz /\
  EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> ptr /\ x <> next | _ => T) /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?cs' ss'. asm_steps lo (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    venom_asm_rel lo qs (update_var next (base_val + sz) (update_var ptr base_val vs)) cs' /\
    cs'.as_pc = cs.as_pc + 2 /\
    sym_steps_mode allow_own p env own 2 ss = SymOK ss' /\
    asm_sym_rel_own lo p env own cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ sym_kinds_ok cplan fn ret [] qs ss' /\
    qs.ps_stack = residual ++ [Var ptr; Var next]
Proof
  strip_tac >> irule sym_bump_prepared_local_emit_mode_core >>
  simp[] >> rpt conj_tac
  >- metis_tac[asmSymForwardOwnTheory.asm_sym_rel_own_pc]
  >- metis_tac[asm_sym_steps_mode_sim]
  >- metis_tac[] >>
  qexistsl [`base_op`, `inst`, `ps`, `size_op`] >> simp[]
QED

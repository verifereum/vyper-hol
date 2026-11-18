(* Numeric GAS and POP kernels, shared across relocated execution modes. *)
Theory symControlGasOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel symPlannerMoves symPostfixSim
  symShuffleSim gasFrameSim fnFrameDeepGas fnFrameStepsRevertForward
  asmSplice asmSymSem asmSem frameRel contextCodegenRel unitShapeDefs
  stackPlanGen stackPlanTypes planExec venomExecSemantics venomState venomInst
  dfgDefs fnPlanPrefix allocMono

val control_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", control_bridge_core_tm);
val _ = Parse.temp_overload_on ("control_frame", ``\lo code_ok p ctx cplan fn ret srest labs0 ps cs ss.
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b) /\
  (fn_has_retpc fn ==> MEM (AsmLabel ret) p)``);

Theorem sym_kinds_ok_pop:
  !cplan fn ret srest ps ss op sv stk base'.
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := SNOC op ps.ps_stack) ss /\
  ss.sym_stack = sv :: stk ==>
  sym_kinds_ok cplan fn ret srest ps
    (ss with <|sym_base := base'; sym_stack := stk|>)
Proof
  rw[sym_kinds_ok_def] >>
  gvs[listTheory.REVERSE_SNOC, listTheory.LIST_REL_CONS1] >> metis_tac[]
QED

Theorem noncopy_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM out inst.inst_outputs /\
  inst.inst_opcode <> ADD /\ inst.inst_opcode <> ASSIGN ==>
  ~code_end_var fn out
Proof
  rpt strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem sym_gas_output_not_code_end:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  ~code_end_var fn out
Proof
  strip_tac >> irule noncopy_output_not_code_end >>
  conj_tac >- fs[codegen_ready_fn_def] >>
  qexists_tac `inst` >> simp[]
QED

Theorem sym_gas_output_kind:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  op_kind_ok fn ret (Var out) (Val w)
Proof
  strip_tac >>
  `~retpc_var fn out /\ ~code_end_var fn out` by
    metis_tac[gasFrameSimTheory.gas_output_non_retpc,
              sym_gas_output_not_code_end] >>
  simp[op_kind_ok_def]
QED

Theorem sym_step_gas:
  sym_step p env (AsmOp "GAS") ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  `asm_op_arity "GAS" = 0 /\
   ALOOKUP dup_table "GAS" = NONE /\
   ALOOKUP swap_table "GAS" = NONE /\
   ALOOKUP log_table "GAS" = NONE` by EVAL_TAC >>
  Cases_on `ss.sym_base.as_gas_readings` >>
  simp[sym_step_def, sym_step_op_def, sym_step_concrete_def,
       mem_labels_hit_def, asm_op_mem_reads_def, mem_labels_clear_def,
       asm_op_mem_writes_def, GSYM pred_setTheory.UNIV_DEF,
       finite_mapTheory.DRESTRICT_UNIV, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, asm_gas_def, asm_push_val_def, asm_next_def,
       sym_lift_def, sym_state_component_equality, asm_state_component_equality]
QED

Theorem sym_gas_steps:
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  strip_tac >>
  rewrite_tac[arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[asm_block_at_def, sym_step_gas]
QED

Theorem sym_gas_kinds_steps:
  !cplan fn ret srest ps ss p env out.
  sym_kinds_ok cplan fn ret srest ps ss /\
  op_kind_ok fn ret (Var out)
    (Val (HD (ss.sym_base.as_gas_readings ++ [0w]))) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  rpt gen_tac >> strip_tac >>
  drule sym_gas_steps >> disch_then (qspec_then `env` assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule symShuffleSimTheory.sym_kinds_ok_push >> simp[]
QED

Theorem sym_pop_pushed_steps:
  ss.sym_stack = sv :: stk /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "POP"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := ss.sym_base.as_pc + 1;
                    sym_stack := stk|>)
Proof
  strip_tac >> rewrite_tac[arithmeticTheory.ONE, asmSpliceTheory.sym_steps_def] >>
  gvs[asm_block_at_def, sym_step_def, sym_step_op_def, sym_set_stack_def,
      asm_next_def]
QED

Theorem sym_gas_optimistic_steps:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule gasFrameSimTheory.gas_optimistic_cases >> strip_tac
  >- (gvs[execute_plan_def, asmSpliceTheory.sym_steps_def]) >>
  `dist < LENGTH ps.ps_stack` by metis_tac[planWfTheory.stack_get_depth_bound] >>
  drule allocMonoTheory.do_swap_spill_base >> strip_tac >>
  `r.sr_spill_base <= ps.ps_alloc.sa_spill_base` by metis_tac[] >>
  drule_all_then MATCH_ACCEPT_TAC symPlannerMovesTheory.sym_do_swap
QED

Theorem sym_gas_emit_steps:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >>
  `op_kind_ok fn ret (Var out)
    (Val (HD (ss.sym_base.as_gas_readings ++ [0w])))` by
    metis_tac[sym_gas_output_kind] >>
  drule_all sym_gas_kinds_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> simp[] >>
  drule sym_gas_steps >> disch_then (qspec_then `env` assume_tac) >> gvs[]
QED

Theorem sym_pop_pushed_kinds_steps:
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := SNOC op ps.ps_stack) ss /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "POP"] ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  strip_tac >>
  `?sv stk. ss.sym_stack = sv :: stk` by
    (fs[sym_kinds_ok_def, listTheory.REVERSE_SNOC, listTheory.LIST_REL_CONS1] >>
     gvs[]) >>
  drule_all sym_pop_pushed_steps >> disch_then (qspec_then `env` assume_tac) >>
  goal_assum (drule_at Any) >> simp[] >>
  irule sym_kinds_ok_pop >> metis_tac[]
QED

Theorem sym_gas_live_plan_steps:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  optimistic_swap_plan dfg inst nl term
    (ps with ps_stack := SNOC (Var out) ps.ps_stack) = (tail, arranged) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) tail /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (SOEmit "GAS" :: tail)) ==>
  ?last.
    sym_steps p env (LENGTH (execute_plan initial_fmp (SOEmit "GAS" :: tail))) ss = SymOK last /\
    sym_kinds_ok cplan fn ret srest (release_dead_spills nl arranged) last /\
    last.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (SOEmit "GAS" :: tail)) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `execute_plan initial_fmp (SOEmit "GAS" :: tail) =
    AsmOp "GAS" :: execute_plan initial_fmp tail` by
    simp[execute_plan_def, exec_stack_op_def] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"]` by
    (fs[stackOpSimTheory.asm_block_at_cons] >>
     simp[stackOpSimTheory.asm_block_at_cons, asm_block_at_def]) >>
  `MEM out inst.inst_outputs` by simp[] >>
  drule_all sym_gas_emit_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan initial_fmp tail)` by
    fs[stackOpSimTheory.asm_block_at_cons] >>
  `spill_alloc_layout_wf (ps with ps_stack := SNOC (Var out) ps.ps_stack).ps_alloc
    (ps with ps_stack := SNOC (Var out) ps.ps_stack).ps_spilled` by simp[] >>
  drule_all sym_gas_optimistic_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss''` >> simp[] >> conj_tac
  >- (pure_rewrite_tac[arithmeticTheory.ADD1] >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      rewrite_tac[sym_steps_add] >> simp[]) >>
  irule sym_kinds_ok_release_dead_spills >> simp[]
QED

Theorem sym_gas_retained_plan_steps:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOEmit "GAS"]) ==>
  ?ss'.
    sym_steps p env (LENGTH (execute_plan initial_fmp [SOEmit "GAS"])) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := SNOC (Var out) ps.ps_stack)) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOEmit "GAS"]) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"] = [AsmOp "GAS"]` by
    simp[execute_plan_def, exec_stack_op_def] >>
  gvs[] >> `MEM out inst.inst_outputs` by simp[] >>
  drule_all sym_gas_emit_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> simp[] >> irule sym_kinds_ok_release_dead_spills >> simp[]
QED

Theorem sym_gas_pop_plan_steps:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1]) ==>
  ?ss'.
    sym_steps p env (LENGTH (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1])) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest (release_dead_spills nl ps) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1]) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> gvs[] >>
  `execute_plan initial_fmp [SOEmit "GAS"; SOPop 1] = [AsmOp "GAS"; AsmOp "POP"]` by EVAL_TAC >>
  gvs[] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"]` by
    (fs[stackOpSimTheory.asm_block_at_cons] >>
     simp[stackOpSimTheory.asm_block_at_cons, asm_block_at_def]) >>
  `MEM out inst.inst_outputs` by simp[] >>
  drule_all sym_gas_emit_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc [AsmOp "POP"]` by
    fs[stackOpSimTheory.asm_block_at_cons] >>
  drule_all sym_pop_pushed_kinds_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss''` >> simp[] >> conj_tac
  >- (pure_rewrite_tac[arithmeticTheory.TWO, arithmeticTheory.ADD1] >>
      rewrite_tac[sym_steps_add] >> simp[]) >>
  irule sym_kinds_ok_release_dead_spills >> simp[]
QED

Theorem sym_gas_plan_steps:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'.
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> drule_all gasFrameSimTheory.gas_plan_shape >> disch_then assume_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[] >>
  qpat_x_assum `!ps next_liveness next_is_term liveness is_halting fn dfg cfg bb_label. _` kall_tac >>
  Cases_on `MEM out nl` >> simp[]
  >- (Cases_on `optimistic_swap_plan dfg inst nl term
        (ps with ps_stack := SNOC (Var out) ps.ps_stack)` >>
      simp[] >> strip_tac >>
      gvs[allocMonoTheory.release_dead_spills_spill_base,
          allocMonoTheory.release_dead_spills_next_offset] >>
      drule_all sym_gas_live_plan_steps >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  Cases_on `halting` >> simp[]
  >- (rw[] >> drule_all sym_gas_retained_plan_steps >>
      disch_then (qspecl_then [`nl`, `env`] strip_assume_tac) >>
      qexists `ss'` >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rw[] >> drule_all sym_gas_pop_plan_steps >>
  disch_then (qspecl_then [`nl`, `env`] strip_assume_tac) >>
  qexists `ss'` >> simp[]
QED


Theorem sym_gas_plan_frame_sim_mode_conditional:
  (!n cs ss ss'. bridge_core lo code_ok cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
      bridge_core lo code_ok cs' ss') /\
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  control_frame lo code_ok p ctx cplan fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps_mode allow_own p env own (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    control_frame lo code_ok p ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `ss.sym_base.as_pc = cs.as_pc` by
    gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by simp[] >>
  drule_all sym_gas_plan_steps >> disch_then (qspec_then `env` strip_assume_tac) >>
  drule sym_steps_mode_ok >>
  disch_then (qspecl_then [`own`, `allow_own`] assume_tac) >>
  qpat_x_assum `!n cs ss ss'. _` (drule_all_then strip_assume_tac) >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  reverse conj_tac
  >- gvs[asmSymBridgeTheory.asm_sym_rel_core_pc] >>
  reverse conj_tac >- metis_tac[sym_frame_region_labels_transfer] >>
  conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

Theorem sym_gas_frame_sim_deep_mode_kernel:
  !allow_own own code_ok fuel ctx cplan lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    (!n cs ss ss'. bridge_core lo code_ok cs ss /\
      sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
      ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
        bridge_core lo code_ok cs' ss') /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode = GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    source_memory_reads_disjoint cplan inst vs /\
    context_source_memory_writes_disjoint cplan inst vs /\
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\ inst_wf inst /\
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
             EL i (execute_plan cplan.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    control_frame lo code_ok prog ctx cplan fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cplan vs vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cplan lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
        sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
        control_frame lo code_ok prog ctx cplan fn ret srest labs0 ps' as' ss'
Proof
  rpt gen_tac >> disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  gen_tac >> strip_tac >>
  drule_all fnFrameDeepGasTheory.gas_inst_frame_sim_owned_deep_exact_reloc >>
  strip_tac >>
  drule_all gasFrameSimTheory.gas_source_shape >> strip_tac >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  drule_all sym_gas_plan_frame_sim_mode_conditional >> strip_tac >>
  gvs[] >> qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp ops)`, `as'`, `ss'`] >>
  simp[] >> conj_tac >- (qexists `m` >> simp[]) >> metis_tac[]
QED

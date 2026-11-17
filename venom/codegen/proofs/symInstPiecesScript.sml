(* Symbolic special instruction branches, with exact code-length counts. *)
Theory symInstPieces
Ancestors
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst
  symEmitStoreOwn symInstPiecesFacts symInstNamedOwn symInstAssertOwn
  symInstEmissionOwn symInstLocalizeCore
  symInstAssertPrepareOwn symInstAssertSuffixOwn

Theorem sym_phi_dup_rename:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME d /\ do_dup d ps = (ops,qs) /\
  sym_kinds_ok cplan fn ret srest qs ss ==>
  sym_kinds_ok cplan fn ret srest
    (qs with ps_stack := stack_poke 0 (Var x) qs.ps_stack) ss
Proof
  metis_tac[symInstPhiOwnTheory.sym_phi_dup_rename_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_phi_live_prefix_sim:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME d /\ do_dup d ps = (ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp (ops ++ [SOPoke 0 (Var x)])) ==>
  ?ss'. sym_steps p env
      (LENGTH (execute_plan initial_fmp (ops ++ [SOPoke 0 (Var x)]))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest
      (qs with ps_stack := stack_poke 0 (Var x) qs.ps_stack) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp (ops ++ [SOPoke 0 (Var x)])) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_phi_live_prefix_sim_mode)) >> simp[]
QED

Theorem sym_phi_dead_prefix_sim:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME d /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_steps p env (LENGTH (execute_plan initial_fmp [SOPoke d (Var x)])) ss = SymOK ss /\
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack) ss
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_phi_dead_prefix_sim_mode)) >> simp[]
QED

Theorem sym_singleton_cleanup_sim:
  popmany_plan [v] ps = (ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  MATCH_ACCEPT_TAC (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_singleton_cleanup_sim_mode))
QED

Theorem sym_phi_dead_cleanup_sim:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  popmany_plan [Var x] (ps with ps_stack := stack_poke d (Var x) ps.ps_stack) = (ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (SOPoke d (Var x) :: ops)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (SOPoke d (Var x) :: ops))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (SOPoke d (Var x) :: ops)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_phi_dead_cleanup_sim_mode)) >> simp[]
QED

Theorem sym_phi_live_cleanup_sim:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  do_dup d ps = (dup_ops,dup_ps) /\
  popmany_plan [Var x]
    (dup_ps with ps_stack := stack_poke 0 (Var x) dup_ps.ps_stack) = (pop_ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) (dup_ops ++ [SOPoke 0 (Var x)] ++ pop_ops) ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) (dup_ops ++ [SOPoke 0 (Var x)] ++ pop_ops) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp ((dup_ops ++ [SOPoke 0 (Var x)]) ++ pop_ops)) ==>
  ?ss'. sym_steps p env
      (LENGTH (execute_plan initial_fmp ((dup_ops ++ [SOPoke 0 (Var x)]) ++ pop_ops))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp ((dup_ops ++ [SOPoke 0 (Var x)]) ++ pop_ops)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_phi_live_cleanup_sim_mode)) >> simp[]
QED

Theorem sym_phi_plan_sim:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [x] /\ inst.inst_opcode = PHI /\
  generate_phi_plan inst nl halt ps = (ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SOSpill off) ops ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPhiOwnTheory.sym_phi_plan_sim_mode)) >> simp[]
QED

Theorem stack_push_pop_one_poke:
  !stk out. 0 < LENGTH stk ==>
    stack_push out (stack_pop 1 stk) = stack_poke 0 out stk
Proof
  MATCH_ACCEPT_TAC symInstAssignOwnTheory.stack_push_pop_one_poke
QED

Theorem sym_assign_output_state:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_outputs = [x] /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  label_positions_ok inst /\ stack_peek 0 ps.ps_stack = op /\
  0 < LENGTH ps.ps_stack /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_push (Var x) (stack_pop 1 ps.ps_stack)) ss
Proof
  MATCH_ACCEPT_TAC symInstAssignOwnTheory.sym_assign_output_state
QED

Theorem sym_assign_postfix_sim:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_outputs = [x] /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  label_positions_ok inst /\ stack_peek 0 ps.ps_stack = op /\
  0 < LENGTH ps.ps_stack /\
  ps7 = ps with ps_stack := stack_push (Var x) (stack_pop 1 ps.ps_stack) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (pops ++ opts)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (pops ++ opts))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (pops ++ opts)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  MATCH_ACCEPT_TAC (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstAssignOwnTheory.sym_assign_postfix_sim_mode))
QED

Theorem sym_assign_plan_sim:
  ssa_form fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_outputs = [x] /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ label_positions_ok inst /\
  (is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan ASSIGN [op] nl ps = (iops,prepared) /\
  reorder_plan dfg [op] prepared = (rops,arranged) /\
  1 <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  op <> dead_stack_marker /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  stack_peek 0 arranged.ps_stack = op /\ 0 < LENGTH arranged.ps_stack /\
  ps7 = arranged with ps_stack := stack_push (Var x) (stack_pop 1 arranged.ps_stack) /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  (!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp ((iops ++ rops) ++ (pops ++ opts))) ==>
  ?ss'. sym_steps p env
      (LENGTH (execute_plan initial_fmp ((iops ++ rops) ++ (pops ++ opts)))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan initial_fmp ((iops ++ rops) ++ (pops ++ opts))) /\
    (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  MATCH_ACCEPT_TAC (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstAssignOwnTheory.sym_assign_plan_sim_mode))
QED

(* Caller boundary for the singleton ASSIGN preparation. *)
Theorem sym_assign_preparation_facts:
  (is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  residual_budget_wf_marked sb [] ps /\
  emit_input_plan ASSIGN [op] nl ps = (iops,prepared) /\
  reorder_plan dfg [op] prepared = (rops,arranged) /\
  1 <= LENGTH prepared.ps_stack ==>
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  stack_peek 0 arranged.ps_stack = op /\ 0 < LENGTH arranged.ps_stack
Proof
  strip_tac >>
  `(!v. MEM v [op] /\ is_var_operand v ==>
      MEM v ps.ps_stack \/ v IN FDOM ps.ps_spilled) /\
    PERM [op] [op] /\ LENGTH [op] <= 16 /\
    LENGTH [op] <= LENGTH prepared.ps_stack` by simp[] >>
  drule_all deepResidualSimTheory.selected_input_arranged_marked >>
  simp[deepResidualBudgetTheory.plan_state_residual_wf_marked_def] >>
  strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem singleton_cleanup_ops_bounded:
  popmany_plan [v] ps = (ops,qs) /\ plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.singleton_cleanup_ops_bounded
QED

Theorem phi_optional_cleanup_ops_bounded:
  (if cleanup then popmany_plan [v] ps else ([],ps)) = (ops,qs) /\
  plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops /\
  ps.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset
Proof
  Cases_on `cleanup` >> simp[] >> strip_tac
  >- metis_tac[singleton_cleanup_ops_bounded, allocMonoTheory.popmany_plan_next_offset] >>
  gvs[] >> simp[]
QED

Theorem phi_dup_cleanup_ops_bounded:
  plan_slots_bounded sb ps /\ d < LENGTH ps.ps_stack /\
  do_dup d ps = (dups,dup_ps) /\
  (if cleanup then popmany_plan [v]
     (dup_ps with ps_stack := stack_poke 0 v dup_ps.ps_stack)
   else ([],dup_ps with ps_stack := stack_poke 0 v dup_ps.ps_stack)) = (pops,qs) ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (dups ++ [SOPoke 0 v] ++ pops)
Proof
  strip_tac >> drule_all planSpillBoundsTheory.do_dup_slots_bounded >> strip_tac >>
  `plan_slots_bounded sb
    (dup_ps with ps_stack := stack_poke 0 v dup_ps.ps_stack)` by
    (fs[planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
  drule_all phi_optional_cleanup_ops_bounded >>
  simp[planSpillBoundsTheory.ops_spill_bounded_append,
    planSpillBoundsTheory.ops_spill_bounded_def] >>
  metis_tac[planSpillBoundsTheory.ops_spill_bounded_def, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem phi_poke_cleanup_ops_bounded:
  plan_slots_bounded sb ps /\
  (if cleanup then popmany_plan [v]
     (ps with ps_stack := stack_poke d v ps.ps_stack)
   else ([],ps with ps_stack := stack_poke d v ps.ps_stack)) = (pops,qs) ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (SOPoke d v :: pops)
Proof
  simp[planSpillBoundsTheory.ops_spill_bounded_def] >> strip_tac >>
  `plan_slots_bounded sb (ps with ps_stack := stack_poke d v ps.ps_stack)` by
    (fs[planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
  drule_all phi_optional_cleanup_ops_bounded >>
  simp[planSpillBoundsTheory.ops_spill_bounded_def] >> metis_tac[]
QED

Theorem generate_phi_plan_ops_bounded:
  generate_phi_plan inst nl halt ps = (ops,qs) /\ plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops
Proof
  strip_tac >> qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (strip_tac >> gvs[] >> simp[]) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_phi_depth_var_not_marker] >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) nl`
  >- suspend "dup" >> suspend "poke"
QED

Resume generate_phi_plan_ops_bounded[dup]:
  Cases_on `do_dup d ps` >> rename1 `do_dup d ps = (dups,dup_ps)` >> simp[] >>
  Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) nl` >> simp[]
  >- (pairarg_tac >> strip_tac >> gvs[] >>
      irule phi_dup_cleanup_ops_bounded >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule_all planSpillBoundsTheory.do_dup_slots_bounded >>
  simp[planSpillBoundsTheory.ops_spill_bounded_append,
    planSpillBoundsTheory.ops_spill_bounded_def] >> metis_tac[]
QED

Resume generate_phi_plan_ops_bounded[poke]:
  simp[] >> Cases_on `~halt /\ ~MEM (HD inst.inst_outputs) nl` >> simp[]
  >- (pairarg_tac >> strip_tac >> gvs[] >>
      irule phi_poke_cleanup_ops_bounded >> simp[] >> metis_tac[]) >>
  strip_tac >> gvs[planSpillBoundsTheory.ops_spill_bounded_def]
QED
Finalise generate_phi_plan_ops_bounded

Theorem generate_phi_plan_ops_region_confined:
  generate_phi_plan inst nl halt ps = (ops,qs) /\ plan_slots_bounded sb ps /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\ r.sr_spill_base <= sb /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  !off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b
Proof
  strip_tac >> drule_all generate_phi_plan_ops_bounded >>
  metis_tac[scratch_ops_region_confined]
QED

Theorem optimistic_swap_ops_bounded:
  optimistic_swap_plan dfg inst nl term ps = (ops,qs) /\ plan_slots_bounded sb ps ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset ops
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.optimistic_swap_ops_bounded
QED

Theorem assign_postfix_ops_bounded:
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.assign_postfix_ops_bounded
QED

Theorem assign_postfix_ops_region_confined:
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= sb /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  !off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\ context_spill_byte cplan b
Proof
  strip_tac >> drule_all assign_postfix_ops_bounded >>
  simp[planSpillBoundsTheory.ops_spill_bounded_def, in_mem_range_def] >>
  rpt strip_tac >>
  `r.sr_spill_base <= b /\ b < r.sr_spill_end` by
    (first_x_assum (qspec_then `off` mp_tac) >> simp[] >> gvs[]) >>
  simp[contextCodegenRelTheory.context_spill_byte_def] >> metis_tac[]
QED

Theorem assign_postfix_alloc_frame:
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 ==>
  ps7.ps_alloc.sa_spill_base = qs.ps_alloc.sa_spill_base /\
  ps7.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset
Proof
  strip_tac >>
  `((if [x] = [] \/ halt then (pops,ps8) = ([],ps7)
      else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) [x])) ps7 = (pops,ps8)) /\
    (if [x] = [] \/ FILTER (\out. MEM out nl) [x] = [] then (opts,ps9) = ([],ps8)
      else optimistic_swap_plan dfg inst nl term ps8 = (opts,ps9)))` by
    (Cases_on `MEM x nl` >> Cases_on `halt` >> gvs[]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> simp[]
QED

Theorem sym_assign_plan_applicability:
  generated_plan_state_wf_marked sb ps /\
  (is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan ASSIGN [op] nl ps = (iops,prepared) /\
  reorder_plan dfg [op] prepared = (rops,arranged) /\
  1 <= LENGTH prepared.ps_stack /\
  ps7 = arranged with ps_stack := stack_push (Var x) (stack_pop 1 arranged.ps_stack) /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  stack_peek 0 arranged.ps_stack = op /\ 0 < LENGTH arranged.ps_stack /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\ context_spill_byte cplan b)
Proof
  strip_tac >>
  `residual_budget_wf_marked sb [] ps` by
    metis_tac[deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  `(!v. MEM v [op] /\ is_var_operand v ==>
      MEM v ps.ps_stack \/ v IN FDOM ps.ps_spilled) /\
    PERM [op] [op] /\ LENGTH [op] <= 16 /\
    LENGTH [op] <= LENGTH prepared.ps_stack` by simp[] >>
  drule_all deepResidualSimTheory.selected_input_arranged_marked >> strip_tac >>
  `plan_slots_bounded sb arranged /\
    spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled` by
    fs[deepResidualBudgetTheory.plan_state_residual_wf_marked_def] >>
  `stack_peek 0 arranged.ps_stack = op /\ 0 < LENGTH arranged.ps_stack` by
    (drule_all sym_assign_preparation_facts >> simp[]) >>
  `plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled` by
    (fs[planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
  drule_all assign_postfix_alloc_frame >> strip_tac >>
  `r.sr_spill_base <= sb /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    gvs[planSpillBoundsTheory.plan_slots_bounded_def,
      planSpillBoundsTheory.alloc_slots_bounded_def,
      fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  qpat_x_assum `plan_slots_bounded sb arranged` kall_tac >>
  drule_all assign_postfix_ops_bounded >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ops_spill_bounded _ _ _` mp_tac >>
  simp[planSpillBoundsTheory.ops_spill_bounded_def] >>
  disch_then (qspec_then `off` mp_tac) >>
  simp[] >> strip_tac >>
  `r.sr_spill_base <= b /\ b < r.sr_spill_end` by
    gvs[in_mem_range_def] >>
  simp[contextCodegenRelTheory.context_spill_byte_def] >> metis_tac[]
QED

(* PHI dispatch does not release spills after generate_phi_plan. *)
Theorem generated_phi_plan_result:
  inst.inst_opcode = PHI /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) ==>
  generate_phi_plan inst nl halt ps = (ops,qs)
Proof
  strip_tac >> gvs[generate_inst_plan_def, AllCaseEqs()]
QED

Theorem sym_generated_phi_plan_applicability:
  inst.inst_opcode = PHI /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  generated_plan_state_wf_marked sb ps /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  generate_phi_plan inst nl halt ps = (ops,qs) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b)
Proof
  strip_tac >> drule_all generated_phi_plan_result >> strip_tac >>
  `plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  drule_all allocMonoTheory.generate_inst_plan_spill_base >> strip_tac >>
  `r.sr_spill_base <= sb` by
    gvs[planSpillBoundsTheory.plan_slots_bounded_def,
      planSpillBoundsTheory.alloc_slots_bounded_def] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all generate_phi_plan_ops_region_confined >> simp[]
QED

Theorem regular_postfix_ops_spill_bounded:
  LENGTH inst.inst_outputs <= 1 /\
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.regular_postfix_ops_spill_bounded
QED

Theorem sym_regular_postfix_applicability:
  LENGTH inst.inst_outputs <= 1 /\ generated_plan_state_wf_marked sb ps7 /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ps7.ps_alloc.sa_spill_base = qs.ps_alloc.sa_spill_base /\
  ps7.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.sym_regular_postfix_applicability
QED

Theorem sym_regular_prefix_applicability:
  generated_plan_state_wf_marked sb ps /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  emitted = arranged with ps_stack := FOLDL (\stk out. stack_push (Var out) stk)
    (stack_pop (LENGTH selected) arranged.ps_stack) inst.inst_outputs /\
  (if inst.inst_outputs = [] \/ halt then ([],emitted)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted)
    = (pops,popped) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,tail) /\
  qs = release_dead_spills nl tail /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded sb ps /\ residual_budget_wf_marked sb [] ps /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.sym_regular_prefix_applicability
QED

Theorem sym_prepared_prefix_endpoint:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  cs.as_stack = top ++ rest /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n
    (cs with as_stack := top) = AsmOK mid /\
  sym_steps p env n ss = SymOK prepared ==>
  asm_sym_rel p env (mid with as_stack := mid.as_stack ++ rest) prepared
Proof
  strip_tac >>
  irule (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`,
      `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      symInstPrefixOwnTheory.sym_prepared_prefix_endpoint_mode_conditional)) >>
  simp[] >> metis_tac[asm_sym_steps_lockstep]
QED

Theorem sym_prepared_emit_localize:
  asm_sym_rel p env (cs with as_stack := cs.as_stack ++ rest) ss /\
  venom_asm_rel lo ps vs cs /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  ?top. ss.sym_stack = top ++ srest /\
    asm_sym_rel p env cs (ss with sym_stack := top) /\
    sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
    LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
      srest rest /\ LENGTH top = LENGTH cs.as_stack
Proof
  MATCH_ACCEPT_TAC (REWRITE_RULE [asmSymBridgeTheory.asm_sym_rel_core_canonical] (Q.INST
    [`lo` |-> `SND (compute_label_offsets p)`,
     `operand_lo` |-> `lo`, `code_ok` |-> `asm_data_env_ok p env`]
    symInstLocalizeCoreTheory.sym_prepared_emit_localize_maps_core))
QED

Theorem prepared_suffix_concrete_height[local]:
  venom_asm_rel lo ps vs cs /\ ps.ps_stack = residual ++ selected ==>
  LENGTH selected <= LENGTH cs.as_stack
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.prepared_suffix_concrete_height
QED

Theorem sym_named_inst_symbolic_run:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss name.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
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
    label_flow_ok ctx /\
    (!dst x sz w off. inst.inst_opcode = CODECOPY /\
      inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
      eval_operand (Var x) vs = SOME w /\
      FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
      w2n (w - n2w off) < dimword (:256) DIV 2) /\
    sym_data_label prog env "code_end" /\
    (MEM (Label "runtime_begin") inst.inst_operands ==>
     sym_data_label prog env "runtime_begin") /\ asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss /\
    venom_to_evm_name inst.inst_opcode = SOME name ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?ss'. sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK ss' /\
        sym_kinds_ok cp fn ret srest ps' ss' /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  gen_tac >> strip_tac >>
  drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)
    symInstNamedOwnTheory.sym_named_inst_symbolic_run_mode_core >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`F`, `ARB`, `asm_data_env_ok prog env`] mp_tac) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `MEM _ _.cp_regions`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `venom_to_evm_name _ = _`)) >>
  disch_then (qspecl_then [`o2pc`, `env`, `labs0`] mp_tac) >>
  simp[asmSymBridgeTheory.asm_sym_rel_core_canonical, sym_steps_mode_def] >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
      conj_tac
      >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
          `ssa_form fn` by fs[codegen_ready_fn_def] >>
          `~is_pre_codegen_opcode inst.inst_opcode` by
            metis_tac[generate_inst_plan_pre_codegen_none, optionTheory.NOT_SOME_NONE] >>
          qpat_assum `localps.ps_stack = _` (fn th => rewrite_tac[GSYM th]) >>
          drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`) sym_named_source_emit >>
          disch_then (drule_at (Pat `asm_step _ _ _ _ = _`)) >>
          disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
          disch_then (drule_at (Pat `venom_asm_rel _ _ (frame_view _ _ _ with vs_memory := _) _`)) >>
          disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
          disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
          disch_then (drule_at (Pat `_.ps_stack = _ ++ _`)) >>
          simp[]) >>
      gvs[] >> metis_tac[label_flow_ok_def]) >> simp[]
QED

(* Paired preparation keeps the exact-height concrete stack local. *)
Theorem sym_selected_prefix_paired:
  opc <> INVOKE /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded sb ps /\ residual_budget_wf_marked sb [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==> operand_val vs lo op = operand_val vs lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  lo = SND (compute_label_offsets p) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  cs.as_stack = top ++ rest /\
  venom_asm_rel lo ps vs (cs with as_stack := top) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?mid ready localtop.
    plan_state_residual_wf_marked sb selected (LENGTH selected) arranged /\
    arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
    asm_steps lo (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops)))
      (cs with as_stack := top) = AsmOK mid /\
    venom_asm_rel lo arranged vs mid /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    asm_sym_rel p env mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  irule (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`,
      `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      symInstPrefixOwnTheory.sym_selected_prefix_paired_mode_conditional)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  qexistsl [`nl`, `opc`, `operands`, `prepared`, `ps`, `r`] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sym_frame_suffix_compose:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  sym_steps p env n ss = SymOK mid /\ sym_steps p env m mid = SymOK final /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) ==>
  sym_steps p env (n + m) ss = SymOK final /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  simp[sym_frame_inv_def] >> strip_tac >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symInstPrefixPairOwnTheory.sym_frame_suffix_compose_mode_core)) >>
  simp[]
QED

Theorem sym_log_name_dispatch:
  n <= 4 ==>
  ALOOKUP log_table ("LOG" ++ num_to_dec_string n) = SOME n /\
  ~MEM ("LOG" ++ num_to_dec_string n) ["POP"; "JUMP"; "JUMPI"; "CODESIZE"] /\
  ALOOKUP dup_table ("LOG" ++ num_to_dec_string n) = NONE /\
  ALOOKUP swap_table ("LOG" ++ num_to_dec_string n) = NONE /\
  asm_op_arity ("LOG" ++ num_to_dec_string n) = n + 2
Proof
  MATCH_ACCEPT_TAC symInstLogOwnTheory.sym_log_name_dispatch
QED

Theorem sym_log_prepared_suffix:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  LENGTH selected = w2n tc + 2 /\ REVERSE selected = off :: len :: topics /\
  w2n tc <= 4 /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  venom_asm_rel lo qs vsout cs' /\
  ps.ps_stack = residual ++ selected /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  qs = ps with ps_stack := stack_pop (LENGTH selected) ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp ("LOG" ++ num_to_dec_string (w2n tc))) cs = AsmOK cs' /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    stail wtail ==>
  ?full. sym_steps p env 1 (ss with sym_stack := ss.sym_stack ++ stail) =
      SymOK full /\
    asm_sym_rel p env (cs' with as_stack := cs'.as_stack ++ wtail) full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail (release_dead_spills nl qs) full
Proof
  strip_tac >>
  irule (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `slo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      symInstLogOwnTheory.sym_log_prepared_suffix_mode_core)) >>
  conj_tac >- (rpt strip_tac >> drule_all sym_single_step_replay_safe >> simp[]) >>
  metis_tac[]
QED

(* Successful source execution supplies the raw, pre-release LOG endpoint. *)
Theorem sym_log_prepared_run:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  REVERSE selected = offop :: lenop :: topicops /\ w2n tc <= 4 /\
  step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := m) = OK vsout /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = stack_pop (LENGTH selected) ps.ps_stack ++ selected /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  EVERY (\(off,len). len = 0 \/ off + len <= qs.ps_alloc.sa_spill_base \/
    qs.ps_alloc.sa_next_offset <= off)
    (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := m)) /\
  qs = release_dead_spills nl
    (ps with ps_stack := stack_pop (LENGTH selected) ps.ps_stack) /\
  asm_block_at p cs.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] /\
  LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    stail wtail ==>
  ?full. sym_steps p env 1 (ss with sym_stack := ss.sym_stack ++ stail) =
      SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret stail qs full
Proof
  strip_tac >>
  irule (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `slo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      symInstLogOwnTheory.sym_log_prepared_run_mode_core)) >>
  conj_tac >- (rpt strip_tac >> drule_all sym_single_step_replay_safe >> simp[]) >>
  metis_tac[]
QED

Theorem reverse_two_operands[local]:
  2 <= LENGTH (xs:operand list) ==>
  ?a b tail. REVERSE xs = a :: b :: tail
Proof
  MATCH_ACCEPT_TAC symInstLogOwnTheory.reverse_two_operands
QED

Theorem successful_log_operand_shape[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?offop lenop topicops. REVERSE selected = offop :: lenop :: topicops
Proof
  MATCH_ACCEPT_TAC symInstLogOwnTheory.successful_log_operand_shape
QED

Theorem sym_log_inst_symbolic_run:
  lo = SND (compute_label_offsets prog) /\
  inst.inst_opcode = LOG /\ inst_wf inst /\
  inst.inst_operands = Lit tc :: selected /\ w2n tc <= 4 /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH selected <= 16 /\
  LENGTH selected <= LENGTH (SND (emit_input_plan LOG selected nl ps)).ps_stack /\
  (!op. MEM op selected /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) selected ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op selected ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op selected /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at selected) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) selected /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  irule (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      symInstLogOwnTheory.sym_log_inst_symbolic_run_mode_core)) >>
  conj_tac >- (rpt strip_tac >> drule_all sym_single_step_replay_safe >> simp[]) >>
  conj_tac >- (rpt strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  simp[] >> conj_tac >- (qexists `r` >> simp[]) >>
  qexistsl [`bb`, `cfg`, `cs`, `fuel`, `halt`, `inst`, `liveness`, `mem0`,
    `nl`, `ps`, `ra`, `rest`, `sb`, `selected`, `tc`, `term`, `vs`, `vsout`] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

(* Assertion success consumes one value; the caller suffix is untouched. *)
Theorem sym_assert_prepared_run:
  inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond] /\
  step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel p env cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] ==>
  ?full. sym_steps p env 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    localtop cs.as_stack` by gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  drule_at (Pat `step_inst _ _ _ _ = _`)
    (REWRITE_RULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
      symInstAssertOwnTheory.sym_assertion_prepared_run_mode_core)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ srest _ _`)) >>
  disch_then irule >> simp[]
QED

Theorem sym_assert_inst_symbolic_run:
  lo = SND (compute_label_offsets prog) /\
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      symInstAssertOwnTheory.sym_assert_inst_symbolic_run_mode_core)) >> simp[]
QED

(* Frame specialization of paired preparation; branch allocation facts remain explicit. *)
Theorem sym_frame_selected_prefix_paired:
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  inst.inst_opcode <> INVOKE /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
  MEM inst (fn_insts fn) /\ source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  step_inst fuel ctx inst vs = OK vsout /\
  generated_plan_state_wf_marked sb ps /\ fn_shape_ok fn /\
  lo = SND (compute_label_offsets p) /\ dfg = dfg_build_function fn /\
  emit_input_plan inst.inst_opcode operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?mid ready localtop m'.
    plan_state_residual_wf_marked sb selected (LENGTH selected) arranged /\
    arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := cs.as_memory) mid /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    asm_sym_rel p env mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH localtop = LENGTH mid.as_stack /\
    step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := cs.as_memory) =
      OK (frame_view fn ra vsout with vs_memory := m') /\
    EVERY (\(off,len). len = 0 \/ off + len <= final.ps_alloc.sa_spill_base \/
      final.ps_alloc.sa_next_offset <= off)
      (source_memory_read_ranges inst (frame_view fn ra vs with vs_memory := cs.as_memory))
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      symInstPrefixOwnTheory.sym_frame_selected_prefix_paired_mode_conditional)) >> simp[]
QED

(* Both assertion templates execute three steps on their successful path. *)
Theorem sym_assertion_prepared_run:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\
  step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel p env cs (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_stack = localtop ++ srest /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) ==>
  ?full. sym_steps p env 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    localtop cs.as_stack` by gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`]
    symInstAssertOwnTheory.sym_assertion_prepared_run_mode_core)) >> simp[]
QED

Theorem asm_unique_label_index:
  !p i lbl. asm_labels_unique p /\ i < LENGTH p /\ EL i p = AsmLabel lbl ==>
    INDEX_OF (AsmLabel lbl) p = SOME i
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.asm_unique_label_index
QED

Theorem asm_static_block_label_index:
  asm_static_wf p /\ asm_block_at p pc code /\
  i < LENGTH code /\ EL i code = AsmLabel lbl ==>
  INDEX_OF (AsmLabel lbl) p = SOME (pc + i)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.asm_static_block_label_index
QED

Theorem sym_assert_unreachable_frame_prepare[local]:
  lo = SND (compute_label_offsets prog) /\ inst.inst_opcode = ASSERT_UNREACHABLE /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
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
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss = SymOK ready /\
    sym_kinds_ok cplan fn ret srest arranged ready /\
    ready.sym_base.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ready.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    ready.sym_stack = localtop ++ srest /\
    asm_sym_rel prog env mid (ready with sym_stack := localtop) /\
    sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
    asm_block_at prog ready.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl]
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      symInstAssertPrepareOwnTheory.sym_assert_unreachable_frame_prepare_mode_core)) >> simp[]
QED

Theorem sym_assert_fresh_release_kinds[local]:
  sym_kinds_ok cplan fn ret srest
    (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) ss /\
  fresh_label prefix (ps with ps_stack := stack_pop 1 ps.ps_stack) = (lbl,qs) ==>
  sym_kinds_ok cplan fn ret srest (release_dead_spills nl qs) ss
Proof
  MATCH_ACCEPT_TAC symInstAssertOwnTheory.sym_assert_fresh_release_kinds
QED

Theorem sym_assert_unreachable_prepared_suffix[local]:
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst.inst_operands = [cond] /\
  step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel prog env mid (ready with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret [] arranged (ready with sym_stack := localtop) /\
  sym_kinds_ok cplan fn ret srest arranged ready /\ ready.sym_stack = localtop ++ srest /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
  EVERY (\op. op <> dead_stack_marker) [cond] /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  asm_static_wf prog /\ asm_block_at prog ready.sym_base.as_pc
    [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
  fresh_label "reachable" (arranged with ps_stack := stack_pop 1 arranged.ps_stack) = (lbl,p3) ==>
  ?full. sym_steps prog env 3 ready = SymOK full /\
    full.sym_mem_labels = ready.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest (release_dead_spills nl p3) full
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets prog)) sv = SOME w)
    localtop mid.as_stack` by gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`, `slo` |-> `SND (compute_label_offsets prog)`]
    symInstAssertSuffixOwnTheory.sym_assert_unreachable_prepared_suffix_mode_core)) >> simp[]
QED

Theorem sym_assert_unreachable_inst_symbolic_run:
  lo = SND (compute_label_offsets prog) /\
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [cond] <= LENGTH (SND (emit_input_plan ASSERT_UNREACHABLE [cond] nl ps)).ps_stack /\
  (!op. MEM op [cond] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) [cond] ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op [cond] ==> eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op [cond] /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at [cond]) /\
    operand_equiv dfg op at ==> operand_val (frame_view fn ra vs) lo op =
      operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) [cond] /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) /\
  asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops) - 1) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      symInstAssertOwnTheory.sym_assert_unreachable_inst_symbolic_run_mode_core)) >> simp[]
QED

Theorem sym_bump_postfix_applicability:
  inst.inst_outputs = [ptr;next] /\ ptr <> next /\
  ps7.ps_stack = residual ++ [Var ptr;Var next] /\
  generated_plan_state_wf_marked sb ps7 /\
  (if inst.inst_outputs = [] \/ halt then ([],ps7)
   else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
    = (pops,ps8) /\
  (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
   else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
  qs = release_dead_spills nl ps9 /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  ps7.ps_alloc.sa_spill_base = qs.ps_alloc.sa_spill_base /\
  ps7.ps_alloc.sa_next_offset <= qs.ps_alloc.sa_next_offset /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.sym_bump_postfix_applicability
QED

Theorem istore_plan_decompose:
  inst.inst_opcode = ISTORE /\ inst_wf inst /\
  inst.inst_operands = [dst; value] /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  inst.inst_outputs = [] /\ compute_operands inst = [dst; value] /\
  ?iops prepared rops arranged.
    emit_input_plan ISTORE [dst; value] nl ps = (iops,prepared) /\
    reorder_plan dfg [dst; value] prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "SWAP1"; SOEmit "MSTORE"] /\
    qs = release_dead_spills nl (arranged with ps_stack := stack_pop 2 arranged.ps_stack)
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.istore_plan_decompose
QED

Theorem sym_istore_prepared_run:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [dst; value] /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_sym_rel p env cs (ss with sym_stack := localtop) /\
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
  ?full. sym_steps p env 2 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 2 ps.ps_stack)) full
Proof
  strip_tac >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
    localtop cs.as_stack` by gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
    symInstStoreInitOwnTheory.sym_istore_prepared_run_mode_core)) >> simp[]
QED

Theorem sym_istore_inst_symbolic_run:
  lo = SND (compute_label_offsets prog) /\
  inst.inst_opcode = ISTORE /\ inst_wf inst /\ inst.inst_operands = [dst; value] /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked sb ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\
  LENGTH [dst; value] <= LENGTH (SND (emit_input_plan ISTORE [dst; value] nl ps)).ps_stack /\
  (!op. MEM op [dst; value] /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
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
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = OK vsout ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, sym_frame_inv_def] >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def, asmSymBridgeTheory.asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      symInstStoreInitOwnTheory.sym_istore_inst_symbolic_run_mode_core)) >> simp[]
QED

Theorem initial_fmp_plan_decompose:
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_operands = [] /\
  inst.inst_outputs = [x] /\
  generate_inst_plan liveness dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  ?pops ps8 opts ps9.
    (if halt then ([],ps with ps_stack := stack_push (Var x) ps.ps_stack)
     else popmany_plan (if MEM x nl then [] else [Var x])
       (ps with ps_stack := stack_push (Var x) ps.ps_stack)) = (pops,ps8) /\
    (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8)) = (opts,ps9) /\
    ops = [SOInitialFmp] ++ (pops ++ opts) /\ qs = release_dead_spills nl ps9
Proof
  MATCH_ACCEPT_TAC symInstPiecesFactsTheory.initial_fmp_plan_decompose
QED

Theorem sym_initial_fmp_generated_cleanup:
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
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts))) ==>
  ?final. sym_steps p env
      (LENGTH (execute_plan initial_fmp ([SOInitialFmp] ++ (pops ++ opts)))) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. ~R b ==> FLOOKUP final.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`, `B` |-> `asm_sym_rel p env`,
     `lo` |-> `SND (compute_label_offsets p)`]
      symInstStoreInitOwnTheory.sym_initial_fmp_generated_cleanup_mode_core)) >> simp[]
QED

Theorem sym_initial_fmp_inst_symbolic_run:
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
  asm_static_wf prog /\ asm_block_at prog cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps cs ss ==>
  ?final. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK final /\
    sym_kinds_ok cplan fn ret srest qs final /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP final.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  strip_tac >>
  `asm_sym_rel prog env cs ss /\ ss.sym_base.as_pc = cs.as_pc /\
   sym_kinds_ok cplan fn ret srest ps ss /\
   (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     FLOOKUP ss.sym_mem_labels b = FLOOKUP labs0 b)` by
    (fs[sym_frame_inv_def] >> metis_tac[asmSymBridgeTheory.asm_sym_rel_pc]) >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`, `B` |-> `asm_sym_rel prog env`,
     `lo` |-> `SND (compute_label_offsets prog)`]
      symInstStoreInitOwnTheory.sym_initial_fmp_inst_symbolic_run_mode_core)) >> simp[]
QED

(* Prepared BUMP is a local two-step emission; caller framing is separate. *)
Theorem sym_bump_prepared_local_emit:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  sym_kinds_ok cplan fn ret [] ps ss /\
  venom_asm_rel (SND (compute_label_offsets p)) ps vs cs /\
  ps.ps_stack = residual ++ [base_op; size_op] /\
  base_op <> dead_stack_marker /\ size_op <> dead_stack_marker /\
  operand_val vs (SND (compute_label_offsets p)) base_op = SOME base_val /\
  operand_val vs (SND (compute_label_offsets p)) size_op = SOME sz /\
  EVERY (\op. case op of Var x => x <> ptr /\ x <> next | _ => T) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    case op of Var x => x <> ptr /\ x <> next | _ => T) /\
  qs = ps with ps_stack := stack_push (Var next)
    (stack_push (Var ptr) (stack_pop 2 ps.ps_stack)) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    venom_asm_rel (SND (compute_label_offsets p)) qs
      (update_var next (base_val + sz) (update_var ptr base_val vs)) cs' /\
    cs'.as_pc = cs.as_pc + 2 /\
    sym_steps p env 2 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret [] qs ss' /\
    qs.ps_stack = residual ++ [Var ptr; Var next]
Proof
  strip_tac >>
  `!cs ss. asm_sym_rel p env cs ss ==> ss.sym_base.as_pc = cs.as_pc` by
    metis_tac[asmSymBridgeTheory.asm_sym_rel_pc] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`, `R` |-> `asm_sym_rel p env`,
     `lo` |-> `SND (compute_label_offsets p)`]
      symInstStoreInitOwnTheory.sym_bump_prepared_local_emit_mode_core)) >> simp[]
QED

(* Symbolic special instruction branches, with exact code-length counts. *)
Theory symInstPieces
Ancestors
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim symEmitSim fnFrameDeepInst

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
  strip_tac >> drule phi_depth_operand >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    metis_tac[stack_get_phi_depth_var_not_marker] >>
  `qs.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
    metis_tac[do_dup_stack_exact, pairTheory.SND] >>
  irule sym_kinds_ok_poke >> simp[stack_peek_def, listTheory.EL_APPEND_EQN] >>
  metis_tac[symInstKindsTheory.phi_var_output_kind]
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
  `execute_plan initial_fmp [SOPoke 0 (Var x)] = []` by
    simp[execute_plan_def, exec_stack_op_def] >>
  simp[stackOpSimTheory.execute_plan_append] >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_phi_depth_var_not_marker] >>
  drule_all sym_do_dup_sim_marked_ops_bounded >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> simp[] >> irule sym_phi_dup_rename >> metis_tac[]
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
  simp[execute_plan_def, exec_stack_op_def, sym_steps_def] >>
  metis_tac[sym_phi_rename]
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
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- (`popmany_plan [v] ps = ([],ps)` by
        (irule fnBlockPlanStaticFactsTheory.popmany_plan_absent >> simp[]) >>
      gvs[] >> qexists `ss` >> simp[execute_plan_def, sym_steps_def]) >>
  drule_all sym_popmany_plan_singleton_sim_marked_ops_bounded >>
  disch_then (qspec_then `env` strip_assume_tac) >> metis_tac[]
QED

Theorem execute_plan_poke_cons:
  execute_plan initial_fmp (SOPoke d op :: ops) = execute_plan initial_fmp ops
Proof
  simp[execute_plan_def, exec_stack_op_def]
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
  simp[execute_plan_poke_cons] >> strip_tac >>
  `sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack) ss` by
    metis_tac[sym_phi_rename] >>
  `spill_alloc_layout_wf
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack).ps_alloc
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack).ps_spilled` by simp[] >>
  drule_all sym_singleton_cleanup_sim >> simp[]
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
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_phi_depth_var_not_marker] >>
  `spill_alloc_layout_wf dup_ps.ps_alloc dup_ps.ps_spilled` by
    metis_tac[do_dup_layout_wf, pairTheory.SND] >>
  `spill_alloc_layout_wf
    (dup_ps with ps_stack := stack_poke 0 (Var x) dup_ps.ps_stack).ps_alloc
    (dup_ps with ps_stack := stack_poke 0 (Var x) dup_ps.ps_stack).ps_spilled` by simp[] >>
  `(!off. MEM (SOSpill off) dup_ops ==> off < dimword (:256)) /\
   (!off b. MEM (SOSpill off) dup_ops /\ in_mem_range off 32 b ==>
     R b /\ context_spill_byte cplan b) /\
   (!off. MEM (SOSpill off) pop_ops ==> off < dimword (:256)) /\
   (!off b. MEM (SOSpill off) pop_ops /\ in_mem_range off 32 b ==>
     R b /\ context_spill_byte cplan b)` by metis_tac[listTheory.MEM_APPEND] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append] >>
  rewrite_tac[stackOpSimTheory.asm_block_at_append] >> strip_tac >>
  drule_all sym_phi_live_prefix_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan initial_fmp pop_ops)` by metis_tac[] >>
  drule_all sym_singleton_cleanup_sim >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss''` >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  simp[Once sym_steps_add] >>
  simp[stackOpSimTheory.execute_plan_append] >> metis_tac[]
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
  qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def] >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (strip_tac >> gvs[] >> qexists `ss` >> simp[execute_plan_def, sym_steps_def]) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  Cases_on `MEM (operand_to_string (stack_peek d ps.ps_stack)) nl`
  >- suspend "live" >>
  suspend "dead"
QED

Resume sym_phi_plan_sim[dead]:
  simp[] >> Cases_on `~halt /\ ~MEM x nl` >> simp[]
  >- suspend "dead_pop" >>
  strip_tac >> gvs[] >> qexists `ss` >>
  simp[execute_plan_def, exec_stack_op_def, sym_steps_def] >>
  metis_tac[sym_phi_rename, listTheory.MEM]
QED

Resume sym_phi_plan_sim[dead_pop]:
  pairarg_tac >> strip_tac >> gvs[] >>
  `MEM x inst.inst_outputs` by simp[] >>
  drule_all sym_phi_dead_cleanup_sim >> simp[]
QED

Resume sym_phi_plan_sim[live]:
  Cases_on `do_dup d ps` >>
  rename1 `do_dup d ps = (dup_ops,dup_ps)` >> simp[] >>
  Cases_on `~halt /\ ~MEM x nl` >> simp[]
  >- suspend "live_pop" >>
  strip_tac >> gvs[] >>
  `MEM x inst.inst_outputs` by simp[] >>
  drule_all sym_phi_live_prefix_sim >> simp[]
QED

Resume sym_phi_plan_sim[live_pop]:
  pairarg_tac >> strip_tac >> gvs[] >>
  `MEM x inst.inst_outputs` by simp[] >>
  drule_all (SRULE [listTheory.APPEND_ASSOC, listTheory.MEM_APPEND,
    listTheory.MEM] sym_phi_live_cleanup_sim) >> simp[]
QED
Finalise sym_phi_plan_sim

Theorem stack_push_pop_one_poke:
  !stk out. 0 < LENGTH stk ==>
    stack_push out (stack_pop 1 stk) = stack_poke 0 out stk
Proof
  Induct >> simp[stack_push_def, stack_pop_def, stack_poke_def] >>
  Cases_on `stk` >>
  gvs[listTheory.LUPDATE_def, stack_push_def, stack_pop_def, stack_poke_def]
QED

Theorem sym_assign_output_state:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_outputs = [x] /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  label_positions_ok inst /\ stack_peek 0 ps.ps_stack = op /\
  0 < LENGTH ps.ps_stack /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_push (Var x) (stack_pop 1 ps.ps_stack)) ss
Proof
  strip_tac >> simp[stack_push_pop_one_poke] >>
  irule sym_assign_rename_top >> metis_tac[listTheory.MEM]
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
  strip_tac >>
  `sym_kinds_ok cplan fn ret srest ps7 ss` by
    metis_tac[sym_assign_output_state] >>
  `(!out. inst.inst_outputs = [out] ==>
      stack_get_depth (Var out) ps7.ps_stack = SOME 0) /\
    spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled` by
    simp[stack_get_depth_def, stack_push_def, listTheory.REVERSE_SNOC, stack_find_def] >>
  `(if inst.inst_outputs = [] \/ halt then ([],ps7)
     else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7)
     = (pops,ps8) /\
   (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9)` by
    (Cases_on `MEM x nl` >> gvs[]) >>
  `LENGTH inst.inst_outputs <= 1` by simp[] >>
  drule_all sym_regular_generated_postfix_sim_marked >> simp[]
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
  strip_tac >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append] >>
  rewrite_tac[stackOpSimTheory.asm_block_at_append] >> strip_tac >>
  `ASSIGN <> INVOKE /\ PERM [op] [op] /\ LENGTH [op] <= 16 /\
    LENGTH [op] <= LENGTH prepared.ps_stack /\
    (!v. MEM v [op] /\ is_var_operand v ==> MEM v ps.ps_stack \/ v IN FDOM ps.ps_spilled) /\
    EVERY (\v. v <> dead_stack_marker /\
      !at. operand_equiv dfg v at ==> at <> dead_stack_marker) [op]` by gvs[] >>
  drule_all sym_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan initial_fmp (pops ++ opts))` by
    metis_tac[] >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\b. r.sr_spill_base <= b /\ b < r.sr_spill_end`]
    sym_assign_postfix_sim)) >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss''` >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  simp[Once sym_steps_add] >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  simp[] >> metis_tac[]
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
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- (`popmany_plan [v] ps = ([],ps)` by
        (irule fnBlockPlanStaticFactsTheory.popmany_plan_absent >> simp[]) >>
      gvs[] >> simp[]) >>
  metis_tac[popmany_singleton_ops_spill_bounded]
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
  strip_tac >> drule optimistic_swap_result_cases >> strip_tac
  >- (gvs[] >> simp[]) >>
  metis_tac[planSpillBoundsTheory.do_swap_slots_bounded]
QED

Theorem assign_postfix_ops_bounded:
  plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled /\
  (if halt then ([],ps7) else popmany_plan (if MEM x nl then [] else [Var x]) ps7)
    = (pops,ps8) /\
  (if MEM x nl then optimistic_swap_plan dfg inst nl term ps8 else ([],ps8))
    = (opts,ps9) /\ qs = release_dead_spills nl ps9 ==>
  ops_spill_bounded sb qs.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  strip_tac >>
  Cases_on `MEM x nl`
  >- (gvs[popmany_plan_def] >> drule_all optimistic_swap_ops_bounded >>
      simp[allocMonoTheory.release_dead_spills_next_offset]) >>
  gvs[] >> Cases_on `halt` >> gvs[] >>
  drule_all singleton_cleanup_ops_bounded >>
  simp[allocMonoTheory.release_dead_spills_next_offset]
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
  strip_tac >> Cases_on `inst.inst_outputs`
  >- gvs[planSpillBoundsTheory.ops_spill_bounded_def] >>
  rename1 `inst.inst_outputs = x::xs` >> Cases_on `xs` >> gvs[] >>
  irule assign_postfix_ops_bounded >> qexistsl [`dfg`, `halt`, `inst`, `nl`, `ps7`, `ps8`, `ps9`, `term`, `x`] >>
  Cases_on `MEM x nl` >> gvs[]
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
  strip_tac >>
  `plan_slots_bounded sb ps7 /\ spill_alloc_layout_wf ps7.ps_alloc ps7.ps_spilled` by
    fs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  `((if inst.inst_outputs = [] \/ halt then (pops,ps8) = ([],ps7)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7 = (pops,ps8)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (opts,ps9) = ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8 = (opts,ps9)))` by
    (Cases_on `inst.inst_outputs = []` >>
     gvs[COND_EXPAND, AllCaseEqs()]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> strip_tac >>
  `r.sr_spill_base <= sb` by
    gvs[planSpillBoundsTheory.plan_slots_bounded_def,
      planSpillBoundsTheory.alloc_slots_bounded_def] >>
  drule_all regular_postfix_ops_spill_bounded >> strip_tac >>
  metis_tac[symPostfixSimTheory.scratch_ops_region_confined]
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
  strip_tac >>
  `residual_budget_wf_marked sb [] ps` by
    metis_tac[deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  drule_all deepResidualSimTheory.selected_input_arranged_marked >> strip_tac >>
  `((if inst.inst_outputs = [] \/ halt then (pops,popped) = ([],emitted)
    else popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) emitted = (pops,popped)) /\
    (if inst.inst_outputs = [] \/ FILTER (\out. MEM out nl) inst.inst_outputs = []
     then (opts,tail) = ([],popped)
     else optimistic_swap_plan dfg inst nl term popped = (opts,tail)))` by
    (Cases_on `inst.inst_outputs = []` >> gvs[COND_EXPAND, AllCaseEqs()]) >>
  drule_all generatedPrefixSimTheory.regular_postfix_alloc_frame >> strip_tac >>
  gvs[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
    deepResidualBudgetTheory.plan_state_residual_wf_marked_def,
    planSpillBoundsTheory.plan_slots_bounded_def,
    planSpillBoundsTheory.alloc_slots_bounded_def] >> gvs[]
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
  drule asmFrameTheory.asm_steps_frame >>
  disch_then (qspec_then `rest` assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  `cs with as_stack := top ++ rest = cs` by
    simp[asmSemTheory.asm_state_component_equality] >> gvs[]
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
  strip_tac >>
  `?top. ss.sym_stack = top ++ srest /\ LENGTH top = LENGTH cs.as_stack` by
    (gvs[sym_kinds_ok_def, codegenRelTheory.venom_asm_rel_def,
         codegenRelTheory.plan_stack_rel_def] >> metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_REVERSE]) >>
  drule asm_sym_rel_localize_stack >>
  disch_then (qspecl_then [`rest`, `cs.as_stack`, `top`, `srest`] mp_tac) >>
  simp[] >> strip_tac >>
  irule sym_kinds_ok_localize_stack >> simp[]
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
    (!op w. inst.inst_opcode = ADD /\
            inst.inst_operands = [op; Label "code_end"] /\
            eval_operand op vs = SOME w ==> w2n w < dimword (:256) DIV 2) /\
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
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
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
  strip_tac >>
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
  simp[] >> strip_tac >>
  `ssa_form fn` by
    (qpat_x_assum `codegen_ready_fn fn` mp_tac >>
     simp[stackPlanGenTheory.codegen_ready_fn_def]) >>
  `asm_sym_rel prog env as ss /\ sym_kinds_ok cplan fn ret srest ps ss` by
    metis_tac[sym_frame_inv_def] >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (qpat_x_assum `EVERY _ ops` mp_tac >>
     simp[listTheory.EVERY_APPEND]) >>
  `ss.sym_base.as_pc = as.as_pc` by
    (qpat_x_assum `asm_sym_rel prog env as ss` mp_tac >>
     simp[asmSymBridgeTheory.asm_sym_rel_def] >> rpt strip_tac >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (qpat_x_assum `asm_block_at prog as.as_pc _` mp_tac >>
     simp[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append]) >>
  drule_at (Pat `emit_input_plan _ _ _ _ = _`) sym_selected_prefix_sim_marked >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`sb`, `r`, `env`] mp_tac) >>
  simp[] >>
  (impl_tac >-
    (qpat_x_assum `EVERY _ (compute_operands inst)` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[])) >>
  strip_tac >>
  drule_at (Pat `sym_steps _ _ _ _ = _`) sym_prepared_prefix_endpoint >>
  disch_then (drule_at (Pat `asm_steps _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  drule_all sym_prepared_emit_localize >> strip_tac >>
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
  qpat_assum `step_inst fuel ctx inst vs = OK vs'`
    (mp_then (Pat `step_inst _ _ _ _ = _`) mp_tac sym_named_source_emit) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_steps _ _ _ 1 _ = _`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `venom_asm_rel _ _ _ _`)) >>
  disch_then (drule_at (Pat `emitted = _`)) >>
  disch_then (qspecl_then [`stack_pop (LENGTH selected) arranged.ps_stack`, `name`] mp_tac) >>
  cheat

QED

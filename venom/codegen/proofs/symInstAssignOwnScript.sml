(* ASSIGN preparation in either symbolic execution mode. *)
Theory symInstAssignOwn
Ancestors
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim

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

Theorem sym_assign_postfix_sim_mode:
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
  ?ss'. sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (pops ++ opts))) ss = SymOK ss' /\
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
  drule_all sym_regular_generated_postfix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  qexists `ss'` >> simp[] >> irule sym_steps_mode_ok >> simp[]
QED

Theorem sym_assign_plan_sim_mode:
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
  ?ss'. sym_steps_mode allow_own p env own
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
  `sym_steps_mode allow_own p env own
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss = SymOK ss'` by
    (irule sym_steps_mode_ok >> simp[]) >>
  `asm_block_at p ss'.sym_base.as_pc (execute_plan initial_fmp (pops ++ opts))` by
    metis_tac[] >>
  drule_all (BETA_RULE (Q.INST
    [`R` |-> `\b. r.sr_spill_base <= b /\ b < r.sr_spill_end`]
    sym_assign_postfix_sim_mode)) >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] strip_assume_tac) >>
  qexists `ss''` >>
  pure_rewrite_tac[Once stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  simp[Once sym_steps_mode_add] >>
  pure_rewrite_tac[stackOpSimTheory.execute_plan_append, listTheory.LENGTH_APPEND] >>
  simp[] >> metis_tac[]
QED

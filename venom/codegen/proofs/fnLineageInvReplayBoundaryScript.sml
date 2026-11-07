Theory fnLineageInvReplayBoundary
Ancestors
  fnLineageInvActualReplay fnPlanLineageInventory reorderSim stackPlanGen
  stackPlanTypes list rich_list pred_set

Theorem available_inst_bottom_frame:
 !spill_base lv dfg cfg fn inst nl halt term lbl ps ops qs n core m.
 lineage_core n core ps /\
 residual_budget_wf spill_base [] (ps with ps_stack := core) /\
 inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI /\
 inst.inst_opcode <> OFFSET /\ inst.inst_opcode <> NOP /\
 ~is_param_opcode inst.inst_opcode /\
 LENGTH (compute_operands inst) <= 16 /\
 EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
 (!v. MEM (Var v) (compute_operands inst) ==>
   MEM (Var v) core \/ Var v IN FDOM ps.ps_spilled) /\
 ALL_DISTINCT inst.inst_outputs /\
 EVERY (\v. ~MEM (Var v) (compute_operands inst) /\
   ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs /\
 generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs)
 ==>
 generate_inst_plan lv dfg cfg fn inst nl halt term lbl
   (ps with ps_stack := REPLICATE m dead_stack_marker ++ ps.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE m dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >> strip_tac >>
 `ps.ps_stack = REPLICATE n dead_stack_marker ++ core` by
   gvs[lineage_core_def] >>
 qabbrev_tac `canon = ps with ps_stack := core` >>
 Cases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl canon` >>
 rename1 `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ canon = (cops,cqs)` >>
 `!r. generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl
   (canon with ps_stack := REPLICATE r dead_stack_marker ++ canon.ps_stack) =
   (cops,cqs with ps_stack := REPLICATE r dead_stack_marker ++ cqs.ps_stack)` by
   (gen_tac >> irule generate_regular_plan_bottom_frame >>
    simp[Abbr `canon`] >> metis_tac[]) >>
 `canon with ps_stack := REPLICATE n dead_stack_marker ++ canon.ps_stack = ps` by
   (simp[Abbr `canon`, plan_state_component_equality]) >>
 first_assum (qspec_then `n` assume_tac) >>
 first_assum (qspec_then `m+n` assume_tac) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 gvs[Abbr `canon`, GSYM REPLICATE_APPEND, APPEND_ASSOC]
QED

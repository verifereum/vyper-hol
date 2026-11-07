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

(* Count spill resources only when the remaining input/live footprint can
   restore them.  Unrequested surplus spills must not bound stack slots. *)
Theorem emit_one_input_stack_upper_acc[local]:
  !done rest opc nl h ps.
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled /\
          MEM x (MAP Var (operand_vars (h::rest) ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars (h::rest) ++ nl)) then 1 else 0)) ==>
    !x. LIST_ELEM_COUNT x (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc (operand_vars rest ++ nl) h ps)).ps_spilled /\
          MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ [h]) +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `x` assume_tac) >>
  qspecl_then [`opc`, `operand_vars rest ++ nl`, `h`, `ps`, `x`]
    assume_tac emit_one_input_inventory_upper >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  drule genBlockSimTheory.bump_emit_one_input_spilled_shape >> strip_tac >>
  Cases_on `x IN FDOM ps.ps_spilled` >>
  Cases_on `h` >> Cases_on `x` >>
  gvs[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def,
      venomInstTheory.operand_var_def, dfgDefsTheory.operand_var_def,
      is_var_operand_def, elem_count_append, MAP_APPEND,
      LIST_ELEM_COUNT_DEF, MEM_MAP, finite_mapTheory.FDOM_DOMSUB] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (qpat_x_assum `emit_one_input _ _ (Lit _) _ = _` mp_tac >>
       simp[emit_one_input_def, is_var_operand_def] >> strip_tac >>
       gvs[stackModelTheory.stack_push_def, SNOC_APPEND, FILTER_APPEND, elem_count_append, LIST_ELEM_COUNT_DEF] >>
       NO_TAC) >>
  TRY (qpat_x_assum `emit_one_input _ _ (Label _) _ = _` mp_tac >>
       simp[emit_one_input_def, is_var_operand_def] >>
       Cases_on `opc = INVOKE` >> strip_tac >>
       gvs[stackModelTheory.stack_push_def, SNOC_APPEND, FILTER_APPEND, elem_count_append, LIST_ELEM_COUNT_DEF] >>
       NO_TAC) >>
  decide_tac
QED

Theorem emit_input_plan_stack_upper_acc[local]:
  !rest done opc nl ps iops qs.
    (!x. LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled /\
          MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0) <=
      LIST_ELEM_COUNT x done +
      (if MEM x (MAP Var (operand_vars rest ++ nl)) then 1 else 0)) /\
    emit_input_plan opc rest nl ps = (iops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack +
      (if x IN FDOM qs.ps_spilled /\ MEM x (MAP Var nl) then 1 else 0) <=
      LIST_ELEM_COUNT x (done ++ rest) + (if MEM x (MAP Var nl) then 1 else 0)
Proof
  Induct_on `rest`
  >- simp[venomInstTheory.operand_vars_def, dfgDefsTheory.operand_vars_def] >>
  rpt gen_tac >> strip_tac >>
  drule emit_one_input_stack_upper_acc >>
  disch_then (qspec_then `opc` assume_tac) >>
  Cases_on `emit_one_input opc (operand_vars rest ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc rest nl mid` >>
  gvs[emit_input_plan_cons] >>
  first_x_assum drule >> disch_then drule >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem emit_input_plan_stack_live_upper:
  !opc operands nl ps iops qs.
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    set ps.ps_stack SUBSET set (MAP Var (operand_vars operands ++ nl)) /\
    emit_input_plan opc operands nl ps = (iops,qs) ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack <=
      LIST_ELEM_COUNT x operands + (if MEM x (MAP Var nl) then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. LIST_ELEM_COUNT x ps.ps_stack +
    (if x IN FDOM ps.ps_spilled /\
        MEM x (MAP Var (operand_vars operands ++ nl)) then 1 else 0) <=
    LIST_ELEM_COUNT x [] +
    (if MEM x (MAP Var (operand_vars operands ++ nl)) then 1 else 0)` by
    (gen_tac >>
     drule all_distinct_elem_count_le_one >>
     disch_then (qspec_then `x` assume_tac) >>
     Cases_on `x IN FDOM ps.ps_spilled`
     >- (`~MEM x ps.ps_stack` by (gvs[DISJOINT_ALT] >> metis_tac[]) >>
         gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
     Cases_on `MEM x (MAP Var (operand_vars operands ++ nl))` >- simp[] >>
     `~MEM x ps.ps_stack` by (gvs[SUBSET_DEF] >> metis_tac[]) >>
     gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM]) >>
  drule_all emit_input_plan_stack_upper_acc >> simp[] >> strip_tac >>
  gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
  Cases_on `x IN FDOM qs.ps_spilled /\ MEM x (MAP Var nl)` >> simp[]
QED

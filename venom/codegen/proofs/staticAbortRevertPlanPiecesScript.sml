Theory staticAbortRevertPlanPieces
Ancestors
  fnFrameTerminalHalt fnPlanPrefix fnBlockPlanStaticBalance staticAbortPlanBoundary planWf stackPlanGen
  stackPlanOps stackModel prefixExec venomInst venomEffects asmIR list arithmetic

Theorem output_free_plan_heights:
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs) /\
  inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) ==>
  ?pre m d. ops = pre ++ [SOEmit name] /\
    prefix_wf lo (LENGTH ps.ps_stack) pre /\
    prefix_end_len lo (LENGTH ps.ps_stack) pre = m /\
    LENGTH (compute_operands inst) <= m /\
    d + LENGTH (compute_operands inst) = m /\ LENGTH qs.ps_stack = d
Proof
  strip_tac >> drule_all output_free_regular_plan >> strip_tac >>
  `prefix_wf lo (LENGTH ps.ps_stack) iops /\
   prefix_end_len lo (LENGTH ps.ps_stack) iops = LENGTH prepared.ps_stack` by
    (qspecl_then [`inst`, `nl`, `ps`, `lo`] mp_tac regular_input_plan_wf_len >> simp[]) >>
  `prefix_wf lo (LENGTH prepared.ps_stack) rops /\
   prefix_end_len lo (LENGTH prepared.ps_stack) rops = LENGTH arranged.ps_stack /\
   LENGTH (compute_operands inst) <= LENGTH arranged.ps_stack` by
    (qspecl_then [`dfg`, `compute_operands inst`, `prepared`, `lo`]
      mp_tac reorder_plan_wf_len >> gvs[] >>
     metis_tac[reorder_plan_length_floor]) >>
  qexistsl_tac [`iops ++ rops`, `LENGTH arranged.ps_stack`, `LENGTH qs.ps_stack`] >>
  simp[APPEND_ASSOC] >>
  `prefix_wf lo (LENGTH ps.ps_stack) (iops ++ rops) /\
   prefix_end_len lo (LENGTH ps.ps_stack) (iops ++ rops) = LENGTH arranged.ps_stack` by
    metis_tac[prefix_wf_len_append] >>
  simp[release_dead_spills_stack, stack_pop_def]
QED

Theorem revert_forward_plan_pieces:
  (k:num) < j /\ k <= q /\ q <= j /\
  inst.inst_opcode = (if q=k then RETURNDATACOPY else if q=j then REVERT else ASSIGN) /\
  (q=k ==> inst.inst_outputs=[] /\ LENGTH inst.inst_operands=3) /\
  (q=j ==> inst.inst_outputs=[] /\ LENGTH inst.inst_operands=2) /\
  (k<q /\ q<j ==> ?rhs out. inst.inst_operands=[rhs] /\ inst.inst_outputs=[out]) /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps = (ops,qs) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) ==>
  ?pre emit post m d.
    ops = pre ++ emit ++ post /\
    prefix_wf lo (LENGTH ps.ps_stack) pre /\
    prefix_end_len lo (LENGTH ps.ps_stack) pre=m /\
    prefix_wf lo d post /\ prefix_end_len lo d post=LENGTH qs.ps_stack /\
    (q=k ==> emit=[SOEmit "RETURNDATACOPY"] /\ post=[] /\
      3<=m /\ d+3=m /\ 3<=m+extra /\ d+extra+3=m+extra) /\
    (k<q /\ q<j ==> emit=[] /\ 1<=m /\ d=m /\ d+extra=m+extra) /\
    (q=j ==> emit=[SOEmit "REVERT"] /\ post=[] /\
      2<=m /\ d+2=m /\ 2<=m+extra /\ d+extra+2=m+extra)
Proof
  strip_tac >> Cases_on `q=k`
  >- (gvs[] >>
      drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        output_free_plan_heights >>
      simp[venom_to_evm_name_def, is_commutative_def] >>
      disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `pre` >>
      gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
          prefix_wf_def, prefix_end_len_def] >> decide_tac) >>
  Cases_on `q=j`
  >- (gvs[] >>
      drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        output_free_plan_heights >>
      simp[venom_to_evm_name_def, is_commutative_def] >>
      disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `pre` >>
      gvs[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def,
          prefix_wf_def, prefix_end_len_def] >> decide_tac) >>
  `k<q /\ q<j` by decide_tac >> gvs[] >>
  drule regular_plan_admin_decomposition >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  qexistsl_tac [`pre`, `post`] >>
  gvs[generate_emit_ops_def, venom_to_evm_name_def, compute_operands_def,
      python_stack_operands_def, ir_specific_operand_order_def]
QED

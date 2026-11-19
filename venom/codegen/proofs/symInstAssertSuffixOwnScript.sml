(* Lower assertion suffix boundaries. Operand and concretization maps are independent. *)
Theory symInstAssertSuffixOwn
Ancestors symInstPiecesFacts symEmitOwn symEmitSim
  symPostfixSim symPlannerSim stackPlanGen stackPlanOps stackModel asmSplice
  planExec codegenSymRel asmSymSem doSwapSim genBlockSim fnFrameDeepInst

Theorem sym_assertion_prepared_run_mode_core:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) localtop cs.as_stack /\
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
  ?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) full
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `?w tail. localtop = Val w :: tail /\ w <> 0w` by
    (drule_all (SRULE [] (Q.INST
       [`ss` |-> `ss with sym_stack := localtop`, `srest` |-> `[]`]
       sym_assert_prepared_nonzero_core)) >> simp[]) >>
  `ss.sym_stack = Val w :: (tail ++ srest)` by simp[] >>
  `?full. sym_steps_mode allow_own p env own 3 ss = SymOK full /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    full.sym_stack = DROP 1 ss.sym_stack` by
    (Cases_on `inst.inst_opcode = ASSERT` >> gvs[]
     >- (drule_all sym_assert_success_run_mode >> simp[] >> metis_tac[]) >>
     drule_all sym_assert_unreachable_success_run_mode >> simp[] >> metis_tac[]) >>
  `1 <= LENGTH ps.ps_stack` by simp[] >>
  qexists `full` >> simp[] >> irule sym_kinds_ok_release_dead_spills >>
  irule sym_emit_kinds_pop >> qexistsl [`1`, `ps`, `ss`] >> simp[]
QED

Theorem sym_assert_fresh_release_kinds:
  sym_kinds_ok cplan fn ret srest
    (release_dead_spills nl (ps with ps_stack := stack_pop 1 ps.ps_stack)) ss /\
  fresh_label prefix (ps with ps_stack := stack_pop 1 ps.ps_stack) = (lbl,qs) ==>
  sym_kinds_ok cplan fn ret srest (release_dead_spills nl qs) ss
Proof
  strip_tac >> gvs[stackPlanTypesTheory.fresh_label_def] >>
  irule sym_kinds_ok_inventory_mono >> goal_assum (drule_at Any) >>
  mp_tac (Q.SPECL
    [`ps with <|ps_stack := stack_pop 1 ps.ps_stack;
       ps_label_counter := ps.ps_label_counter + 1|>`,
     `ps with ps_stack := stack_pop 1 ps.ps_stack`, `nl`]
    (GEN_ALL release_dead_spills_inventory_cong)) >> simp[]
QED

Theorem sym_assert_unreachable_prepared_suffix_mode_core:
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst.inst_operands = [cond] /\
  step_inst fuel ctx inst vs = OK vsout /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) localtop mid.as_stack /\
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
  ?full. sym_steps_mode allow_own prog env own 3 ready = SymOK full /\
    full.sym_mem_labels = ready.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest (release_dead_spills nl p3) full
Proof
  strip_tac >>
  `INDEX_OF (AsmLabel lbl) prog = SOME (ready.sym_base.as_pc + 3)` by
    (drule_at (Pat `asm_block_at _ _ _`) asm_static_block_label_index >>
     disch_then (qspecl_then [`lbl`, `3`] mp_tac) >> simp[]) >>
  `?full. sym_steps_mode allow_own prog env own 3 ready = SymOK full /\
    full.sym_mem_labels = ready.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest
      (release_dead_spills nl (arranged with ps_stack := stack_pop 1 arranged.ps_stack)) full` by
    (drule_at (Pat `venom_asm_rel _ arranged _ mid`) sym_assertion_prepared_run_mode_core >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ [] _ _`)) >>
     disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ ready`)) >>
     disch_then (drule_at (Pat `step_inst _ _ _ vs = _`)) >>
     disch_then irule >> simp[] >>
     gvs[venomMemPropsTheory.eval_operand_with_memory,
       genFrameSimTheory.operand_val_memory_update] >> metis_tac[]) >>
  drule_all sym_assert_fresh_release_kinds >> strip_tac >>
  qexists `full` >> simp[]
QED

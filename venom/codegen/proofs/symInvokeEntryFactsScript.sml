(* Shared INVOKE argument facts and successful numeric entry seeds. *)
Theory symInvokeEntryFacts
Ancestors
  symPostfixSim symFnSimSpec codegenSymRel codegenSymOwnRel fnFrameDeepInvoke
  asmSymBridge asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst dfgDefs list symPlannerSim prefixExec mixedPrefixSim symShuffleSim
  gasFrameSim fnFrameStepsRevertForward

Theorem sym_invoke_argument_not_code_end_own:
  label_flow_own_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  rw[label_flow_own_ok_def] >>
  first_x_assum drule_all >> simp[] >> metis_tac[]
QED

Theorem sym_invoke_argument_shape_core:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args ==>
  opaque_use_ok fn /\ EVERY (\op. ~is_label_operand op) args
Proof
  strip_tac >>
  `opaque_use_ok fn /\ label_positions_ok inst` by
    (gvs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  gvs[label_positions_ok_def]
QED

Theorem sym_invoke_argument_word_kind_own:
  fn_shape_ok fn /\ label_flow_own_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\ MEM op args /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >>
  drule_all sym_invoke_argument_shape_core >> strip_tac >>
  `~is_label_operand op` by gvs[EVERY_MEM] >>
  Cases_on `op` >> gvs[is_label_operand_def, op_kind_ok_def] >>
  metis_tac[fnFrameBoundaryInvokeTheory.invoke_arguments_not_retpc,
            sym_invoke_argument_not_code_end_own, MEM]
QED

Theorem sym_invoke_argument_list_words_own:
  fn_shape_ok fn /\ label_flow_own_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  LIST_REL (op_kind_ok fn ret) (REVERSE args) svs ==>
  EVERY (\sv. ?w. sv = Val w) svs
Proof
  rw[EVERY_MEM] >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  gvs[MEM_REVERSE] >>
  `x <> dead_stack_marker` by metis_tac[] >>
  drule_all sym_invoke_argument_word_kind_own >> simp[]
QED

Theorem sval_conc_words_core:
  !svs ws lo.
  EVERY (\sv. ?w. sv = Val w) svs /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) svs ws ==>
  svs = MAP Val ws
Proof
  Induct >> Cases_on `ws` >> simp[] >>
  rpt strip_tac >> gvs[sval_conc_def] >> metis_tac[]
QED

Theorem sym_invoke_arranged_stack_core:
  !lo ctx cp fn ret srest ps cs ss inst nm args saved_ops values saved rest.
  fn_shape_ok fn /\ label_flow_own_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_kinds_ok cp fn ret srest ps ss /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) ss.sym_stack cs.as_stack /\
  ps.ps_stack = saved_ops ++ args /\
  cs.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args ==>
  ?saved_sym.
    ss.sym_stack = MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym
Proof
  rpt strip_tac >>
  gvs[sym_kinds_ok_def, REVERSE_APPEND, LIST_REL_SPLIT1] >>
  rename1 `LIST_REL (op_kind_ok fn ret) (REVERSE args) arg_syms` >>
  `EVERY (\sv. ?w. sv = Val w) arg_syms` by
    (drule_all sym_invoke_argument_list_words_own >> simp[]) >>
  `LENGTH arg_syms = LENGTH values` by
    metis_tac[LIST_REL_LENGTH, LENGTH_REVERSE] >>
  `LIST_REL (\sv w. sval_conc lo sv = SOME w) arg_syms values` by
    (qpat_x_assum `LIST_REL (\sv w. sval_conc lo sv = SOME w) arg_syms _` mp_tac >>
     qmatch_goalsub_rename_tac `LIST_REL (\sv w. sval_conc lo sv = SOME w) arg_syms arg_words` >>
     strip_tac >>
     `LENGTH values = LENGTH arg_words` by metis_tac[LIST_REL_LENGTH] >>
     `values = arg_words` by
       (qpat_x_assum `_ ++ _ = _ ++ _` mp_tac >>
        pure_rewrite_tac[GSYM APPEND_ASSOC] >>
        strip_tac >> metis_tac[rich_listTheory.APPEND_EQ_APPEND_EQ]) >> gvs[]) >>
  drule_all sval_conc_words_core >> strip_tac >> gvs[]
QED

Theorem sym_invoke_arranged_stack_own:
  !lo p env own ctx cp fn ret srest ps cs ss inst nm args saved_ops values saved rest.
  fn_shape_ok fn /\ label_flow_own_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_kinds_ok cp fn ret srest ps ss /\ asm_sym_rel_own lo p env own cs ss /\
  ps.ps_stack = saved_ops ++ args /\
  cs.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args ==>
  ?saved_sym.
    ss.sym_stack = MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym
Proof
  rpt strip_tac >> irule sym_invoke_arranged_stack_core >>
  gvs[asm_sym_rel_own_def] >> metis_tac[]
QED

Theorem sym_invoke_selected_prefix_sim_marked_core:
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss =
          SymOK ss' /\
        sym_kinds_ok cplan fn ret srest arranged ss' /\
        ss'.sym_base.as_pc =
          ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
        (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `emit_input_plan ADD operands nl ps = (iops,prepared)` by
    metis_tac[fnFrameBoundaryInvokeTheory.invoke_label_free_input] >>
  `ADD <> INVOKE /\ PERM operands operands` by simp[] >>
  drule_all sym_selected_prefix_sim_marked >> simp[]
QED

Theorem sym_invoke_call_packet_core:
  !p env ss ret_lbl nm pc.
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  INDEX_OF (AsmLabel nm) p = SOME pc ==>
  sym_steps p env 3 ss =
    SymOK (ss with <| sym_base := ss.sym_base with as_pc := pc;
                     sym_stack := Lab ret_lbl 0 :: ss.sym_stack |> )
Proof
  rpt strip_tac >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[asmSpliceTheory.sym_steps_compute, sym_step_def, sym_set_stack_def,
       sym_step_op_def, sym_jump_def, sym_jump_dest_def, asm_next_def]
QED

Theorem sym_invoke_return_code_label_core:
  !p pc fmp ret nm post.
  asm_block_at p pc (execute_plan fmp
    ([SOPushLabel ret; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret] ++ post)) ==>
  MEM (AsmLabel ret) p
Proof
  rpt strip_tac >> irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >> simp[execute_plan_def, exec_stack_op_def]
QED

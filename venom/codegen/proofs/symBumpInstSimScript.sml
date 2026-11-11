Theory symBumpInstSim
Ancestors
  symInstPieces symPostfixSim symEmitSim deepInstSim deepResidualSim
  genBlockSim stackPlanGen planExec codegenSymRel asmSymBridge asmSymSem
  fnPlanPrefix genFrameSim allocMono venomWf fnBlockPlanStaticRegion

Theorem bump_plan_decompose:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\
  generate_inst_plan lv dfg cfg fn inst nl halt term bb ps = SOME (ops,qs) ==>
  ?iops prepared rops arranged pops ps8 opts ps9.
    emit_input_plan BUMP [base_op; size_op] nl ps = (iops,prepared) /\
    reorder_plan dfg [base_op; size_op] prepared = (rops,arranged) /\
    popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) [ptr;next]))
       (arranged with ps_stack := stack_push (Var next)
         (stack_push (Var ptr) (stack_pop 2 arranged.ps_stack))) = (pops,ps8) /\
    (if FILTER (\out. MEM out nl) [ptr;next] = [] then ([],ps8)
     else optimistic_swap_plan dfg inst nl term ps8) = (opts,ps9) /\
    ops = iops ++ rops ++ bump_emit_ops ++ pops ++ opts /\
    qs = release_dead_spills nl ps9
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, venomInstTheory.is_param_opcode_def,
    generate_regular_inst_plan_def, compute_operands_def,
    venomInstTheory.python_stack_operands_def, venomInstTheory.ir_specific_operand_order_def,
    venomEffectsTheory.is_commutative_def, generate_emit_ops_def] >>
  simp[is_pre_codegen_opcode_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sym_bump_prepared_full_emit:
  inst.inst_opcode = BUMP /\ inst.inst_operands = [base_op; size_op] /\
  inst.inst_outputs = [ptr; next] /\ ptr <> next /\
  ssa_form fn /\ opaque_use_ok fn /\ label_flow_ok ctx /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  asm_static_wf p /\ asm_sym_rel p env cs (ss with sym_stack := top) /\
  sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
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
  ss.sym_stack = top ++ srest /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "DUP2"; AsmOp "ADD"] ==>
  ?full. sym_steps p env 2 ss = SymOK full /\
    full.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    full.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs full /\
    qs.ps_stack = residual ++ [Var ptr;Var next]
Proof
  strip_tac >>
  `asm_block_at p (ss with sym_stack := top).sym_base.as_pc
    [AsmOp "DUP2"; AsmOp "ADD"]` by simp[] >>
  drule_all sym_bump_prepared_local_emit >> strip_tac >>
  rename1 `sym_steps p env 2 (ss with sym_stack := top) = SymOK localend` >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnBlockBodyHelpersTheory.label_positions_ok_other >> simp[] >>
     metis_tac[unitShapeDefsTheory.fn_shape_ok_def, listTheory.EVERY_MEM,
       unitShapeDefsTheory.inst_shape_ok_def]) >>
  `?delta fmp tail. top = Val delta :: Val fmp :: tail` by
    (qpat_assum `sym_kinds_ok _ _ _ [] ps _`
       (mp_then (Pat `sym_kinds_ok _ _ _ _ _ _`) mp_tac ordinary_prepared_selected_numeric) >>
     disch_then (drule_at (Pat `ps.ps_stack = _`)) >>
     disch_then (qspecl_then [`inst`, `ctx`] mp_tac) >>
     (impl_tac >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])) >> simp[] >>
     metis_tac[numeric_prefix_two]) >>
  qpat_assum `sym_steps p env 2 (ss with sym_stack := top) = _`
    (mp_then (Pat `sym_steps _ _ _ _ = _`) mp_tac sym_bump_steps_ok_stack_suffix) >>
  simp[] >> disch_then (qspec_then `srest` mp_tac) >> simp[] >> strip_tac >>
  qexists `localend with sym_stack := localend.sym_stack ++ srest` >>
  `ss with sym_stack := top ++ srest = ss` by
    (simp[asmSymSemTheory.sym_state_component_equality]) >>
  gvs[] >> conj_tac >- gvs[asmSymBridgeTheory.asm_sym_rel_def] >>
  irule sym_kinds_ok_restore_stack >> simp[]
QED

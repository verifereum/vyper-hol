(* Source label flow shared by runtime and deploy lowering. *)
Theory sourceLabelFlow
Ancestors
  runtimeLabelInvariant codegenSymOwnRel o1LabelFlowSourceBoundary
  unitShapeDefs stackPlanTypes venomInst list

Theorem source_own_flow:
  o1_source_unit_ok unit /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst) ==>
  label_flow_own_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands)
Proof
  strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "code_end") inst.inst_operands` by
    (rpt strip_tac >> res_tac >>
     gvs[source_inst_ok_def, EVERY_MEM] >>
     qpat_x_assum `!e. MEM e inst.inst_operands ==> _`
       (qspec_then `Label "code_end"` mp_tac) >>
     simp[rb_operand_ok_for_def]) >>
  `!f x. MEM f unit.cu_context.ctx_functions ==> ~code_end_var f x` by
    metis_tac[code_end_var_absent] >>
  simp[label_flow_own_ok_def] >> rpt strip_tac >> res_tac >>
  `label_positions_ok inst /\ opaque_use_ok fn` by
    (fs[o1_source_unit_ok_def, unit_shape_ok_def, fn_shape_ok_def,
        EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `LENGTH inst.inst_operands = 3` by
    (res_tac >> gvs[source_inst_ok_def]) >>
  gvs[LENGTH_EQ_NUM_compute] >>
  rename1 `inst.inst_operands = [dst; src; sz]` >>
  `!x. src = Var x ==> ~retpc_var fn x` by
    (rpt strip_tac >>
     qpat_x_assum `opaque_use_ok fn`
       (mp_tac o REWRITE_RULE [opaque_use_ok_def]) >>
     disch_then (qspecl_then [`inst`, `x`] mp_tac) >>
     simp[retpc_use_ok_def]) >>
  Cases_on `src` >> gvs[is_label_operand_def, label_positions_ok_def] >>
  metis_tac[]
QED

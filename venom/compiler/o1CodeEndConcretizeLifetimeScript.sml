Theory o1CodeEndConcretizeLifetime
Ancestors
  o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp
  concretizeMemLocDefs venomPassDispatcher o1PassContract venomInst list

Theorem concretize_stage_protected_lifetime:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C.ctx_functions ==>
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
        MEM (Var x) j.inst_operands ==>
        j.inst_opcode = CODECOPY /\
        (?dst sz. j.inst_operands = [dst; Var x; sz] /\
          dst <> Var x /\ sz <> Var x) /\
        ?pre post. bb.bb_instructions = pre ++ d::j::post)) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >> gvs[] >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_concretize,
      concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  rename1 `code_end_var (apply_context_concretize_layout ctx layout f) x` >>
  `!y. code_end_var (apply_context_concretize_layout ctx layout f) y <=>
       code_end_var (concretize_function_with_positions layout.cl_positions f) y` by
    (gen_tac >> irule code_end_var_same_blocks >>
     simp[apply_context_concretize_layout_def, apply_concretize_layout_def]) >>
  gvs[fn_insts_def, apply_context_concretize_layout_def,
      apply_concretize_layout_def] >>
  qpat_x_assum `!f. MEM f C.ctx_functions ==> _` drule >> strip_tac >>
  drule (SRULE [fn_insts_def] concretize_function_code_end_lifetime) >>
  disch_then (qspec_then `layout.cl_positions` mp_tac) >>
  simp[fn_insts_def] >> metis_tac[]
QED

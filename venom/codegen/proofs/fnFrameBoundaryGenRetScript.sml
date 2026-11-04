Theory fnFrameBoundaryGenRet
Ancestors
  genFrameSim frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map callLayoutDefs list rich_list

Theorem release_dead_spills_stack:
  (release_dead_spills nl ps).ps_stack = ps.ps_stack
Proof
  simp[release_dead_spills_def] >>
  qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v nl | Label v => T)
    (fmap_to_alist ps.ps_spilled)`, `xs`) >>
  qid_spec_tac `ps` >> Induct_on `xs` >> simp[] >>
  Cases_on `h` >> simp[]
QED

Theorem ret_plan_decompose:
  inst.inst_opcode = RET /\ inst_wf inst /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) ==>
  ?iops prepared rops arranged.
    emit_input_plan RET (compute_operands inst) nl ps = (iops, prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops, arranged) /\
    ops = iops ++ rops ++ [SOEmit "JUMP"] /\
    final.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack
Proof
  strip_tac >>
  `inst.inst_outputs = []` by
    (gvs[inst_wf_def] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      generate_regular_inst_plan_def, is_commutative_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  gvs[generate_emit_ops_def, venom_to_evm_name_def] >>
  gvs[release_dead_spills_stack] >>
  metis_tac[]
QED

Theorem ret_source_values:
  inst.inst_opcode = RET /\ step_inst fuel ctx inst vs = IntRet ret vs' ==>
  vs' = vs /\ ?vals. eval_operands inst.inst_operands vs = SOME vals /\
    vals <> [] /\ ret.iret_values = FRONT vals
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  Cases_on `x` >> gvs[]
QED

Theorem ret_payload_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = RET /\
  inst.inst_operands = front ++ [Var pc] /\ MEM (Var x) front ==>
  ~retpc_var fn x
Proof
  strip_tac >> strip_tac >>
  `MEM (Var x) inst.inst_operands` by simp[] >>
  drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def] >> strip_tac >> gvs[]
QED

Theorem eval_operands_append:
  !xs ys s. eval_operands (xs ++ ys) s =
    OPTION_BIND (eval_operands xs s) (\vx.
      OPTION_BIND (eval_operands ys s) (\vy. SOME (vx ++ vy)))
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands xs s` >> simp[] >>
  Cases_on `eval_operands ys s` >> simp[]
QED

Theorem eval_operands_reverse:
  !xs s. eval_operands (REVERSE xs) s =
    OPTION_MAP REVERSE (eval_operands xs s)
Proof
  Induct >> simp[eval_operands_def, eval_operands_append] >> rpt gen_tac >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands xs s` >> simp[]
QED

Theorem ret_frame_view_values:
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  opaque_use_ok fn /\ retpc_shape_ok fn /\
  step_inst fuel ctx inst vs = IntRet ret vs' ==>
  vs' = vs /\ eval_operands (REVERSE (compute_operands inst))
    (frame_view fn ra vs) = SOME (ra :: REVERSE ret.iret_values)
Proof
  strip_tac >> drule_all ret_source_values >> strip_tac >> gvs[] >>
  `?front x. inst.inst_operands = front ++ [Var x] /\
    retpc_var (reachable_fn fn) x` by
    (gvs[retpc_shape_ok_def] >> metis_tac[]) >>
  `retpc_var fn x` by metis_tac[reachable_retpc_var] >>
  `MEM inst (fn_insts fn)` by
    (irule reachable_fn_insts_nonphi >> simp[]) >>
  `!y. MEM (Var y) front ==> ~retpc_var fn y` by
    metis_tac[ret_payload_not_retpc] >>
  `eval_operands front (frame_view fn ra vs) = eval_operands front vs` by
    (mp_tac (Q.INST [`ops` |-> `front`, `s` |-> `vs`,
                     `m` |-> `vs.vs_memory`] eval_operands_frame_view) >>
     `frame_view fn ra vs with vs_memory := vs.vs_memory = frame_view fn ra vs` by
       simp[frame_view_def, venom_state_component_equality] >>
     simp[]) >>
  gvs[eval_operands_append, eval_operands_def, AllCaseEqs()] >>
  gvs[compute_operands_def, python_stack_operands_def,
      ir_specific_operand_order_def, eval_operands_reverse,
      eval_operands_append, eval_operands_def, eval_operand_def,
      lookup_var_def, frame_view_def, FLOOKUP_FMAP_MAP2] >>
  simp[rich_listTheory.FRONT_APPEND_NOT_NIL]
QED

Theorem get_params_param_prefix:
  !prefix body. EVERY (\i. is_param_opcode i.inst_opcode) prefix ==>
    get_params (prefix ++ body) = prefix ++ get_params body
Proof
  Induct >> simp[get_params_def]
QED

Theorem canonical_retpc_in_params:
  canonical_param_prefix fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETPC_PARAM ==>
  fn_has_retpc fn
Proof
  simp[canonical_param_prefix_iff] >> strip_tac >>
  gvs[fn_has_retpc_def, fn_insts_def, fn_insts_blocks_def,
      MEM_FLAT, MEM_MAP, no_param_insts_def, EVERY_MEM,
      is_param_opcode_def] >>
  simp[get_params_param_prefix, EVERY_MEM, is_param_opcode_def,
       get_params_def, EXISTS_APPEND] >>
  gvs[is_param_opcode_iff, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem retpc_var_has_param:
  codegen_ready_fn fn /\ retpc_var fn x ==> fn_has_retpc fn
Proof
  simp[codegen_ready_fn_def, retpc_var_def] >> strip_tac >>
  drule copy_phi_var_has_seed >> strip_tac >>
  irule canonical_retpc_in_params >> metis_tac[]
QED

Theorem ret_source_frame_boundary:
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
  step_inst fuel ctx inst vs = IntRet ret vs' ==>
  vs' = vs /\ fn_has_retpc fn /\
  eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) =
    SOME (ra :: REVERSE ret.iret_values)
Proof
  strip_tac >>
  drule_all ret_frame_view_values >> strip_tac >> simp[] >>
  `?front x. inst.inst_operands = front ++ [Var x] /\
    retpc_var (reachable_fn fn) x` by
    (gvs[retpc_shape_ok_def] >> metis_tac[]) >>
  metis_tac[reachable_retpc_var, retpc_var_has_param]
QED

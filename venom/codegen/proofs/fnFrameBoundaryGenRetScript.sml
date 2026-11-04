Theory fnFrameBoundaryGenRet
Ancestors
  genFrameSim frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst fcgDefs livenessDefs dfgDefs
  venomWf venomEffects stackPlanOps asmIR frameViewFacts finite_map callLayoutDefs list rich_list reorderSim planWf stackModel

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

Theorem reduce_depth_plan_small_result:
  reduce_depth_plan fuel targets op f len ps = (ops, ps') /\
  LENGTH ps'.ps_stack <= 16 ==> ops = [] /\ ps' = ps
Proof
  strip_tac >>
  `MIN 17 (LENGTH ps.ps_stack) <= LENGTH ps'.ps_stack` by
    metis_tac[reduce_depth_plan_length_floor] >>
  `LENGTH ps.ps_stack <= 16` by (gvs[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  Cases_on `fuel` >> gvs[reduce_depth_plan_def] >>
  Cases_on `stack_get_unfixed_depth op f len ps.ps_stack` >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `x <= 16` by decide_tac >> gvs[]
QED

Theorem do_swap_small_result:
  do_swap dist ps = (ops, ps') /\ LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= 16 /\
  LENGTH ps.ps_stack = LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  Cases_on `dist = 0` >> simp[do_swap_def] >>
  Cases_on `dist <= 16`
  >- (simp[do_swap_def] >> strip_tac >> gvs[] >>
      simp[stack_swap_length]) >>
  simp[do_swap_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem do_dup_small_result:
  dist < LENGTH ps.ps_stack /\ do_dup dist ps = (ops, ps') /\
  LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack < LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  Cases_on `dist <= 15`
  >- (simp[do_dup_def] >> strip_tac >> gvs[stack_dup_def]) >>
  simp[do_dup_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[stack_dup_def]
QED

Theorem do_restore_no_spill:
  do_restore op ps = (ops, ps') ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  simp[do_restore_def] >> Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[] >> strip_tac >> gvs[stack_push_def]
QED

Theorem emit_one_input_small_result:
  emit_one_input opc nl op ps = (ops, ps') /\ LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  simp[emit_one_input_def] >> pairarg_tac >> simp[] >>
  `LENGTH ps.ps_stack <= LENGTH ps1.ps_stack /\
   (!off. ~MEM (SOSpill off) restore_ops)` by
    (Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)` >>
     gvs[] >> metis_tac[do_restore_no_spill]) >>
  Cases_on `op` >> simp[]
  >- (strip_tac >> gvs[stack_push_def])
  >- (IF_CASES_TAC >> simp[]
      >- (Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[]
          >- (strip_tac >> gvs[]) >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          drule stack_get_depth_props >> strip_tac >>
          drule_all do_dup_small_result >> strip_tac >> simp[]) >>
      strip_tac >> gvs[]) >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[stack_push_def]
QED

Theorem emit_input_plan_small_result:
  !inputs ps ops ps'.
  emit_input_plan opc inputs nl ps = (ops, ps') /\ LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  Induct >> simp[emit_input_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `LENGTH ps1.ps_stack <= 16` by decide_tac >>
  drule_all emit_one_input_small_result >> strip_tac >> simp[]
QED

Theorem reorder_one_small_result:
  reorder_one dfg targets idx op ps = (ops, ps') /\ LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  simp[reorder_one_def] >> pairarg_tac >> simp[] >>
  `LENGTH ps.ps_stack <= LENGTH ps1.ps_stack /\
   (!off. ~MEM (SOSpill off) restore_ops)` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                  (LENGTH targets) ps.ps_stack` >> gvs[]
     >- (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
         metis_tac[do_restore_no_spill])) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
              (LENGTH targets) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `LENGTH ps2.ps_stack <= 16 ==> ps2 = ps1 /\ reduce_ops = []` by
    (Cases_on `x > 16` >> gvs[] >> metis_tac[reduce_depth_plan_small_result]) >>
  qpat_x_assum `(case _ of _ => _) = (restore_ops, ps1)` kall_tac >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[stack_poke_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all do_swap_small_result >> strip_tac >>
  `LENGTH ps3.ps_stack <= 16` by decide_tac >>
  qpat_x_assum `do_swap _ ps3 = _` kall_tac >>
  drule_all do_swap_small_result >> strip_tac >> gvs[]
QED

Theorem reorder_fold_small_result[local]:
  !xs acc ps ops ps'.
  FOLDL (\(ops, ps) (idx, op).
    let (step_ops, next) = reorder_one dfg targets idx op ps in
      (ops ++ step_ops, next)) (acc, ps) xs = (ops, ps') /\
  LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. MEM (SOSpill off) ops ==> MEM (SOSpill off) acc)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >> fs[LET_THM] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `LENGTH next.ps_stack <= 16` by decide_tac >>
  drule_all reorder_one_small_result >> strip_tac >>
  conj_tac >- decide_tac >> gvs[]
QED

Theorem reorder_plan_small_result:
  reorder_plan dfg targets ps = (ops, ps') /\ LENGTH ps'.ps_stack <= 16 ==>
  LENGTH ps.ps_stack <= LENGTH ps'.ps_stack /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  simp[reorder_plan_def] >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [LET_THM] reorder_fold_small_result) >> simp[]
QED

Theorem ret_plan_no_spill:
  inst.inst_opcode = RET /\ inst_wf inst /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps =
    SOME (ops, final) /\ final.ps_stack = [] /\
  LENGTH (compute_operands inst) <= 16 ==>
  !off. ~MEM (SOSpill off) ops
Proof
  strip_tac >> drule_all ret_plan_decompose >> strip_tac >>
  `LENGTH arranged.ps_stack <= 16` by
    (gvs[stack_pop_def, DROP_EQ_NIL] >> decide_tac) >>
  drule_all reorder_plan_small_result >> strip_tac >>
  `LENGTH prepared.ps_stack <= 16` by decide_tac >>
  drule_all emit_input_plan_small_result >> strip_tac >> gvs[]
QED

Theory fnFrameBoundaryGenRet
Ancestors
  genFrameSim frameRel contextCodegenRel codegenRel emitSim
  fnFrameTerminalPrep preparedPrefixSim asmFrame strongPrefixSim prefixSim stackOpSim
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


val ret_dispatch = map
  (fn name => SIMP_CONV (srw_ss())
    [asm_step_def, asm_step_op_def, asm_step_arith_def,
     asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
     asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
     asm_step_context_def, swap_table_def, dup_table_def, log_table_def]
    ``asm_step lo o2pc (AsmOp ^name) st``)
  [``"POP"``, ``"MLOAD"``,
   ``"SWAP1"``, ``"SWAP2"``, ``"SWAP3"``, ``"SWAP4"``,
   ``"SWAP5"``, ``"SWAP6"``, ``"SWAP7"``, ``"SWAP8"``,
   ``"SWAP9"``, ``"SWAP10"``, ``"SWAP11"``, ``"SWAP12"``,
   ``"SWAP13"``, ``"SWAP14"``, ``"SWAP15"``, ``"SWAP16"``, ``"SWAP?"``,
   ``"DUP1"``, ``"DUP2"``, ``"DUP3"``, ``"DUP4"``,
   ``"DUP5"``, ``"DUP6"``, ``"DUP7"``, ``"DUP8"``,
   ``"DUP9"``, ``"DUP10"``, ``"DUP11"``, ``"DUP12"``,
   ``"DUP13"``, ``"DUP14"``, ``"DUP15"``, ``"DUP16"``, ``"DUP?"``];

Theorem no_spill_prefix_step_bytes:
  !op initial_fmp ins lo o2pc st st'.
  is_prefix_op op /\ (!off. op <> SOSpill off) /\
  MEM ins (exec_stack_op initial_fmp op) /\
  asm_step lo o2pc ins st = AsmOK st' ==>
  st'.as_pc = st.as_pc + 1 /\
  (!b. read_byte b st'.as_memory = read_byte b st.as_memory)
Proof
  Cases >> simp[is_prefix_op_def, exec_stack_op_def, MEM_REPLICATE] >>
  rpt gen_tac >> strip_tac
  >- (Cases_on `o'` >> gvs[exec_stack_op_def, asm_step_def, asm_next_def,
        AllCaseEqs()])
  >- (fs ret_dispatch >> gvs[asm_pop_def, asm_next_def, AllCaseEqs()])
  >- (pop_assum mp_tac >> pure_rewrite_tac[swap_name_def] >>
      rpt IF_CASES_TAC >> strip_tac >> fs ret_dispatch >>
      gvs[asm_swap_def, asm_next_def, AllCaseEqs()])
  >- (pop_assum mp_tac >> pure_rewrite_tac[dup_name_def] >>
      rpt IF_CASES_TAC >> strip_tac >> fs ret_dispatch >>
      gvs[asm_dup_def, asm_next_def, AllCaseEqs()])
  >> fs ret_dispatch >>
  gvs[asm_step_def, AllCaseEqs()] >>
  fs[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
     asm_step_bitwise_def, asm_step_memory_def] >>
  gvs[asm_mload_def, asm_next_def, AllCaseEqs(), read_byte_expand]
QED

Theorem read_only_block_bytes[local]:
  !code st st'.
  asm_block_at prog st.as_pc code /\
  asm_steps lo o2pc prog (LENGTH code) st = AsmOK st' /\
  (!ai si si'. MEM ai code /\ asm_step lo o2pc ai si = AsmOK si' ==>
    si'.as_pc = si.as_pc + 1 /\
    (!b. read_byte b si'.as_memory = read_byte b si.as_memory)) ==>
  !b. read_byte b st'.as_memory = read_byte b st.as_memory
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> simp[asm_block_at_cons, Once asm_steps_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `s''.as_pc = st.as_pc + 1 /\
   (!b. read_byte b s''.as_memory = read_byte b st.as_memory)` by
    (qpat_x_assum `!ai si si'. _` irule >> simp[] >> metis_tac[]) >>
  `!b. read_byte b st'.as_memory = read_byte b s''.as_memory` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem no_spill_prefix_bytes:
  EVERY is_prefix_op ops /\ (!off. ~MEM (SOSpill off) ops) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' ==>
  !b. read_byte b st'.as_memory = read_byte b st.as_memory
Proof
  strip_tac >> irule read_only_block_bytes >>
  qexists `execute_plan initial_fmp ops` >> simp[] >>
  qexistsl_tac [`lo`, `o2pc`, `prog`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `?op. MEM op ops /\ MEM ai (exec_stack_op initial_fmp op)` by
    (gvs[execute_plan_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  irule no_spill_prefix_step_bytes >>
  qexistsl_tac [`initial_fmp`, `ai`, `lo`, `o2pc`, `op`] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem ret_frame_prefix:
  !ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
    base ps vs st ops final ra rest mem0 values.
  inst.inst_opcode = RET /\ inst_wf inst /\
  generated_plan_state_wf base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  final.ps_stack = [] /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  eval_operands (REVERSE (compute_operands inst)) (frame_view fn ra vs) = SOME values ==>
  ?n mid.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp "JUMP"] /\
    mid.as_stack = values ++ rest /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      read_byte b mid.as_memory = read_byte b mem0) /\
    shared_state_rel vs mid
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ret_plan_no_spill >> strip_tac >>
  drule_all ret_plan_decompose >> strip_tac >>
  drule fn_frame_inv_local_state >> strip_tac >>
  suspend "local_run"
QED

Resume ret_frame_prefix[local_run]:
  rename1 `generated_plan_state_wf spillbase ps` >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op _ /\ is_var_operand op ==> _` drule >>
     simp[] >> strip_tac
     >- (drule stack_get_depth_props >> simp[stack_peek_def] >>
         strip_tac >> disj1_tac >>
         qpat_x_assum `EL _ _ = op` (SUBST1_TAC o SYM) >>
         irule EL_MEM >> decide_tac) >>
     Cases_on `op IN FDOM ps.ps_spilled` >> fs[FLOOKUP_DEF]) >>
  `residual_budget_wf spillbase [] ps /\ plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (fs[generated_plan_state_wf_def] >>
     metis_tac[residual_budget_wf_canonical]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops)` by
    (pure_rewrite_tac[EVERY_MEM] >> Cases >> simp[] >> metis_tac[MEM_APPEND]) >>
  `asm_block_at prog (st with as_stack := top).as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    (gvs[execute_plan_append, asm_block_at_append]) >>
  `PERM (compute_operands inst) (compute_operands inst)` by simp[] >>
  `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` by gvs[] >>
  `!op. operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs) lo op` by
    (Cases >> simp[operand_val_def]) >>
  `!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo op =
    operand_val (frame_view fn ra vs with vs_memory := st.as_memory) lo at` by
    (simp[] >> metis_tac[]) >>
  suspend "labels"
QED

Resume ret_frame_prefix[labels]:
  `LIST_REL (\op value. operand_val (frame_view fn ra vs) lo op = SOME value)
    (REVERSE (compute_operands inst)) values` by
    (irule eval_operands_operand_val_rel >> simp[]) >>
  `!op. MEM op (compute_operands inst) ==>
    IS_SOME (operand_val (frame_view fn ra vs) lo op)` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[LIST_REL_EL_EQN] >> strip_tac >>
     simp[MEM_EL] >> rpt strip_tac >>
     qpat_x_assum `!n. n < _ ==> _` (qspec_then
       `LENGTH (compute_operands inst) - (n + 1)` mp_tac) >>
     `LENGTH (compute_operands inst) - (n + 1) < LENGTH (compute_operands inst)` by decide_tac >>
     simp[EL_REVERSE] >>
     `LENGTH (compute_operands inst) - (LENGTH (compute_operands inst) - (n + 1) + 1) = n` by decide_tac >>
     simp[GSYM arithmeticTheory.ADD1]) >>
  `!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)` by
    (rpt strip_tac >> first_x_assum drule >>
     Cases_on `FLOOKUP lo l` >> simp[operand_val_def]) >>
  `RET <> INVOKE` by simp[] >>
  drule_all selected_prefix_prepared_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  suspend "lift"
QED

Resume ret_frame_prefix[lift]:
  rename1 `venom_asm_rel lo arranged _ endpoint` >>
  `prefix_wf lo (LENGTH ps.ps_stack) iops` by
    (`prefix_wf lo (LENGTH ps.ps_stack)
        (FST (emit_input_plan RET (compute_operands inst) nl ps))` by
       (irule (cj 1 emit_input_plan_wf_len) >> simp[]) >> gvs[]) >>
  `prefix_wf (lo:string |-> num) (LENGTH prepared.ps_stack) rops` by
    (qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
     qpat_x_assum `LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack` mp_tac >>
     qpat_x_assum `LENGTH (compute_operands inst) <= 16` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     mp_tac (Q.SPECL [`dfg`, `compute_operands inst`, `prepared`, `lo`]
       (INST_TYPE [alpha |-> ``:num``] reorder_plan_wf_len)) >> simp[] >> strip_tac >> simp[]) >>
  `EVERY is_prefix_op (iops ++ rops)` by
    (simp[] >> metis_tac[prefix_wf_every_prefix_op]) >>
  `!off. ~MEM (SOSpill off) (iops ++ rops)` by
    (gvs[] >> metis_tac[]) >>
  drule_all no_spill_prefix_bytes >> strip_tac >>
  `arranged.ps_stack = compute_operands inst` by gvs[] >>
  `endpoint.as_stack = values` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `venom_asm_rel lo arranged _ endpoint` mp_tac >>
     qpat_x_assum `!op. operand_val (_ with vs_memory := _) _ op = _` mp_tac >>
     qpat_x_assum `arranged.ps_stack = compute_operands inst` mp_tac >>
     qpat_x_assum `EVERY (\op. op <> dead_stack_marker /\ _) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, plan_stack_rel_def, LIST_REL_EL_EQN, EVERY_MEM] >>
     rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >>
     simp[] >> strip_tac >>
     `MEM (EL x (REVERSE (compute_operands inst))) (compute_operands inst)` by
       (once_rewrite_tac[GSYM MEM_REVERSE] >> irule EL_MEM >> simp[]) >>
     `x < LENGTH (compute_operands inst)` by decide_tac >>
     qpat_x_assum `!i. i < LENGTH (compute_operands inst) ==> _`
       (qspec_then `x` mp_tac) >> simp[] >>
     `EL x (REVERSE (compute_operands inst)) <> dead_stack_marker` by metis_tac[] >>
     simp[]) >>
  suspend "finish"
QED

Resume ret_frame_prefix[finish]:
  `context_memory_rel cplan vs.vs_memory st.as_memory /\
   (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
     read_byte b st.as_memory = read_byte b mem0)` by
    (qpat_x_assum `fn_frame_inv _ _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_def] >>
     metis_tac[]) >>
  `context_memory_rel cplan vs.vs_memory endpoint.as_memory` by
    (gvs[context_memory_rel_def] >> metis_tac[]) >>
  `shared_state_rel vs endpoint` by
    (qpat_x_assum `venom_asm_rel lo arranged _ endpoint` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[venom_asm_rel_def, shared_state_rel_def, venom_asm_terminal_rel_def,
       frame_view_def]) >>
  drule asm_steps_frame >> disch_then (qspec_then `rest` assume_tac) >>
  `st with as_stack := top ++ rest = st` by
    simp[asm_state_component_equality] >>
  qexistsl_tac [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `endpoint with as_stack := endpoint.as_stack ++ rest`] >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (gvs[execute_plan_append, asm_block_at_append, execute_plan_def,
          exec_stack_op_def]) >>
  gvs[shared_state_rel_def, venom_asm_terminal_rel_def] >>
  metis_tac[]
QED

Finalise ret_frame_prefix

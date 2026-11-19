Theory requestCutFrameReady
Ancestors
  requestCutPrimitiveReady requestCutInvokeReady
  fnFramePrefixDriver fnFramePrefixEntry fnFramePrefix fnFrameSymbolicPrefix
  fnBlockBodySteps fnBlockBodyHelpers fnBlockBody o1ContractCfgNormJointCursors
  unitShapeDefs contextCodegenRel frameJointTransition stackPlanGen stackPlanTypes
  asmIR venomExecSemantics venomState venomInst finite_map list

Theorem active_frame_no_primitive_error[local]:
  active_frame_plan rp unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode <> PHI ==>
    EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  pure_rewrite_tac[active_frame_plan_def] >>
  strip_tac >> drule_all body_plan_active_inst >> strip_tac >>
  drule_all body_plan_inv_inst >> strip_tac >>
  drule body_plan_inv_facts >> strip_tac >>
  drule_all body_plan_inv_static >> strip_tac >>
  irule request_cut_primitive_no_error >> asm_rewrite_tac[] >>
  strip_tac >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule reachable_fn_mem_inst >> simp[] >> qexists_tac `bb` >>
     simp[] >> metis_tac[body_plan_inv_def]) >>
  fs[retpc_shape_ok_def] >> metis_tac[listTheory.APPEND_eq_NIL, listTheory.NOT_CONS_NIL]
QED

Theorem entry_frame_no_primitive_error[local]:
  entry_frame_plan rp unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode <> PHI ==>
    EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
  >- (drule_all entry_frame_active_param >> strip_tac >>
      drule_all entry_frame_plan_next >>
      disch_then (qspec_then `fuel` strip_assume_tac) >> simp[]) >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (fs[entry_frame_plan_def] >> gvs[] >> decide_tac) >>
  drule_all entry_frame_plan_ready >> strip_tac >>
  drule_all active_frame_no_primitive_error >> simp[]
QED

Theorem compute_operands_subset[local]:
  MEM op (compute_operands inst) ==> MEM op inst.inst_operands
Proof
  rw[compute_operands_def, get_non_label_operands_def, MEM_FILTER] >>
  metis_tac[MEM_TL]
QED

Theorem request_cut_operand_ready:
  wf_ssa fn /\ wf_function fn /\ supply_prefix_defined fn s /\
  active_inst fn inst s /\ inst.inst_opcode <> PHI /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP s.vs_labels l)) ==>
  EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[EVERY_MEM] >> qx_gen_tac `op` >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, FLOOKUP_DEF]
  >- (rename1 `v IN FDOM s.vs_vars` >>
      drule compute_operands_subset >> strip_tac >>
      drule_all supply_cursor_use_defined >> simp[]) >>
  qpat_x_assum `!l. MEM (Label l) _ ==> _` drule >> simp[FLOOKUP_DEF]
QED

(* The selected C9 frame handles parameter fetches. The paired cursor
   supplies defined operands for its ordinary fetches. *)
Theorem request_cut_stopped_noninvoke_ready:
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved) q8
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ((?base es.
      normal_frame_plan rp unit cpl prog base es
        (JointConfig stk PG G tn fn inst s oms om hs h) ast) \/
   (?env base es ss.
      normal_frame_symbolic_plan env rp unit cpl prog base es
        (JointConfig stk PG G tn fn inst s oms om hs h) ast ss)) /\
  inst.inst_opcode <> INVOKE /\
  (!l. MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP s.vs_labels l)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule cfg_norm_joint_cursor_supply >> strip_tac >>
  `inst.inst_opcode <> PHI ==>
     EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)` by
    metis_tac[request_cut_operand_ready] >>
  `(?a ra rest mem. active_frame_plan rp unit cpl prog fn s a ra rest mem) \/
   (?entry a ra pc_ret rest mem.
      entry_frame_plan rp unit cpl prog fn entry s a ra pc_ret rest mem)` by
    (qpat_x_assum `(?base es. _) \/ _`
       (strip_assume_tac o REWRITE_RULE [normal_frame_plan_def, normal_frame_symbolic_plan_def,
         active_frame_symbolic_plan_def, active_frame_plan_def, entry_frame_symbolic_plan_def]) >>
     metis_tac[active_frame_plan_def]) >>
  pop_assum strip_assume_tac
  >- (drule_all active_frame_no_primitive_error >> simp[]) >>
  drule_all entry_frame_no_primitive_error >> simp[]
QED

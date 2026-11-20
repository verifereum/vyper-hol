Theory requestCutFrameReady
Ancestors
  requestCutPrimitiveReady requestCutInvokeReady
  fnFramePrefixDriver fnFramePrefixEntry fnFramePrefix fnFrameSymbolicPrefix
  fnBlockBodySteps fnBlockBodyHelpers fnBlockBody o1ContractCfgNormJointCursors
  unitShapeDefs contextCodegenRel frameJointTransition stackPlanGen stackPlanTypes
  asmIR venomExecSemantics venomState venomInst finite_map list
  fnPlanPlaceRevertPostamble asmSymRelocLabelsOwn

Theorem active_frame_no_primitive_error_reloc[local]:
  active_frame_plan_reloc lo rp unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode <> PHI ==>
    EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  pure_rewrite_tac[active_frame_plan_reloc_def] >>
  strip_tac >> drule_all body_plan_active_inst_reloc >> strip_tac >>
  drule_all body_plan_inv_inst_reloc >> strip_tac >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  drule_all body_plan_inv_static_reloc >> strip_tac >>
  irule request_cut_primitive_no_error >> asm_rewrite_tac[] >>
  strip_tac >>
  `MEM inst (fn_insts (reachable_fn fn))` by
    (irule reachable_fn_mem_inst >> simp[] >> qexists_tac `bb` >>
     simp[] >> metis_tac[body_plan_inv_reloc_def]) >>
  fs[retpc_shape_ok_def] >> metis_tac[listTheory.APPEND_eq_NIL, listTheory.NOT_CONS_NIL]
QED

Theorem entry_frame_no_primitive_error_reloc[local]:
  entry_frame_plan_reloc lo rp unit cpl prog fn entry s ast ra pc_ret rest mem0 /\
  code_labels_agree prog lo /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode <> PHI ==>
    EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `s.vs_inst_idx < LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`
  >- (drule_all entry_frame_active_param_reloc >> strip_tac >>
      drule_all entry_frame_plan_next_reloc >>
      disch_then (qspec_then `fuel` strip_assume_tac) >> simp[]) >>
  `s.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` by
    (fs[entry_frame_plan_reloc_def] >> gvs[] >> decide_tac) >>
  drule_all entry_frame_plan_ready_reloc >> strip_tac >>
  drule_all active_frame_no_primitive_error_reloc >> simp[]
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
Theorem request_cut_stopped_noninvoke_ready_reloc:
  cfg_norm_joint_cursors C8 unit.cu_context (schedules,(rounds,cells),saved) q8
    (JointConfig stk PG G tn fn inst s oms om hs h) /\
  code_labels_agree prog lo /\
  (?ra rest mem0.
    active_frame_plan_reloc lo rp unit cpl prog fn s ast ra rest mem0 \/
    ?entry pc_ret. entry_frame_plan_reloc lo rp unit cpl prog fn entry s ast
      ra pc_ret rest mem0) /\
  inst.inst_opcode <> INVOKE /\
  (inst.inst_opcode <> PHI ==>
    !l. MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP s.vs_labels l)) ==>
  step_inst fuel unit.cu_context inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule cfg_norm_joint_cursor_supply >> strip_tac >>
  `inst.inst_opcode <> PHI ==>
     EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst)` by
    metis_tac[request_cut_operand_ready] >>
  qpat_x_assum `?ra rest mem0. _` strip_assume_tac
  >- (drule_all active_frame_no_primitive_error_reloc >> simp[]) >>
  drule_all entry_frame_no_primitive_error_reloc >> simp[]
QED

Theory o1LowerDloadSuppliedSegmentResources
Ancestors
  o1LowerDloadSuppliedSegmentTransport o1LowerDloadSuppliedSegmentControl
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadRawBridge
  o1PassLift memSafeRun unitMemInv
  o1PassContract lowerDloadDefs contextRawReachable contextCodegenRel
  venomExecProps venomExecSemantics list

Theorem ld_raw_code_data:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rw[enters_block_def, setup_callee_def] >>
  imp_res_tac venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  imp_res_tac step_inst_ok_code_data >>
  gvs[setup_callee_def, AllCaseEqs()] >>
  qpat_x_assum `s_phi = _` (fn th => once_rewrite_tac [th]) >> simp[]
QED

Theorem ld_raw_code_layout:
  raw_reachable vs C fn inst s /\ code_layout_valid vs ==>
  code_layout_valid s
Proof
  strip_tac >> drule ld_raw_code_data >> strip_tac >>
  drule raw_reachable_labels >> strip_tac >>
  gvs[code_layout_valid_def]
QED

Theorem ld_joint_raw_reachable:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C ==>
  raw_reachable vs C fn inst s
Proof
  strip_tac >> drule ld_joint_source >> strip_tac >>
  drule occ_frame_reachable_projection >> strip_tac >>
  irule ld_frame_raw_reachable >>
  metis_tac[ld_ctx_shape_lookup_wf]
QED

Theorem ld_joint_segment_layout:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs ==>
  code_layout_valid t
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_segment_offset:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  mem_inv dload_offset_ok C vs /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [op]) \/
   (inst.inst_opcode = DLOADBYTES /\
    ?dst sz. inst.inst_operands = [dst;op;sz])) /\
  eval_operand op s = SOME off ==>
  w2n off + (LENGTH t.vs_code - LENGTH t.vs_data_section) < dimword (:256)
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_segment_control:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ active_inst fn inst s /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [ptr] /\
     inst.inst_outputs = [out]) \/
   (inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dst;ptr;sz])) ==>
  ?u fn' v es v' bb'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\
    lower_dload_inst_supply v inst = (es,v') /\
    EVERY (\id. id < v.irs_next_inst) (fn_ir_inst_ids fn) /\
    (!x. MEM x (fn_ir_vars fn) ==> MEM x v.irs_used_vars) /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE (LENGTH es) (DROP t.vs_inst_idx bb'.bb_instructions) = es /\
    t.vs_inst_idx + LENGTH es <= LENGTH bb'.bb_instructions /\
    ~MEM (HD es).inst_id (fn_ir_inst_ids fn) /\
    EVERY (\x. ~MEM x (fn_ir_vars fn))
      (FLAT (MAP (\i. i.inst_outputs)
        (TAKE (if inst.inst_opcode = DLOAD then 2 else 1) es))) /\
    (!p ov. inst.inst_opcode = DLOAD /\ inst.inst_operands = [p] /\
      inst.inst_outputs = [ov] ==>
      ld_joint_scratch u fn inst.inst_id (HD es).inst_id) /\
    (!next. active_inst fn next (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ld_joint_control u fn fn'
        (s with vs_inst_idx := SUC s.vs_inst_idx)
        (t with vs_inst_idx := t.vs_inst_idx + LENGTH es))
Proof
  (* P4a in progress *) cheat
QED

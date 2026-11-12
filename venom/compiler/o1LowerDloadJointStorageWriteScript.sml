(* Masked shared-store writes at occurrence boundaries. *)
Theory o1LowerDloadJointStorageWrite
Ancestors
  o1LowerDloadJointStorageRead o1LowerDloadJointMemoryWrite
  o1LowerDloadJointScalar o1LowerDloadJointAssign o1LowerDloadShared
  o1LowerDloadJointRelation o1LowerDloadEnvironment o1LowerDloadOccurrence
  ptrDiscipline venomState venomExecSemantics venomInst
  finite_map list pred_set combin vfmState pointerConfinedDefs memLocDefs
  unitShapeDefs o1LowerDloadRelocationKernel contextCodegenRel o1PassContract venomWf

Theorem ld_shared_sstore:
  ld_shared_agree D A tn s t /\
  s.vs_call_ctx.cc_address = A /\ t.vs_call_ctx.cc_address = A /\
  word_agree_except m v w ==>
  ld_shared_agree D A (tn with t_stor := key_update tn.t_stor key m)
    (sstore key v s) (sstore key w t)
Proof
  simp[ld_shared_agree_def, sstore_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[key_update_def, word_agree_except_def])
  >- (qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `t.vs_call_ctx.cc_address` mp_tac) >>
      disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED

Theorem ld_shared_tstore:
  ld_shared_agree D A tn s t /\
  s.vs_call_ctx.cc_address = A /\ t.vs_call_ctx.cc_address = A /\
  word_agree_except m v w ==>
  ld_shared_agree D A (tn with t_trans := key_update tn.t_trans key m)
    (tstore key v s) (tstore key w t)
Proof
  simp[ld_shared_agree_def, tstore_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[key_update_def, word_agree_except_def]) >>
  simp[combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED

Theorem ld_joint_store_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ inst.inst_operands = [kop;vop] /\
  eval_operand kop s = SOME key /\ eval_operand vop s = SOME v ==>
  ?w. eval_operand kop t = SOME key /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==> op_prov H op = NONE` by
    (drule ld_joint_scalar_no_provenance >>
     gvs[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn kop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[MEM, taint_ok_def] >>
     metis_tac[]) >>
  `!vv. ~retpc_use_ok inst vv` by gvs[MEM, retpc_use_ok_def] >>
  `eval_operand kop s = eval_operand kop t` by
    (irule ld_joint_operand_clean >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  `?w. eval_operand vop t = SOME w /\
    ld_value_agree sites (op_prov H vop) (op_taint tn vop) v w` by
    (irule ld_joint_operand_value >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  qexists_tac `w` >> gvs[ld_value_agree_def]
QED

Theorem ld_joint_shared_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_accounts := sa; vs_transient := sx|> /\
  t1 = t with <|vs_accounts := ta; vs_transient := tx|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H stk PG G
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  tn1.t_var = tn.t_var /\ tn1.t_mem = tn.t_mem /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H sites X ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_storage_store_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_storage_store_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\ step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

(* Structural boundary for combined memory, immutable and log effects. *)
Theory o1LowerDloadJointInternalEffects
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointStorageWrite o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRangeRead o1LowerDloadJointAssign o1LowerDloadShared
  o1LowerDloadJointRangeCopy
  o1LowerDloadJointRelation o1LowerDloadEnvironment o1LowerDloadOccurrence
  o1LowerDloadJointScalar o1LowerDloadRelocationKernel
  ptrDiscipline venomState venomExecSemantics venomInst
  memLocDefs words pointerConfinedDefs
  finite_map list pred_set unitShapeDefs o1PassContract venomWf codegenRel contextCodegenRel

Theorem ld_joint_internal_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|> /\
  t1 = t with <|vs_memory := mt; vs_immutables := imt; vs_logs := lt|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_dyn_agree (dyn_floor C vs) tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  (* P4a in progress *) cheat
QED

(* Check that both concrete effect shapes enter the combined boundary;
   payload relations remain semantic obligations, not framing assumptions. *)
Theorem ld_internal_effect_update_shapes[local]:
  (?ms ims ls. istore off v s =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>) /\
  (?ms ims ls. (s with vs_logs := s.vs_logs ++ [ev]) =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>)
Proof
  conj_tac
  >- (qexistsl_tac [`(mstore off v s).vs_memory`,
                   `s.vs_immutables |+ (off,v)`,`s.vs_logs`] >>
      simp[istore_def, mstore_def, venom_state_component_equality]) >>
  qexistsl_tac [`s.vs_memory`,`s.vs_immutables`,`s.vs_logs ++ [ev]`] >>
  simp[venom_state_component_equality]
QED

Theorem ld_shared_istore:
  ld_shared_agree D A tn s t /\ word_agree_except m v w ==>
  ld_shared_agree D A (tn with t_imm := key_update tn.t_imm off m)
    (istore off v s) (istore off w t)
Proof
  simp[ld_shared_agree_def, istore_def, mstore_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `key = off` >>
  gvs[key_update_def, word_agree_except_def, FAPPLY_FUPDATE_THM]
QED

Theorem ld_shared_logs_append:
  ld_shared_agree D A tn s t ==>
  ld_shared_agree D A tn
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_joint_istore_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
  ?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\ op_prov G p = NONE
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_istore_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = ISTORE /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_dyn_agree (dyn_floor C vs) (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  (* P4a in progress *) cheat
QED


Theorem ld_joint_log_scalar[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  MEM op (sz::tops) ==>
  eval_operand op s = eval_operand op t
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_log_read[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  LENGTH tops = w2n tc /\ eval_operand p s = SOME x /\
  eval_operand sz s = SOME l /\ eval_operands tops s = SOME topics ==>
  ?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    eval_operands tops t = SOME topics /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_eval_operands_defined:
  !ops s. IS_SOME (eval_operands ops s) <=>
    EVERY (\op. IS_SOME (eval_operand op s)) ops
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `s` assume_tac) >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands ops s` >> gvs[]
QED

Theorem ld_joint_log_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_dyn_agree (dyn_floor C vs) (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_internal_effect_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [ISTORE; LOG] /\ step_inst fuel C inst s = OK s1 /\
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

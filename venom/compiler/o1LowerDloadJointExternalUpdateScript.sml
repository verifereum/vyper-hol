(* Common structural boundary for external-call state updates. *)
Theory o1LowerDloadJointExternalUpdate
Ancestors
  o1LowerDloadJointInternalEffects o1LowerDloadJointRelation
  o1LowerDloadEnvironment o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadJointAssign pointerConfinedDefs
  o1LowerDloadShared ptrDiscipline venomState venomExecSemantics venomInst
  finite_map list unitShapeDefs o1PassContract venomWf contextCodegenRel

Theorem ld_joint_external_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_vars := es; vs_memory := ms; vs_accounts := acs;
    vs_transient := trs; vs_logs := ls; vs_outcomes := os;
    vs_requests := rqs; vs_pending_deletions := pds; vs_returndata := rds|> /\
  t1 = t with <|vs_vars := et; vs_memory := mt; vs_accounts := act;
    vs_transient := trt; vs_logs := lt; vs_outcomes := ot;
    vs_requests := rqt; vs_pending_deletions := pdt; vs_returndata := rdt|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_dyn_agree (dyn_floor C vs) tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 /\
  s1.vs_returndata = t1.vs_returndata ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  (* P4a in progress *) cheat
QED

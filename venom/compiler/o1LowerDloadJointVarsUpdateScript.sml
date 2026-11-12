(* Frame preservation for arbitrary variable-map replacements. *)
Theory o1LowerDloadJointVarsUpdate
Ancestors
  o1LowerDloadJointAssign o1LowerDloadJointRelation o1LowerDloadEnvironment
  o1LowerDloadOccurrence o1PassContract contextCodegenRel venomWf
  venomState list ptrDiscipline o1LowerDloadShared irSupply venomInst

Theorem ld_joint_vars_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = (s with vs_vars := sv) /\ t1 = (t with vs_vars := tv) /\
  G1 = step_prov PG G inst s1 /\ H1 = occurrence_step a HP H inst s1 /\
  tn1 = step_taint inst s s1 tn /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  (* P4a in progress *) cheat
QED

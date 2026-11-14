(* Exact raw/effective annotation boundary for an erased copy. *)
Theory readonlyInvokeCopyFwdCopyAnnotations
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdRel taintAgree
  internalReturnCopyFwdSim o1LowerDloadShared
  venomExecSemantics venomState ptrDiscipline
  finite_map words list pred_set

Theorem ricf_copy_annotation_compatibility:
  G = ricf_effective_prov fn s G0 /\
  tn = ricf_effective_taint fn s tn0 /\
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Var dst;Var sv;Lit z] /\
  inst.inst_outputs = [] /\
  eval_operands inst.inst_operands s = SOME [n2w db;n2w sb;z] /\
  db < dimword(:256) /\ sb < dimword(:256) /\
  u = mcopy db sb (w2n z) s /\
  s1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
    {db+q | q < w2n z /\ sb+q IN tn0.t_mem} ==>
  step_prov PG G inst u = ricf_effective_prov fn s1 G0 /\
  step_taint inst s u tn = ricf_effective_taint fn s1 un
Proof
  strip_tac >>
  `!xs prev T m. phis_taint prev (T with t_mem := m) xs =
                  phis_taint prev T xs` by
    (Induct >> simp[phis_taint_def, phi_taint_def, op_taint_def]) >>
  `eval_operand (Var dst) s = SOME (n2w db) /\
   eval_operand (Var sv) s = SOME (n2w sb) /\
   eval_operand (Lit z) s = SOME z` by
    gvs[eval_operands_def, AllCaseEqs()] >>
  drule_all step_taint_mcopy >>
  simp[w2n_n2w] >> strip_tac >>
  gvs[step_prov_def, set_prov_def, DRESTRICT_UNIV,
      ricf_effective_prov_def, ricf_effective_taint_def,
      entry_prov_def, entry_taint_vars_def,
      mcopy_def, write_memory_with_expansion_def,
      AllCaseEqs(), taint_component_equality]
QED

(* PC-only transport leaves saved target frames and every ghost map intact. *)
Theorem ricf_cert_copy_successor:
  G = ricf_effective_prov fn s G0 /\
  tn = ricf_effective_taint fn s tn0 /\
  inst.inst_opcode = MCOPY /\
  inst.inst_operands = [Var dst;Var sv;Lit z] /\
  inst.inst_outputs = [] /\
  eval_operands inst.inst_operands s = SOME [n2w db;n2w sb;z] /\
  db < dimword(:256) /\ sb < dimword(:256) /\
  u = mcopy db sb (w2n z) s /\
  s1 = u with vs_inst_idx := SUC s.vs_inst_idx /\
  un = tn0 with t_mem :=
    (tn0.t_mem DIFF {i | db <= i /\ i < db+w2n z}) UNION
    {db+q | q < w2n z /\ sb+q IN tn0.t_mem} /\
  s.vs_inst_idx = t.vs_inst_idx /\
  ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then un else entry_taint_vars fn s un)
    fn sites maps targets G0 un cur curs u t ==>
  ricf_cert_core D ids stk PG
    (step_prov PG G inst u) (step_taint inst s u tn)
    fn sites maps targets G0 un cur curs s1
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `step_prov PG G inst u = ricf_effective_prov fn s1 G0 /\
   step_taint inst s u tn = ricf_effective_taint fn s1 un` by
    (irule ricf_copy_annotation_compatibility >> metis_tac[]) >>
  qpat_x_assum `un = _` kall_tac >>
  simp[] >> irule ricf_cert_reconstruct >>
  fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  conj_tac >- (fs[ircf_cross_def] >> metis_tac[]) >>
  conj_tac >- (fs[ricf_cert_crosses_def, ircf_cross_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[ricf_frame_agree_def, ircf_dead_def, ircf_cross_def] >>
      conj_tac
      >- (drule taint_agree_inst_idx >>
          disch_then (qspec_then `SUC t.vs_inst_idx` mp_tac) >> simp[]) >>
      metis_tac[]) >>
  gvs[ricf_live_stack_agree_def, merge_callee_state_def]
QED

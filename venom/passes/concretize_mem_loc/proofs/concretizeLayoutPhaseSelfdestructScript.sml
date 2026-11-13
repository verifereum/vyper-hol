Theory concretizeLayoutPhaseSelfdestruct
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutHaltExit
  concretizeLayoutLocalSelfdestruct concretizeLayoutSupplement
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameRelocationLocal frameRelocationEnvironment ptrDiscipline
  venomExecSemantics venomState venomInst list pred_set

(* Storage masks do not move when balances are transferred.  The existing
   account theorem covers both beneficiary=self and beneficiary<>self. *)
Theorem concretize_selfdestruct_supplement:
  inst.inst_opcode = SELFDESTRUCT /\ relocation_env s t /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  concretize_supplement D tn s t /\
  step_inst_base inst s = Halt post /\ step_inst_base inst t = Halt tpost ==>
  concretize_supplement D (step_taint inst s post tn) post tpost
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[eval_operands_def] >>
  `eval_operand addr_op t = SOME addr` by metis_tac[MEM] >>
  qpat_x_assum `step_inst_base inst t = Halt tpost` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  qpat_assum `inst.inst_opcode = SELFDESTRUCT`
    (fn th => pure_rewrite_tac[th, venomInstTheory.opcode_case_def]) >>
  fs[relocation_env_def] >> strip_tac >> gvs[] >>
  gvs[concretize_supplement_def, halt_state_def, set_returndata_def,
    step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  drule accounts_agree_except_selfdestruct_eip6780 >> simp[]
QED


Theorem layout_selfdestruct_halt:
  ptr_discipline lo C vs0 /\ taint_within D C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SELFDESTRUCT /\ active_inst fn inst s /\
  step_inst_base inst s = Halt post ==>
  ?tpost. step_inst_base inst t = Halt tpost /\
    dead_result_rel D (Halt post) (Halt tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `resolved_config_ok g.lop_config g.lop_ids g.lop_anns` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    metis_tac[GEN_ALL selfdestruct_operands] >>
  `?post'. step_inst_base inst t = Halt post' /\
    concretize_local_obs post post'` by
    metis_tac[GEN_ALL (REWRITE_RULE[GSYM concretize_local_obs_def, ETA_AX]
      (Q.INST [`D` |-> `<| d_stor := K (K UNIV); d_trans := K (K UNIV);
        d_imm := K UNIV; d_ret := K {} |>`]
        (SPEC_ALL concretize_selfdestruct_complete)))] >>
  `final_taint vs0 C post (step_taint inst s post tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >>
     qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `0`] >>
     simp[step_inst_non_invoke]) >>
  `concretize_supplement D (step_taint inst s post tn) post post'` by
    metis_tac[GEN_ALL concretize_selfdestruct_supplement] >>
  qexists `post'` >> simp[] >>
  irule concretize_supplement_halt_exit >>
  fs[concretize_local_obs_def, dead_result_rel_def] >>
  qexistsl [`C`, `ret_taint tn inst s`, `step_taint inst s post tn`, `vs0`] >>
  simp[ret_taint_def]
QED

val _ = export_theory();

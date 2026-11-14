(* Successful target internal returns reconstruct actual source executions. *)
Theory lowerDloadReturnReconstruction
Ancestors
  lowerDloadReturnInterfaceProbe lowerDloadReturnInterior
  lowerDloadReturnTerminating lowerDloadReturnInvoke lowerDloadReturnInvokePush
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_concrete_packages_static:
  (!fuel ctx inst s z. step_inst fuel ctx inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_S ^ld_covered_ambient_static ^ld_probe_point ^ld_probe_terminal
      fuel ctx inst s z) /\
  (!fuel ctx bb s z. run_block_non_phis fuel ctx bb s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_E ^ld_covered_ambient_static ^ld_probe_point ^ld_probe_terminal
      fuel ctx bb s z) /\
  (!fuel ctx fn s z. run_blocks fuel ctx fn s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_R ^ld_covered_ambient_static ^ld_probe_point ^ld_probe_terminal
      fuel ctx fn s z)
Proof
  match_mp_tac (CONV_RULE
    (RATOR_CONV (RATOR_CONV BETA_CONV) THENC
     RATOR_CONV BETA_CONV THENC BETA_CONV)
    (ISPECL [``^ld_covered_ambient_static``, ``^ld_probe_point``, ``^ld_probe_terminal``]
      ld_return_package_induction)) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (irule ld_return_terminating_S_static >> simp[]) >>
      irule ld_return_nonterminal_S_static >> simp[]) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC ld_return_invoke_S_static
QED

Theorem ld_invoke_return_reconstruction_static:
  ^ld_covered_ambient_static lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel C' calleeT ct = IntRet rt u ==>
  ?callee argsS cs fc.
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    ^ld_probe_terminal lo P C C' vs0
      (<|cf_fn := fn; cf_inst := inst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      callee cs (f::fs) fc A Sigma names rt u
Proof
  strip_tac >> drule_all ld_invoke_guarded_push_static >> strip_tac >>
  qexistsl_tac [`callee`, `argsS`, `cs`, `fc`] >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  irule ld_probe_run_return >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  MATCH_ACCEPT_TAC (cj 3 ld_return_concrete_packages_static)
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "return reconstruction has kernel hypotheses")
  [ld_return_concrete_packages_static, ld_invoke_return_reconstruction_static];

Theorem ld_return_concrete_packages:
  (!fuel ctx inst s z. step_inst fuel ctx inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_S ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
      fuel ctx inst s z) /\
  (!fuel ctx bb s z. run_block_non_phis fuel ctx bb s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_E ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
      fuel ctx bb s z) /\
  (!fuel ctx fn s z. run_blocks fuel ctx fn s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_R ^ld_covered_ambient ^ld_probe_point ^ld_probe_terminal
      fuel ctx fn s z)
Proof
  rpt conj_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (drule_all (cj 1 ld_return_concrete_packages_static) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_tac >>
      rpt gen_tac >> disch_tac >>
      disch_then (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE [o1PassContractTheory.o1_run_state_ok_def]) >>
      first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (drule_all (cj 2 ld_return_concrete_packages_static) >>
      CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_tac >>
      rpt gen_tac >> disch_tac >>
      disch_then (map_every assume_tac o CONJUNCTS o
        REWRITE_RULE [o1PassContractTheory.o1_run_state_ok_def]) >>
      first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all (cj 3 ld_return_concrete_packages_static) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> disch_tac >>
  rpt gen_tac >> disch_tac >>
  disch_then (map_every assume_tac o CONJUNCTS o
    REWRITE_RULE [o1PassContractTheory.o1_run_state_ok_def]) >>
  first_x_assum irule >> rpt conj_tac >> simp[] >>
  qpat_x_assum `!k bb tp. _` mp_tac >> simp[]
QED

Theorem ld_invoke_return_reconstruction:
  ^ld_covered_ambient lo C C' vs0 Sigma names fn fn' /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME calleeT /\
  eval_operands ops t = SOME argsT /\
  setup_callee calleeT argsT t = SOME ct /\
  run_blocks fuel C' calleeT ct = IntRet rt u ==>
  ?callee argsS cs fc.
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops s = SOME argsS /\ setup_callee callee argsS s = SOME cs /\
    fc = <|lf_serial := N; lf_supply := Sigma nm; lf_fn := callee;
      lf_src := cs; lf_tgt := ct; lf_H := FEMPTY;
      lf_Q := MAP (op_prov f.lf_H) ops; lf_E := {}; lf_tv := FEMPTY|> /\
    ^ld_probe_terminal lo P C C' vs0
      (<|cf_fn := fn; cf_inst := inst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      callee cs (f::fs) fc A Sigma names rt u
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE o
    REWRITE_RULE [o1PassContractTheory.o1_run_state_ok_def]) >>
  mp_tac (BETA_RULE ld_invoke_return_reconstruction_static) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

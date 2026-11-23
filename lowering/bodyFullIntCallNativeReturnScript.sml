(* The complete native child trace of the same setup has the same ordered
   GAS sites as the completed child certificate, at any successful fuel. *)
Theory bodyFullIntCallNativeReturn
Ancestors
  entryCreateBodyCut gasFocusVisitSiteProjection fragGasOriginPtrInvoke
  gasEventsFuel contextCodegenRel venomExecSemantics venomState list

Theorem intcall_completed_child_native:
  enters_block callee setup entered /\
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,pg)
    (entered,G,tn) marks (IntRet ir cs,Gc,tc) /\
  run_blocks fuel ctx callee setup = IntRet ret chosen ==>
  ret = ir /\ chosen = cs /\
  marks = create_cut_marks explicit (trace_blocks p d fuel ctx callee setup)
Proof
  strip_tac >>
  `exit_result (IntRet ir cs)` by simp[fragExecTheory.exit_result_def] >>
  drule_all setup_terminal_certificate >> strip_tac >>
  `run_blocks fuel' ctx callee setup = run_blocks fuel ctx callee setup /\
   gas_events_blocks fuel' ctx callee setup = gas_events_blocks fuel ctx callee setup` by
    (Cases_on `fuel' <= fuel`
     >- (qspecl_then [`fuel'`,`ctx`,`callee`,`setup`,`fuel`] mp_tac
          (cj 3 gas_events_fuel_extension) >> simp[]) >>
     `fuel <= fuel'` by decide_tac >>
     qspecl_then [`fuel`,`ctx`,`callee`,`setup`,`fuel'`] mp_tac
       (cj 3 gas_events_fuel_extension) >> simp[]) >>
  fs[] >>
  qspecl_then [`p`,`d`,`fuel`,`ctx`,`callee`,`setup`] mp_tac
    (cj 3 focus_visit_site_projection) >>
  disch_then (SUBST1_TAC o SYM) >>
  simp[create_cut_marks_def, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

(* Checked consumer side of the successful-return interface.
   This theory does not reconstruct a source callee execution. *)
Theory lowerDloadReturnInterfaceProbe
Ancestors
  lowerDloadSafetyRunInduction lowerDloadSafetyAmbient
  lowerDloadSafetyRelation venomExecSemantics venomState venomInst list
Libs
  lowerDloadReturnPackageLib

Theorem ld_invoke_from_return:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  run_blocks sf C fn cs = IntRet rs cs' /\
  rs.iret_values = rt.iret_values /\
  bind_outputs inst.inst_outputs rt.iret_values target = SOME target' ==>
  ?s'. bind_outputs inst.inst_outputs rs.iret_values
         (adopt_return_fmp rs (merge_callee_state s cs')) = SOME s' /\
       step_inst sf C inst s = OK s'
Proof
  strip_tac >>
  `LENGTH inst.inst_outputs = LENGTH rs.iret_values` by
    gvs[bind_outputs_def, AllCaseEqs()] >>
  `?s'. bind_outputs inst.inst_outputs rs.iret_values
         (adopt_return_fmp rs (merge_callee_state s cs')) = SOME s'` by
    simp[bind_outputs_def] >>
  qexists `s'` >> simp[] >> once_rewrite_tac[step_inst_def] >> simp[]
QED

val _ = if null (hyp ld_invoke_from_return) then ()
        else raise Fail "invoke consumer has hypotheses";


(* General capability projections isolate composition from semantic producers. *)
Theorem ld_probe_entry_body:
  ^ld_probe_entry C' fn' Point q /\
  lookup_block q.vs_current_bb fn'.fn_blocks = SOME bb /\
  eval_phis q bb.bb_instructions = OK tp /\
  run_block_non_phis k C' bb
    (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = z /\
  ((?u. z = OK u) \/ (?rt u. z = IntRet rt u)) ==>
  Point bb (tp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  simp[] >> metis_tac[]
QED

Theorem ld_probe_terminal_invoke:
  ^ld_probe_terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  bind_outputs inst.inst_outputs rt.iret_values target = SOME target' ==>
  ?sf s'. step_inst sf C inst s = OK s'
Proof
  simp[] >> strip_tac >> drule_all ld_invoke_from_return >>
  metis_tac[]
QED


(* Predicate-parametric composition is proved once; concrete schemas below
   are specializations, not independent induction proofs. *)
Theorem ld_return_package_induction:
  !Ambient Point Terminal. ^ld_package_induction Ambient Point Terminal
Proof
  rpt gen_tac >>
  CONV_TAC (RATOR_CONV (RATOR_CONV BETA_CONV) THENC
            RATOR_CONV BETA_CONV THENC BETA_CONV) >> strip_tac >>
  match_mp_tac (ISPECL
    [``^ld_probe_S Ambient Point Terminal``,
     ``^ld_probe_E Ambient Point Terminal``,
     ``^ld_probe_R Ambient Point Terminal``] ld_successful_run_induction) >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (ntac 2 (pop_assum kall_tac) >> suspend "next")
  >- (ntac 2 (pop_assum kall_tac) >> suspend "term")
  >- (ntac 2 (pop_assum kall_tac) >> suspend "ret")
  >- (ntac 2 (pop_assum kall_tac) >> suspend "jump")
  >> ntac 2 (pop_assum kall_tac) >> suspend "return"
QED

Resume ld_return_package_induction[next]:
  rpt gen_tac >> strip_tac >> gvs[] >> rpt strip_tac >>
  metis_tac[]
QED
Resume ld_return_package_induction[term]:
  rpt gen_tac >> strip_tac >> gvs[] >> rpt strip_tac >> metis_tac[]
QED
Resume ld_return_package_induction[ret]:
  rpt gen_tac >> strip_tac >> gvs[] >> rpt strip_tac >> metis_tac[]
QED
Resume ld_return_package_induction[jump]:
  rpt gen_tac >> strip_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> rpt strip_tac >> metis_tac[]
QED
Resume ld_return_package_induction[return]:
  rpt gen_tac >> strip_tac >> gvs[] >> rpt strip_tac >> metis_tac[]
QED
Finalise ld_return_package_induction

(* Preserve the checked experimental specialization, beta-equivalent to its
   original statement. Production has a separate covered-supply ambient. *)
Theorem ld_probe_conditional_induction:
  !Ambient Point Terminal.
  Ambient = ^ld_probe_ambient /\ Point = ^ld_probe_point /\
  Terminal = ^ld_probe_terminal ==>
  ^ld_package_induction Ambient Point Terminal
Proof
  rpt gen_tac >> disch_then kall_tac >>
  MATCH_ACCEPT_TAC ld_return_package_induction
QED

(* The third semantic producer is Entry at the actual setup state q.
   This projection does not derive it from setup or from target success. *)
Theorem ld_probe_run_return:
  (!fuel ctx fnT q z. run_blocks fuel ctx fnT q = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    ^ld_probe_R Ambient Point Terminal fuel ctx fnT q z) /\
  Ambient lo C C' vs0 Sigma names fn fn' /\
  ^ld_probe_entry C' fn'
    (Point lo P C C' vs0 stk fn fn' cs fs f0 A0 Sigma names) q /\
  run_blocks fuel C' fn' q = IntRet rt u ==>
  Terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
Proof
  simp[] >> strip_tac >>
  qpat_x_assum `!fuel ctx fnT q. _`
    (qspecl_then [`fuel`, `C'`, `fn'`, `q`] mp_tac) >> simp[] >>
  disch_then irule >> simp[] >> first_assum ACCEPT_TAC
QED

val _ = List.app (fn th => if null (hyp th) then ()
             else raise Fail "return interface probe has kernel hypotheses")
  [ld_probe_entry_body, ld_probe_terminal_invoke,
   ld_probe_conditional_induction, ld_probe_run_return];

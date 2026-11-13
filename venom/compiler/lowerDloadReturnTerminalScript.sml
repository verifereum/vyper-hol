(* Conditional terminal packaging: return effects are explicit premises. *)
Theory lowerDloadReturnTerminal
Ancestors
  lowerDloadSafetyAmbient lowerDloadReturnAlignment lowerDloadSafetyKernel
  lowerDloadSafetyRelation finite_map list
Libs
  lowerDloadReturnPackageLib

Theorem ld_return_terminal_package:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  ^ld_probe_stable lo P Sigma names fs f0 A0 A frames /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ inst.inst_opcode = RET /\
  step_inst 0 C inst s = IntRet rs e /\
  step_inst 0 C' inst t = IntRet rt u /\
  rs.iret_values = rt.iret_values /\
  rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
  ld_memory lo A tn e u /\ ld_nonghost tn e u /\
  ld_return_cont C fn cs s ==>
  ^ld_probe_terminal lo P C C' vs0 stk fn cs fs f0 A0 Sigma names rt u
Proof
  strip_tac >>
  `ld_return_suffix C fn s rs e` by
    (irule ld_return_suffix_terminal >> metis_tac[]) >>
  `?sf. run_blocks sf C fn cs = IntRet rs e` by
    fs[ld_return_cont_def] >>
  simp[NoAsms] >>
  qexistsl_tac [`sf`,`rs`,`e`,`A`,`frames`,`tn`,`inst`,`s`,`t`,`PG`,`G`,`N`] >>
  asm_rewrite_tac[] >> simp[FLOOKUP_DRESTRICT] >>
  qpat_x_assum `^ld_probe_stable _ _ _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]
QED

val _ = if null (hyp ld_return_terminal_package) then ()
        else raise Fail "ld_return_terminal_package has hypotheses";

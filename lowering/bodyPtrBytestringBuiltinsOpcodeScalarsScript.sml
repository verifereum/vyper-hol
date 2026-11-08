Theory bodyPtrBytestringBuiltinsOpcodeScalars
Ancestors bodyPtrBytestringBuiltinsOpcodeSimple
          bodyPtrBytestringBuiltinsOpcodeValues bodyPtrBytestringBuiltinsOpcodeState
          exprLowering exprBopLowering

Theorem no_extcode_invert:
  !v ty ce s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_invert v ty ce s))
Proof
  rpt strip_tac >> Cases_on `ty` >> simp[compile_invert_def, no_extcode_emit_op]
QED

Theorem no_extcode_neg:
  !v ty s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_neg v ty s))
Proof
  rpt strip_tac >> simp[compile_neg_def] >> pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void])
QED

Theorem no_extcode_env_var:
  !item s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_env_var item s))
Proof
  Cases >> simp[compile_env_var_def, no_extcode_emit_op] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op])
QED

Theorem no_extcode_acc:
  (!s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce (BaseT AddressT) e s))) ==>
  !item s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_acc cfn ce e item s))
Proof
  strip_tac >>
  `!s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_value cfn ce (BaseT AddressT) e s))` by
    (simp[no_extcode_lower_value]) >>
  Cases >> rpt strip_tac >> simp[compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (qpat_x_assum `!s. compiler_no_extcode s ==> compiler_no_extcode (SND (lower_value _ _ _ _ s))`
    (qspec_then `s` mp_tac) >> simp[] >> strip_tac) >>
  simp[no_extcode_emit_op] >>
  TRY (rename1 `emit_op EXTCODESIZE ops st1 = (cs_op,st2)` >>
    mp_tac (Q.INST [`opc` |-> `EXTCODESIZE`, `ops` |-> `ops`,
      `s` |-> `st1`] no_extcode_emit_op) >> simp[] >> strip_tac >>
    simp[no_extcode_emit_op] >> NO_TAC) >>
  rename1 `emit_inst INVALID ops outs s = (u,t)` >>
  mp_tac (Q.INST [`opc` |-> `INVALID`, `ops` |-> `ops`,
    `outs` |-> `outs`] no_extcode_emit_inst) >> simp[]
QED

Theorem no_extcode_addmod_names:
  !ce rt at a bt b mt m s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_addmod_names ce rt at a bt b mt m s))
Proof
  rpt strip_tac >> simp[compile_addmod_names_def, as_stack_val_pair] >>
  rpt (pairarg_tac >> gvs[]) >>
  `compiler_no_extcode st1` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st2` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  `compiler_no_extcode st3` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st4` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  `compiler_no_extcode st5` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st6` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  simp[no_extcode_addmod]
QED

Theorem no_extcode_mulmod_names:
  !ce rt at a bt b mt m s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_mulmod_names ce rt at a bt b mt m s))
Proof
  rpt strip_tac >> simp[compile_mulmod_names_def, as_stack_val_pair] >>
  rpt (pairarg_tac >> gvs[]) >>
  `compiler_no_extcode st1` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st2` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  `compiler_no_extcode st3` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st4` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  `compiler_no_extcode st5` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st6` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  simp[no_extcode_mulmod]
QED

Theorem no_extcode_powmod256_names:
  !ce rt at a bt b s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_powmod256_names ce rt at a bt b s))
Proof
  rpt strip_tac >> simp[compile_powmod256_names_def, as_stack_val_pair] >>
  rpt (pairarg_tac >> gvs[]) >>
  `compiler_no_extcode st1` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st2` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  `compiler_no_extcode st3` by metis_tac[no_extcode_name_vv, pairTheory.SND] >>
  `compiler_no_extcode st4` by metis_tac[no_extcode_unwrap_value, pairTheory.SND] >>
  simp[no_extcode_pow_mod256]
QED

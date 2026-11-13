Theory dftGasInvContextConvert
Ancestors
  dftGasOracleDefs dftRunRel venomExecSemantics venomInst venomState list

Theorem inv_ev_step_context_convert:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!fn fn' p d s vals t.
    dft_fn_rel fn fn' /\
    ev_blocks orc p d fuel C' fn' s = IntRet vals t ==>
    ev_blocks orc p d fuel C fn s = IntRet vals t) ==>
  !p d inst s r t vals.
    (r = OK t \/ r = IntRet vals t) /\
    ev_step orc p d fuel C' inst s = r ==>
    ev_step orc p d fuel C inst s = r
Proof
  strip_tac >> rpt gen_tac >>
  Cases_on `inst.inst_opcode = GAS` >- simp[ev_step_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >- (
    simp[ev_step_def] >> strip_tac >> gvs[AllCaseEqs()] >>
    rename1 `lookup_function name C'.ctx_functions = SOME callee'` >>
    `?callee. lookup_function name C.ctx_functions = SOME callee /\
       dft_fn_rel callee callee'` by
      (drule dft_fn_rel_lookup_function >>
       disch_then (qspec_then `name` mp_tac) >>
       Cases_on `lookup_function name C.ctx_functions` >> gvs[]) >>
    `setup_callee callee' args s = setup_callee callee args s` by
      metis_tac[dft_fn_rel_setup_callee] >>
    first_x_assum drule_all >> strip_tac >> gvs[]) >>
  simp[ev_step_def]
QED

Theorem inv_block_success_steps[local]:
  (!inst s r t vals.
     (r = OK t \/ r = IntRet vals t) /\
     ev_step orc p d fuel C' inst s = r ==>
     ev_step orc p d fuel C inst s = r) ==>
  !n s r t vals.
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    (r = OK t \/ r = IntRet vals t) /\
    ev_block orc p d fuel C' bb s = r ==>
    ev_block orc p d fuel C bb s = r
Proof
  strip_tac >> completeInduct_on `n` >> rpt gen_tac >>
  disch_then strip_assume_tac >> (
  qpat_x_assum `ev_block _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[ev_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `ev_step orc p d fuel C' inst s` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  (impl_tac >- (gvs[get_instruction_def] >> decide_tac)) >>
  disch_then (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> metis_tac[])
QED

Theorem inv_ev_block_context_convert:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (!fn fn' p d s vals t.
    dft_fn_rel fn fn' /\
    ev_blocks orc p d fuel C' fn' s = IntRet vals t ==>
    ev_blocks orc p d fuel C fn s = IntRet vals t) ==>
  !p d bb s r t vals.
    (r = OK t \/ r = IntRet vals t) /\
    ev_block orc p d fuel C' bb s = r ==>
    ev_block orc p d fuel C bb s = r
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> (
  irule inv_block_success_steps >>
  simp[] >> qexists_tac `C'` >> simp[] >>
  metis_tac[inv_ev_step_context_convert])
QED

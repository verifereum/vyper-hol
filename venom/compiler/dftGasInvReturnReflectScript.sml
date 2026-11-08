Theory dftGasInvReturnReflect
Ancestors
  dftGasInvBlockInit dftGasInvContextConvert dftGasOracleDefs dftRunRel
  venomExecSemantics venomInst venomState list

Theorem inv_ev_blocks_return_reflect:
  !fuel fn fn' p d s vals t.
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  dft_fn_rel fn fn' /\
  ev_blocks orc p d fuel C' fn' s = IntRet vals t ==>
  ev_blocks orc p d fuel C fn s = IntRet vals t
Proof
  Induct >- simp[Once ev_blocks_def] >> rpt gen_tac >> strip_tac >>
  `!fn fn' p d s vals t.
    dft_fn_rel fn fn' /\
    ev_blocks orc p d fuel C' fn' s = IntRet vals t ==>
    ev_blocks orc p d fuel C fn s = IntRet vals t` by metis_tac[] >>
  qpat_x_assum `ev_blocks _ _ _ _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE[ev_blocks_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  rename1 `lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb'` >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        dft_block_rel bb bb'` by
    (`LIST_REL dft_block_rel fn.fn_blocks fn'.fn_blocks` by gvs[dft_fn_rel_def] >>
     drule dft_block_rel_lookup_block >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  drule_all inv_lookup_phis >> strip_tac >>
  qspecl_then [`s`, `bb'.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  gvs[] >> (
  drule_at (Pat `ev_block _ _ _ _ _ _ _ = _`) inv_ev_block_context_convert >>
  disch_then (qspec_then `C` mp_tac) >> simp[] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  drule_at (Pat `ev_block _ _ _ _ _ _ _ = _`) inv_lookup_block_init_reflect >>
  simp[] >>
  disch_then (qspecl_then [`s.vs_current_bb`, `fn'`, `fn`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[ev_blocks_def] >> simp[] >> metis_tac[])
QED

Theorem inv_ev_step_success_reflect:
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  (r = OK t \/ r = IntRet vals t) /\
  ev_step orc p d fuel C' inst s = r ==>
  ev_step orc p d fuel C inst s = r
Proof
  strip_tac >> (
  drule_at (Pat `ev_step _ _ _ _ _ _ _ = _`) inv_ev_step_context_convert >>
  disch_then (qspec_then `C` mp_tac) >> simp[] >>
  disch_then irule >> metis_tac[inv_ev_blocks_return_reflect])
QED

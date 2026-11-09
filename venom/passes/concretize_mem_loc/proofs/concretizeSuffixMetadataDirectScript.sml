Theory concretizeSuffixMetadataDirect
Ancestors
  fmpLowerDefs makeSsaDefs singleUseExpansionDefs dftDefs venomInst

Theorem fmp_checked_seal_mems_used[local]:
  fmp_checked_seal ctx fn info blocks = SOME out ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[fmp_checked_seal_def, fmp_seal_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem fmp_lower_function_mems_used:
  fmp_lower_function ctx s fn = SOME (out,s') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[fmp_checked_seal_mems_used]
QED

Theorem make_ssa_current_fn_mems_used:
  make_ssa_current_fn s fn = (out,s') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[make_ssa_current_fn_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]
QED

Theorem sue_expand_function_supply_mems_used:
  sue_expand_function_supply s fn = (out,s') ==>
  out.fn_mems_used = fn.fn_mems_used
Proof
  simp[sue_expand_function_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem dft_fn_mems_used:
  (dft_fn fn).fn_mems_used = fn.fn_mems_used
Proof
  simp[dft_fn_def] >> pairarg_tac >> simp[]
QED

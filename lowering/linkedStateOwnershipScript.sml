(* Combine ownership of the main and exported entry closures. *)
Theory linkedStateOwnership
Ancestors
  vyperTypeContract vyperTypeCallGraphSoundness list pair

Theorem check_contract_linked_state_ownership:
  check_contract in_deploy layouts addr mods = SOME art /\
  exports_ok layouts addr mods exps ==>
  check_linked_state_ownership layouts addr mods (linked_live_functions mods exps)
Proof
  strip_tac >>
  `check_linked_state_ownership layouts addr mods
     (linked_live_functions_from mods (linked_main_roots mods))` by
    fs[check_contract_def] >>
  `check_linked_state_ownership layouts addr mods
     (linked_live_functions_from mods (linked_export_roots exps))` by
    fs[exports_ok_def] >>
  Cases_on `(case mods of [(NONE,_)] => T | _ => F)` >>
  gvs[check_linked_state_ownership_def,
      EVERY_MEM, FORALL_PROD] >>
  qx_genl_tac [`src`, `tops`] >> strip_tac >>
  qx_gen_tac `tl` >> strip_tac >>
  ntac 2 (qpat_x_assum `!s ts. MEM (s,ts) mods ==> _`
    (qspecl_then [`src`, `tops`]
      (fn th => mp_tac (th |> UNDISCH |> Q.SPEC `tl` |> UNDISCH)))) >>
  Cases_on `tl` >> simp[linked_live_functions_member, DISJ_IMP_THM] >>
  rpt CASE_TAC >> simp[DISJ_IMP_THM]
QED

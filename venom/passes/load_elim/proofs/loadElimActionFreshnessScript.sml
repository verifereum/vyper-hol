Theory loadElimActionFreshness
Ancestors
  loadElimDefs loadElimOriginHelpers venomWf list rich_list
  ASCIInumbers string pred_set

Theorem le_fresh_phi_var_inj[simp]:
  fresh_phi_var n = fresh_phi_var m <=> n = m
Proof
  simp[fresh_phi_var_def, STRCAT_toString_inj]
QED

Theorem le_collected_action_output_prefix:
  MEM pa (collect_phi_actions m ctx cfg result fn) ==>
  isPREFIX "$le_phi_" pa.pa_phi_out
Proof
  strip_tac >> drule collect_phi_actions_member >> strip_tac >>
  drule compute_phi_action_origin >> simp[fresh_phi_var_def]
QED

Theorem le_collected_action_source_disjoint:
  EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
  MEM pa (collect_phi_actions m ctx cfg result fn) ==>
  ~MEM pa.pa_phi_out (fn_all_vars fn)
Proof
  strip_tac >> drule le_collected_action_output_prefix >> strip_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  pure_rewrite_tac[EVERY_MEM] >> BETA_TAC >> metis_tac[]
QED

Theorem le_optional_mapi_output_sublist:
  !xs f. (!i x. f i x = [] \/ MAP out (f i x) = [g x]) ==>
  sublist (MAP out (FLAT (MAPi f xs))) (MAP g xs)
Proof
  Induct >- simp[sublist_def] >> rpt gen_tac >> strip_tac >>
  `sublist (MAP out (FLAT (MAPi (f o SUC) xs))) (MAP g xs)` by
    (first_x_assum irule >> gvs[combinTheory.o_DEF]) >>
  qpat_x_assum `!f'. (!i x. _) ==> _` kall_tac >>
  qpat_x_assum `!i x. _` (qspecl_then [`0`, `h`] strip_assume_tac) >>
  fs[indexedListsTheory.MAPi_def, combinTheory.o_DEF] >>
  metis_tac[sublist_cons, sublist_cons_include]
QED

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

Theorem le_optional_blocks_output_sublist:
  !bs. (!b i x. f b i x = [] \/ MAP out (f b i x) = [g x]) ==>
  sublist (MAP out (FLAT (MAP (\b. FLAT (MAPi (f b) (insts b))) bs)))
          (FLAT (MAP (\b. MAP g (insts b)) bs))
Proof
  Induct >- simp[sublist_def] >> rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[MAP, FLAT, MAP_APPEND] >> BETA_TAC >>
  irule sublist_append_pair >> conj_tac
  >- (irule le_optional_mapi_output_sublist >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem le_collected_action_output_sublist:
  sublist (MAP (\pa. pa.pa_phi_out) (collect_phi_actions m ctx cfg result fn))
    (FLAT (MAP (\bb. MAP (\inst. fresh_phi_var inst.inst_id)
                            bb.bb_instructions) fn.fn_blocks))
Proof
  pure_rewrite_tac[collect_phi_actions_def, LET_THM] >>
  BETA_TAC >> ho_match_mp_tac le_optional_blocks_output_sublist >>
  rpt gen_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  drule compute_phi_action_origin >> simp[]
QED

Theorem le_collected_action_outputs_distinct:
  wf_function fn ==>
  ALL_DISTINCT (MAP (\pa. pa.pa_phi_out) (collect_phi_actions m ctx cfg result fn))
Proof
  strip_tac >>
  irule sublist_ALL_DISTINCT >>
  irule_at Any le_collected_action_output_sublist >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
                                    bb.bb_instructions) fn.fn_blocks))` by
    gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  `ALL_DISTINCT (MAP fresh_phi_var
     (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)))` by
    (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  fs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

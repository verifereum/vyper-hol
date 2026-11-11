(* TOP-LEVEL: a well-founded compiler type-dependency relation satisfies
   the existing computable acyclicity guard. No source whitelist is used. *)
Theory copyAcyclicProps
Ancestors
  copyRankAgreement typedCopyDomain compileEnv vyperAST
  finite_map relation list pair combin arithmetic

Theorem copy_wf_no_return:
  !R child parent. WF R /\ R child parent ==> ~RTC R parent child
Proof
  rpt gen_tac >> strip_tac >> DISCH_TAC >>
  qpat_x_assum `RTC _ _ _` (mp_tac o REWRITE_RULE [RTC_CASES_TC]) >> strip_tac
  >- (gvs[] >> drule_all WF_NOT_REFL >> simp[]) >>
  `TC R parent parent` by (drule_all TC_RIGHT1_I >> simp[]) >>
  drule_all WF_noloops >> simp[]
QED

Theorem copy_wf_deleted_parent_agrees:
  !sf nsid child.
    WF (type_copy_child sf) /\ type_copy_child sf child (StructT nsid) ==>
    copy_metadata_agrees sf (sf \\ nsid_to_string nsid) child
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [copy_metadata_agrees_def] >>
  qx_gen_tac `other_nsid` >> DISCH_TAC >>
  Cases_on `nsid_to_string other_nsid = nsid_to_string nsid`
  >- (`type_copy_child sf child (StructT other_nsid)` by gvs[type_copy_child_def] >>
      mp_tac (Q.ISPECL [`type_copy_child sf`, `(child:type)`, `StructT other_nsid`]
        copy_wf_no_return) >> simp[]) >>
  simp[get_struct_fields_delete]
QED

Theorem copy_wf_rank_struct_equation:
  !sf nsid. WF (type_copy_child sf) ==>
    type_rank sf (StructT nsid) =
      1 + SUM (MAP (type_rank sf o FST o SND) (get_struct_fields sf (nsid_to_string nsid)))
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [type_rank_def, LET_THM] >>
  AP_TERM_TAC >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `type_rank _ (FST (SND field_entry)) = _` >>
  irule type_rank_metadata_agrees >> irule copy_wf_deleted_parent_agrees >>
  simp[type_copy_child_def, MEM_MAP] >> qexists_tac `field_entry` >> simp[]
QED

Theorem wf_type_copy_child_acyclic:
  !sf. WF (type_copy_child sf) ==> acyclic_struct_metadata sf
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [acyclic_struct_metadata_def, FEVERY_DEF] >>
  rpt strip_tac >> rename1 `name IN FDOM sf` >>
  mp_tac (Q.SPECL [`sf`, `(NONE,name)`] copy_wf_rank_struct_equation) >>
  simp[nsid_to_string_def, get_struct_fields_def, FLOOKUP_DEF]
QED

(* TOP-LEVEL: compiler type ranks depend only on metadata reachable from
   their starting type. The statement also applies to cyclic metadata. *)
Theory copyRankAgreement
Ancestors
  typedCopyDomain compileEnv vyperAST finite_map relation list pair combin arithmetic

Definition copy_metadata_agrees_def:
  copy_metadata_agrees sf sub ty <=>
    !nsid. RTC (type_copy_child sf) (StructT nsid) ty ==>
      get_struct_fields sub (nsid_to_string nsid) = get_struct_fields sf (nsid_to_string nsid)
End

Theorem get_struct_fields_delete:
  !sf key name. get_struct_fields (sf \\ key) name =
    if name = key then [] else get_struct_fields sf name
Proof
  rpt gen_tac >> Cases_on `name = key` >> simp[get_struct_fields_def, DOMSUB_FLOOKUP_THM]
QED

Theorem type_copy_child_delete:
  !sf key child parent.
    type_copy_child (sf \\ key) child parent ==> type_copy_child sf child parent
Proof
  rpt gen_tac >> Cases_on `parent` >> simp[type_copy_child_def] >>
  rpt strip_tac >>
  qmatch_asmsub_rename_tac `get_struct_fields (sf \\ key) (nsid_to_string nsid)` >>
  Cases_on `nsid_to_string nsid = key` >> gvs[get_struct_fields_delete]
QED

Theorem copy_descendant_delete:
  !sf key child parent.
    RTC (type_copy_child (sf \\ key)) child parent ==> RTC (type_copy_child sf) child parent
Proof
  rpt gen_tac >> match_mp_tac RTC_MONOTONE >> rpt strip_tac >>
  drule_all type_copy_child_delete >> simp[]
QED

Theorem copy_metadata_agrees_root:
  !sf sub nsid. copy_metadata_agrees sf sub (StructT nsid) ==>
    get_struct_fields sub (nsid_to_string nsid) = get_struct_fields sf (nsid_to_string nsid)
Proof
  simp[copy_metadata_agrees_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem copy_metadata_agrees_child:
  !sf sub parent child.
    copy_metadata_agrees sf sub parent /\ type_copy_child sf child parent ==>
    copy_metadata_agrees sf sub child
Proof
  simp_tac bool_ss [copy_metadata_agrees_def] >> rpt strip_tac >> first_x_assum irule >>
  irule RTC_TRANS >> qexists_tac `child` >> simp[RTC_SINGLE]
QED

Theorem copy_metadata_agrees_delete_child:
  !sf sub nsid child.
    copy_metadata_agrees sf sub (StructT nsid) /\ type_copy_child sf child (StructT nsid) ==>
    copy_metadata_agrees (sf \\ nsid_to_string nsid) (sub \\ nsid_to_string nsid) child
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [copy_metadata_agrees_def] >>
  qx_gen_tac `other_nsid` >> DISCH_TAC >>
  `RTC (type_copy_child sf) (StructT other_nsid) (StructT nsid)` by
    (irule RTC_TRANS >> qexists_tac `child` >> conj_tac
     >- (drule copy_descendant_delete >> simp[]) >> simp[RTC_SINGLE]) >>
  Cases_on `nsid_to_string other_nsid = nsid_to_string nsid` >>
  simp[get_struct_fields_delete] >>
  qpat_x_assum `copy_metadata_agrees _ _ _` (mp_tac o REWRITE_RULE [copy_metadata_agrees_def]) >>
  disch_then (qspec_then `other_nsid` mp_tac) >> simp[]
QED

Theorem copy_rank_array_case:
  !sf elem bd.
    (!sub. copy_metadata_agrees sf sub elem ==> type_rank sub elem = type_rank sf elem) ==>
    !sub. copy_metadata_agrees sf sub (ArrayT elem bd) ==>
      type_rank sub (ArrayT elem bd) = type_rank sf (ArrayT elem bd)
Proof
  rpt strip_tac >> simp_tac bool_ss [type_rank_def] >> AP_TERM_TAC >> first_x_assum irule >>
  irule copy_metadata_agrees_child >> qexists_tac `ArrayT elem bd` >> simp[type_copy_child_def]
QED

Theorem copy_rank_tuple_case:
  !sf tys.
    (!ty. MEM ty tys ==> !sub. copy_metadata_agrees sf sub ty ==>
      type_rank sub ty = type_rank sf ty) ==>
    !sub. copy_metadata_agrees sf sub (TupleT tys) ==>
      type_rank sub (TupleT tys) = type_rank sf (TupleT tys)
Proof
  rpt strip_tac >> simp_tac bool_ss [type_rank_def] >> AP_TERM_TAC >> AP_TERM_TAC >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
  irule copy_metadata_agrees_child >> qexists_tac `TupleT tys` >> simp[type_copy_child_def]
QED

Theorem copy_rank_struct_case:
  !sf nsid.
    (!name field_entry ty.
      name = nsid_to_string nsid /\ MEM field_entry (get_struct_fields sf name) /\
      ty = (FST o SND) field_entry ==>
      !sub. copy_metadata_agrees (sf \\ name) sub ty ==>
        type_rank sub ty = type_rank (sf \\ name) ty) ==>
    !sub. copy_metadata_agrees sf sub (StructT nsid) ==>
      type_rank sub (StructT nsid) = type_rank sf (StructT nsid)
Proof
  rpt strip_tac >>
  `get_struct_fields sub (nsid_to_string nsid) = get_struct_fields sf (nsid_to_string nsid)` by
    (drule copy_metadata_agrees_root >> simp[]) >>
  simp_tac bool_ss [type_rank_def, LET_THM] >> asm_rewrite_tac [] >>
  AP_TERM_TAC >> AP_TERM_TAC >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `type_rank _ (FST (SND field_entry)) = _` >>
  first_x_assum irule >> simp[MEM_MAP] >> conj_tac >- (qexists_tac `field_entry` >> simp[]) >>
  irule copy_metadata_agrees_delete_child >> simp[type_copy_child_def, MEM_MAP] >>
  qexists_tac `field_entry` >> simp[]
QED

Theorem type_rank_metadata_agrees:
  !sf ty. !sub. copy_metadata_agrees sf sub ty ==> type_rank sub ty = type_rank sf ty
Proof
  recInduct type_rank_ind >> rpt conj_tac
  >- simp[type_rank_def]
  >- MATCH_ACCEPT_TAC copy_rank_array_case
  >- MATCH_ACCEPT_TAC copy_rank_tuple_case
  >- MATCH_ACCEPT_TAC copy_rank_struct_case
  >- simp[type_rank_def]
  >> simp[type_rank_def]
QED

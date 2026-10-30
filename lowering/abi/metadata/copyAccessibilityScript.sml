(* TOP-LEVEL: source assignability makes the compiler's type-copy dependency
   tree accessible. Agreement concerns field types only, not numeric sizes. *)
Theory copyAccessibility
Ancestors
  typedCopyDomain compileEnv vyperTypeSystem vyperValue vyperAST
  finite_map relation list pair combin

Definition copy_source_agrees_def:
  copy_source_agrees sf tenv <=>
    !nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==>
      MAP (FST o SND) (get_struct_fields sf (nsid_to_string nsid)) = MAP SND args
End

Theorem copy_source_agrees_delete:
  !sf tenv key. copy_source_agrees sf tenv ==> copy_source_agrees sf (tenv \\ key)
Proof
  simp[copy_source_agrees_def, DOMSUB_FLOOKUP_THM, AllCaseEqs()] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem copy_wfp_leaves:
  (!sf bt. WFP (type_copy_child sf) (BaseT bt)) /\
  (!sf nsid. WFP (type_copy_child sf) (FlagT nsid)) /\
  (!sf. WFP (type_copy_child sf) NoneT)
Proof
  rpt conj_tac >> rpt gen_tac >> irule WFP_RULES >> simp[type_copy_child_def]
QED

Theorem copy_wfp_array:
  !sf elem bd.
    WFP (type_copy_child sf) elem ==> WFP (type_copy_child sf) (ArrayT elem bd)
Proof
  rpt strip_tac >> irule WFP_RULES >> simp[type_copy_child_def]
QED

Theorem copy_wfp_tuple:
  !sf tys.
    EVERY (WFP (type_copy_child sf)) tys ==> WFP (type_copy_child sf) (TupleT tys)
Proof
  rpt strip_tac >> irule WFP_RULES >> fs[type_copy_child_def, EVERY_MEM]
QED

Theorem copy_wfp_struct:
  !sf nsid.
    EVERY (WFP (type_copy_child sf))
      (MAP (FST o SND) (get_struct_fields sf (nsid_to_string nsid))) ==>
    WFP (type_copy_child sf) (StructT nsid)
Proof
  rpt strip_tac >> irule WFP_RULES >> fs[type_copy_child_def, EVERY_MEM]
QED

Theorem assignable_copy_tuple_case:
  !tenv tys.
    (!ty. MEM ty tys ==> assignable_type tenv ty ==>
      !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) ty) ==>
    assignable_type tenv (TupleT tys) ==>
    !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) (TupleT tys)
Proof
  rpt strip_tac >> irule copy_wfp_tuple >> fs[Once assignable_type_def, EVERY_MEM] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem assignable_copy_array_case:
  !tenv elem bd.
    (assignable_type tenv elem ==>
      !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) elem) ==>
    assignable_type tenv (ArrayT elem bd) ==>
    !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) (ArrayT elem bd)
Proof
  rpt strip_tac >> irule copy_wfp_array >> fs[Once assignable_type_def] >>
  first_x_assum irule >> simp[]
QED

Theorem assignable_copy_struct_case:
  !tenv nsid.
    (!source_args args field_entry field_ty.
      FLOOKUP tenv nsid = SOME source_args /\ source_args = StructArgs args /\
      MEM field_entry args /\ field_ty = SND field_entry ==>
      assignable_type (tenv \\ nsid) field_ty ==>
      !sf. copy_source_agrees sf (tenv \\ nsid) ==> WFP (type_copy_child sf) field_ty) ==>
    assignable_type tenv (StructT nsid) ==>
    !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) (StructT nsid)
Proof
  rpt strip_tac >> Cases_on `FLOOKUP tenv nsid` >> gvs[Once assignable_type_def] >>
  rename1 `FLOOKUP tenv nsid = SOME source_type_args` >>
  Cases_on `source_type_args` >> gvs[] >> irule copy_wfp_struct >>
  qpat_x_assum `copy_source_agrees _ _` (fn th =>
    ASSUME_TAC th >> mp_tac (REWRITE_RULE [copy_source_agrees_def] th)) >>
  disch_then drule >> DISCH_TAC >> asm_rewrite_tac [] >>
  fs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
  first_x_assum irule >> simp[copy_source_agrees_delete]
QED

Theorem assignable_type_copy_accessible:
  !tenv ty. assignable_type tenv ty ==>
    !sf. copy_source_agrees sf tenv ==> WFP (type_copy_child sf) ty
Proof
  ho_match_mp_tac assignable_type_ind >> rpt conj_tac
  >- simp[copy_wfp_leaves]
  >- MATCH_ACCEPT_TAC assignable_copy_tuple_case
  >- MATCH_ACCEPT_TAC assignable_copy_array_case
  >- MATCH_ACCEPT_TAC assignable_copy_struct_case
  >- simp[copy_wfp_leaves]
  >> gvs[assignable_type_def]
QED

Theorem copy_fields_accessible_well_founded:
  !sf. (!name. EVERY (WFP (type_copy_child sf))
      (MAP (FST o SND) (get_struct_fields sf name))) ==>
    WF (type_copy_child sf)
Proof
  gen_tac >> DISCH_TAC >>
  `(!ty. WFP (type_copy_child sf) ty) /\
   (!tys. EVERY (WFP (type_copy_child sf)) tys)` suffices_by simp[WF_EQ_WFP] >>
  ho_match_mp_tac (TypeBase.induction_of ``:type``) >>
  simp[copy_wfp_leaves, copy_wfp_array, copy_wfp_tuple, copy_wfp_struct]
QED

(* Allocation-only two-arena frame, used by purity. Unlike length monotonicity,
   this records that existing cells and all non-arena fields are unchanged. *)
Theory vyperAbiAppendFrame
Ancestors
  list rich_list pair vyperState vyperAbiOperand vyperAbiReadOnly
  vyperStatePreservation
  vyperCallOutcomeFrame

Definition abi_append_def:
  abi_append st rt <=> ?suffix imm_suffix. rt = st with <|
    abi_memory := st.abi_memory ++ suffix;
    abi_immutables := st.abi_immutables ++ imm_suffix |>
End

Theorem abi_append_refl[simp]:
  abi_append st st
Proof
  simp[abi_append_def] >> qexistsl_tac [`[]`,`[]`] >> simp[]
QED

Theorem abi_append_trans:
  abi_append st mid /\ abi_append mid rt ==> abi_append st rt
Proof
  rw[abi_append_def] >>
  qexistsl_tac [`suffix ++ suffix'`,`imm_suffix ++ imm_suffix'`] >>
  simp[APPEND_ASSOC, evaluation_state_component_equality]
QED

Theorem abi_append_readonly:
  abi_readonly f ==> state_rel_frame abi_append f
Proof
  simp[state_rel_frame_def, abi_readonly_def]
QED

Theorem capture_abi_memory_append:
  state_rel_frame abi_append (capture_abi_memory cx id tv v)
Proof
  simp[state_rel_frame_def, capture_abi_memory_def] >> gen_tac >>
  rpt CASE_TAC >> simp[return_def, raise_def] >>
  simp[abi_append_def, evaluation_state_component_equality] >>
  metis_tac[APPEND_NIL]
QED

Theorem capture_abi_immutable_append:
  state_rel_frame abi_append (capture_abi_immutable cx src id tv v)
Proof
  simp[state_rel_frame_def, capture_abi_immutable_def] >> gen_tac >>
  rpt CASE_TAC >> simp[return_def, raise_def] >>
  simp[abi_append_def, evaluation_state_component_equality] >>
  metis_tac[APPEND_NIL]
QED

Theorem lookup_abi_local_append:
  state_rel_frame abi_append (lookup_abi_local cx id)
Proof
  simp[state_rel_frame_def, lookup_abi_local_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def] >> gen_tac >>
  Cases_on `lookup_scopes id st.scopes` >> simp[return_def, raise_def] >>
  IF_CASES_TAC >> simp[bind_def, return_def] >>
  Cases_on `capture_abi_memory cx id x.type x.value st` >> Cases_on `q` >> simp[] >>
  drule (capture_abi_memory_append |> SRULE [state_rel_frame_result]) >> simp[]
QED

Theorem lookup_abi_immutable_append:
  state_rel_frame abi_append (lookup_abi_immutable cx src id)
Proof
  simp[state_rel_frame_def, lookup_abi_immutable_def, bind_def, UNCURRY] >>
  gen_tac >> Cases_on `get_immutables cx src st` >> Cases_on `q` >> simp[] >>
  drule vyperStatePreservationTheory.get_immutables_state >> strip_tac >> gvs[] >>
  simp[lift_option_type_def] >> CASE_TAC >> simp[return_def, raise_def] >>
  qmatch_goalsub_rename_tac `abi_append before _` >>
  qmatch_goalsub_rename_tac `abi_primitive (FST entry)` >>
  PairCases_on `entry` >> simp[] >> IF_CASES_TAC >> simp[bind_def, return_def] >>
  Cases_on `capture_abi_immutable cx src id entry0 entry1 before` >>
  rename1 `capture_abi_immutable cx src id entry0 entry1 before = (res,after)` >>
  Cases_on `res` >> simp[] >>
  drule (capture_abi_immutable_append |> SRULE [state_rel_frame_result]) >> simp[]
QED

Theorem lookup_abi_global_append:
  state_rel_frame abi_append (lookup_abi_global cx src id)
Proof
  simp[state_rel_frame_def, lookup_abi_global_def, bind_def,
    lift_option_type_def] >> gen_tac >>
  rpt (CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  simp[lookup_abi_immutable_append |> SRULE [state_rel_frame_def]]
QED

Theorem abi_append_release:
  abi_append st mid ==> release_abi_captures
    (LENGTH st.abi_memory, LENGTH st.abi_immutables) mid = (INL (),st)
Proof
  rw[abi_append_def, release_abi_captures_def, return_def] >>
  simp[TAKE_APPEND, evaluation_state_component_equality]
QED

Theorem abi_append_scoped_state:
  state_rel_frame abi_append f /\
  (do mark <- mark_abi_captures; finally f (release_abi_captures mark) od) st = (res,rt) ==>
  rt = st
Proof
  simp[mark_abi_captures_def, bind_def, return_def, finally_def] >>
  strip_tac >> Cases_on `f st` >>
  `abi_append st r` by (drule_all state_rel_frame_at >> simp[]) >>
  drule abi_append_release >> strip_tac >>
  Cases_on `q` >>
  gvs[ignore_bind_def, bind_def, return_def, raise_def]
QED

val abi_append_finally_state = save_thm("abi_append_finally_state",
  abi_append_scoped_state |> SRULE [mark_abi_captures_def, bind_def, return_def]);

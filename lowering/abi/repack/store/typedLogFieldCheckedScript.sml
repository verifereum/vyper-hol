(* TOP-LEVEL: checked compatible field types satisfy the uniform Log
   contract. Only genuinely recursive outer stores need a child contract. *)
Theory typedLogFieldChecked
Ancestors
  typedLogFieldContract typedStoreContract typedCopyTypeContract
  typedStaticCompatibility typedTupleLeafContract vyperEventCompatibility
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  list finite_map

Theorem event_arg_compatible_word_shape:
  (!fty aty. event_arg_compatible fty aty ==> (is_word_type fty = is_word_type aty)) /\
  (!fts ats. event_arg_compatible_list fts ats ==> MAP is_word_type fts = MAP is_word_type ats)
Proof
  ho_match_mp_tac event_arg_compatible_ind >>
  rw[event_arg_compatible_def, is_word_type_def] >> gvs[is_word_type_def]
QED

Theorem word_event_compatible_same:
  !fty aty. event_arg_compatible fty aty /\ is_word_type fty ==> fty = aty
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_static_type)) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspec_then `FEMPTY` mp_tac) >> simp[word_type_abi_static]
QED

Theorem log_field_type_contract_checked:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    (fty <> aty /\ ~tuple_memory_layout_eq fty aty /\ ~is_bytestring_type fty ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) ==>
    log_field_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_value_has_type)) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`type_env tops`, `ftv`, `atv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  Cases_on `is_word_type fty`
  >- (`fty = aty` by (irule word_event_compatible_same >> simp[]) >>
      pop_assum (SUBST_ALL_TAC o SYM) >> `ftv = atv` by fs[] >> pop_assum SUBST_ALL_TAC >>
      mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `fty`, `atv`]
        log_field_type_contract_word) >> simp[]) >>
  `~is_word_type aty` by
    (mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_word_shape)) >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `fty`, `aty`, `ftv`, `atv`] memory_store_type_contract_checked) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`]
    log_field_type_contract_memory) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked uniform Log field contract: " ^ name)
  end) (DB.thms "typedLogFieldChecked")

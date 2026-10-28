(* TOP-LEVEL: typed event values fit the actual compiler's Log ABI buffer.
   This discharges conversion success and the output-capacity premise of
   native Log emission, including recursive argument widening. *)
Theory checkedLogDataEncoding
Ancestors
  typedLogSplitComplete abiTypeBounds abiTypeShape sourceAbiTypingLists
  vyperTypeABI vyperTypeDefaults vyperABI vyperValue vyperTyping
  stmtLowering compileEnv contractABI list arithmetic

Theorem checked_log_data_encoding_bound:
  !tenv sfields flags fts ftvs values.
    abi_struct_env_rel tenv sfields /\ LENGTH flags = LENGTH fts /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) fts ftvs /\
    values_have_types ftvs values ==>
    ?avs.
      vyper_to_abi_list tenv (log_non_indexed_types flags fts)
        (select_log_args F flags values) = SOME avs /\
      LENGTH (enc (Tuple (MAP (vyper_to_abi_type tenv) (log_non_indexed_types flags fts))) (ListV avs)) <=
        MAX 32 (abi_size_bound sfields (TupleT (log_non_indexed_types flags fts)))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH ftvs` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv)
    (log_non_indexed_types flags fts) (select_log_args F flags ftvs)` by
    (simp_tac bool_ss [log_non_indexed_types_select] >>
     irule select_log_args_list_rel >> simp[]) >>
  `values_have_types (select_log_args F flags ftvs) (select_log_args F flags values)` by
    (simp_tac bool_ss [values_have_types_LIST_REL] >>
     irule select_log_args_list_rel >> fs[values_have_types_LIST_REL]) >>
  qspecl_then [`tenv`, `log_non_indexed_types flags fts`, `select_log_args F flags values`,
    `select_log_args F flags ftvs`] mp_tac (cj 2 vyper_to_abi_total) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `avs` ASSUME_TAC) >>
  qspecl_then [`tenv`, `log_non_indexed_types flags fts`, `select_log_args F flags values`,
    `avs`, `select_log_args F flags ftvs`] mp_tac (cj 2 vyper_to_abi_enc_length_bound) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qspecl_then [`tenv`, `sfields`, `log_non_indexed_types flags fts`, `select_log_args F flags ftvs`]
    mp_tac evaluated_abi_tuple_size_bound >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `avs` >> fs[source_abi_types_map]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked Log data encoding bound: " ^ name)
  end) (DB.thms "checkedLogDataEncoding")

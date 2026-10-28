(* TOP-LEVEL: source event metadata uses the same complete tuple payload as
   the native encoder, without a fixed per-field encoding classification. *)
Theory abiNativeLogSource
Ancestors
  abiNativeLogPath abiLogSourceEncoding eventLogSplitProps e2eDefs
  sourceAbiTypingLists vyperEvent vyperABI compileEnv contractABI list words

Theorem event_metadata_encoding:
  !tenv flags tys values avs logger sig_hash topics.
    encode_indexed_event_topics flags tys values = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags tys) (select_log_args F flags values) = SOME avs ==>
    encode_vyper_event_metadata tenv logger (sig_hash,tys,flags) values =
      SOME <|logger := logger; topics := n2w sig_hash::topics;
        data := enc (Tuple (MAP (vyper_to_abi_type tenv) (log_non_indexed_types flags tys))) (ListV avs)|>
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH values` by
    fs[encode_indexed_event_topics_characterization] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  asm_simp_tac (srw_ss()) [encode_vyper_event_metadata_def, log_non_indexed_values_select, source_abi_types_map]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed unrestricted source event payload: " ^ name)
  end) (DB.thms "abiNativeLogSource")

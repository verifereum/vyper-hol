(* Source and ABI facts at the successful Log argument observation. *)
Theory bodyLogSuccessSourceLayoutMods
Ancestors
  bodyLogAbiLayoutMods bodyLogSourceEncodingMods bodyFullExtCallDirectLayout
  bodyCopyReadPhysicalTypeMods bodyExprPreFacts typedLogSplitComplete
  eventLogSplitProps whitelistLogWiden entryDecodeStaticProps vyperArith
  exprBodyPreProps vyperEventArgCompat typedCopyCompatibility abiLogSourceEncoding
  allocLimits words list pair

Theorem log_layout_typed_rows[local]:
  LIST_REL (\ty v. ?rt. evaluate_type tenv ty = SOME rt /\ value_has_type rt v)
    (MAP SND (rows:('a # type) list)) vs /\
  vyper_to_abi_list tenv (MAP SND rows) vs = SOME avs /\
  sfields_tenv_consistent (sf:string |-> (string # type # num) list) tenv ==>
  let ats = vyper_to_abi_types tenv (MAP SND rows) in
    LIST_REL (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at)
      rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
    LENGTH (enc (Tuple ats) (ListV avs)) <= abi_size_bound sf (TupleT (MAP SND rows))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `ZIP (MAP FST (rows:('a # type) list),MAP SND rows) = rows` by simp[GSYM UNZIP_MAP, ZIP_UNZIP] >>
  mp_tac (Q.INST [`env` |-> `tenv`]
    (ISPECL [``MAP FST (rows:('a # type) list)``,
        ``MAP SND (rows:('a # type) list)``,
        ``MAP SND (rows:('a # type) list)``,
        ``sf:string |-> (string # type # num) list``]
      (Q.GENL [`saved`,`tys`,`arg_types`,`sf`] (SPEC_ALL extcall_direct_args_layout)))) >>
  impl_tac >-
    (qhdtm_assum `LIST_REL`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [LIST_REL_EL_EQN]) >>
     simp_tac (srw_ss()) [LENGTH_MAP, vyperTypeSystemTheory.arg_type_fits_refl] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     first_x_assum (drule_then strip_assume_tac) >>
     qexistsl_tac [`rt`,`rt`] >> simp[EL_MAP]) >>
  disch_then strip_assume_tac >> gvs[]
QED

Theorem log_indexed_lowered_support[local]:
  LENGTH flags = LENGTH dtys /\
  LIST_REL (\dty e. event_arg_compatible dty (expr_type e)) dtys args /\
  EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
  expr_sim_inv_mods mods ce cx env entry /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e entry) args ==>
  EVERY (\(ty,f). f ==> supported_event_leaf_type ty)
    (ZIP (MAP (lowered_value_type ce) args,flags))
Proof
  simp[EVERY_EL, LIST_REL_EL_EQN, LENGTH_ZIP, EL_ZIP, EL_MAP] >>
  strip_tac >> rpt strip_tac >>
  `arg_type_fits (lowered_value_type ce (EL n args)) (expr_type (EL n args))` by
    (irule copy_lowered_fits_mods >> qexistsl_tac [`cx`,`env`,`entry`,`mods`] >>
     simp[] >> metis_tac[expr_body_pre_mods_well_typed]) >>
  `event_arg_compatible (EL n dtys) (lowered_value_type ce (EL n args))` by
    (fs[event_arg_compatible_alias_def] >> metis_tac[cj 1 arg_type_fits_trans]) >>
  `n < LENGTH dtys /\ n < LENGTH flags` by decide_tac >>
  `supported_event_leaf_type (EL n dtys)` by
    (`EL n (ZIP (dtys,flags)) = (EL n dtys,EL n flags)` by
       (irule EL_ZIP >> decide_tac) >>
     qpat_x_assum `!n. _ ==> _ (EL n (ZIP (dtys,flags)))` (qspec_then `n` mp_tac) >>
     simp[UNCURRY]) >>
  irule (cj 1 event_leaf_arg_compatible) >> qexists_tac `EL n dtys` >> simp[]
QED

Theorem log_success_source_layout_mods:
  let tenv = get_tenv cx in
  let atys = MAP (lowered_value_type ce) args in
  let rows = SND (split_log_ops (ZIP (saved,atys)) flags) in
  let ats = vyper_to_abi_types tenv (log_non_indexed_types flags atys) in
  let cap = abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) in
  contract_inv mods exps ctx ce cx /\ contract_namespaces_ok dep mods /\
  stmt_exprs_ok ce (Log id args) /\
  ce.ce_event_info (nsid_to_string id) = SOME (h,dtys,flags) /\
  lookup_event_metadata tenv cx.sources cx.txn.target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL (\dty e. event_arg_compatible dty (expr_type e)) dtys args /\
  EVERY (assignable_type tenv) dtys /\
  EVERY (\(ty,indexed). indexed ==> supported_event_leaf_type ty) (ZIP (dtys,flags)) /\
  expr_sim_inv_mods mods ce cx env entry /\
  EVERY (\e. expr_body_pre_mods mods ce cx env e entry) args /\
  eval_exprs cx args entry = (INL vs,mid) /\ LENGTH saved = LENGTH args ==>
  ?topics avs.
    LENGTH flags = LENGTH args /\ LENGTH flags = LENGTH saved /\ LENGTH flags = LENGTH vs /\
    encode_indexed_event_topics flags atys vs = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags atys)
      (log_non_indexed_values flags vs) = SOME avs /\
    encode_source_event tenv cx.sources cx.txn.target id vs =
      SOME <|logger := cx.txn.target; topics := n2w h::topics;
             data := enc (Tuple ats) (ListV avs)|> /\
    EVERY (\(ty,f). f ==> supported_event_leaf_type ty) (ZIP (atys,flags)) /\
    (!j. j < LENGTH flags ==>
      expr_body_pre_mods mods ce cx env (EL j args) entry /\
      ?rt. evaluate_type tenv (EL j atys) = SOME rt /\
        value_has_type rt (EL j vs) /\
        type_memory_bytes ce (EL j atys) = type_memory_size rt /\ type_memory_size rt < 2**64) /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!ty rt. evaluate_type tenv ty = SOME rt ==> type_memory_bytes ce ty = type_memory_size rt) /\
    MAP SND rows = log_non_indexed_types flags atys /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
    (rows <> [] ==> LENGTH (enc (Tuple ats) (ListV avs)) <= cap /\ cap < dimword (:256))
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_source_encoding_mods >> simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choosel_then [`topics`,`avs`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) log_abi_layout_metadata_mods >>
  drule_all_then assume_tac log_indexed_lowered_support >>
  `LENGTH flags = LENGTH args` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH flags = LENGTH vs` by metis_tac[LIST_REL_LENGTH, LENGTH_MAP] >>
  qabbrev_tac `atys = MAP (lowered_value_type ce) args` >>
  qmatch_goalsub_abbrev_tac `MAP SND rows` >>
  `EVERY (type_alloc_ok ce) atys /\
   abi_size_bound ce.ce_struct_fields (TupleT (log_non_indexed_types flags atys)) < 2**64` by
    (qpat_x_assum `stmt_exprs_ok _ (Log _ _)` mp_tac >>
     simp[stmt_exprs_ok_flat, alloc_limits_stmt_def, log_alloc_ok_def, Abbr `atys`]) >>
  `MAP SND rows = log_non_indexed_types flags atys` by
    (simp[Abbr `rows`, eventLogSplitPropsTheory.split_log_ops_select,
          log_non_indexed_types_select, GSYM select_log_args_MAP,
          MAP_ZIP, LENGTH_ZIP, Abbr `atys`]) >>
  suspend "layout"
QED

Resume log_success_source_layout_mods[layout]:
  `LIST_REL (\ty v. ?rt. evaluate_type (get_tenv cx) ty = SOME rt /\ value_has_type rt v)
    (MAP SND rows) (log_non_indexed_values flags vs)` by
    (simp[log_non_indexed_types_select, log_non_indexed_values_select] >>
     irule select_log_args_list_rel >> simp[Abbr `atys`]) >>
  `vyper_to_abi_list (get_tenv cx) (MAP SND rows)
     (log_non_indexed_values flags vs) = SOME avs` by simp[] >>
  drule_all log_layout_typed_rows >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j. j < LENGTH flags ==>
     expr_body_pre_mods mods ce cx env (EL j args) entry /\
     ?rt. evaluate_type (get_tenv cx) (EL j atys) = SOME rt /\
          value_has_type rt (EL j vs) /\
          type_memory_bytes ce (EL j atys) = type_memory_size rt /\
          type_memory_size rt < 2**64` by suspend "sizes" >>
  `abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) < dimword (:256)` by
    (irule vyperArithTheory.lt_dimword_256 >> qexists_tac `64` >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) []) >>
  qpat_x_assum `MAP SND rows = _` (fn th =>
    rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  qexistsl_tac [`topics`,`avs`] >> asm_rewrite_tac[] >> simp[]
QED

Resume log_success_source_layout_mods[sizes]:
  gen_tac >> strip_tac >>
  `j < LENGTH args /\ j < LENGTH atys` by simp[Abbr `atys`] >>
  conj_tac >- fs[EVERY_EL] >>
  qpat_assum `LIST_REL _ atys vs` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  disch_then (qspec_then `j` mp_tac o CONJUNCT2) >> simp_tac bool_ss [] >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  rename1 `evaluate_type _ (EL j atys) = SOME rt` >>
  `type_memory_bytes ce (EL j atys) = type_memory_size rt` by
    (qpat_assum `!ty tv. evaluate_type _ ty = SOME tv ==> _` (drule_then ACCEPT_TAC)) >>
  qexists_tac `rt` >> asm_rewrite_tac[] >>
  `type_alloc_ok ce (EL j atys)` by fs[EVERY_EL] >>
  Cases_on `is_word_type (EL j atys)` >>
  fs[type_alloc_ok_def, cj 3 word_type_dec_sizes] >> decide_tac
QED

Finalise log_success_source_layout_mods

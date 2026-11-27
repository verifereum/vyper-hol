(* Attach both possible origins of the input payload to the actual caller
   setup witnesses and forward the same invariant into the guarded entry. *)
Theory bodyFullAbiDecodeCallerEntryOrigin
Ancestors
  bodyFullAbiDecodeCallerSetupEntry bodyFullAbiDecodeCallerEntryContained
  exprSimAbiDecodeFootprint exprOpenFirstOperand exprSimHyps vyperValue
  compileEnv abiBuiltinDecodeSetup exprSimAbiDecodeBodyEntry

val caller_input_origin = ``\s b.
  (?aid ib isz.
    aid < abi_builtin_decode_output_site st min_size max_size /\
    FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\
    ib <= w2n (n2w (b+32) : bytes32) /\
    w2n (n2w (b+32) : bytes32) + LENGTH (input_bytes : word8 list) <= ib+isz) \/
  (?name ib isz.
    local_region ce es.scopes s name ib isz /\
    ib <= w2n (n2w (b+32) : bytes32) /\
    w2n (n2w (b+32) : bytes32) + LENGTH (input_bytes : word8 list) <= ib+isz)``;

val (setup_pre, setup_post) =
  dest_imp (#2 (strip_forall (concl abi_decode_body_setup_entry)));
val (setup_witnesses, setup_core) = strip_exists setup_post;
val setup_origin = ``(^caller_input_origin) s ^(hd setup_witnesses)``;
val setup_origin_stmt =
  mk_imp (setup_pre, list_mk_exists (setup_witnesses, mk_conj (setup_core, setup_origin)));

Theorem abi_decode_body_setup_entry_origin:
  ^(list_mk_forall (free_vars setup_origin_stmt, setup_origin_stmt))
Proof
  rpt gen_tac >> disch_tac >>
  first_assum (mp_tac o MATCH_MP (GEN_ALL abi_decode_body_setup_entry)) >>
  disch_then (qx_choose_then `b` (qx_choose_then `data_var` (qx_choose_then `d`
    (assume_tac o BETA_RULE)))) >>
  qexistsl_tac [`b`, `data_var`, `d`] >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(contract_inv _ _ _ _ _ /\ module_body_inv _ _ _ _ _) /\ _`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_assum `?H. V H` (qx_choose_then `horizon` assume_tac) >>
  qpat_assum `!H. V H ==> expr_post H ctx fn ce cx e es0 origin st s0 es _ _ s /\ _`
    (qspec_then `horizon` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac kall_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule_all abi_decode_body_operand_evaluates >> simp[]) >>
  `~is_word_type (expr_type e)` by simp[compileEnvTheory.is_word_type_def] >>
  drule_all abi_decode_bytes_post_footprint >>
  disch_then (qx_choose_then `p` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `b+32+LENGTH input_bytes < dimword (:256) /\ eval_operand data s = SOME (n2w b)` by
    (qpat_assum `_ /\ _ /\ _ /\ _` mp_tac >> simp[]) >>
  `b = p` by
    (`(n2w b : bytes32) = n2w p` by metis_tac[optionTheory.SOME_11] >>
     pop_assum mp_tac >> simp[wordsTheory.n2w_11]) >>
  `w2n (n2w (b+32) : bytes32) = b+32` by simp[] >>
  `st.cs_next_id < abi_builtin_decode_output_site st min_size max_size` by
    simp[abi_builtin_decode_output_site_def] >>
  qpat_x_assum `(?aid ib isz. FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ _) \/ _`
    strip_assume_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  disj2_tac >> goal_assum (drule_at Any) >> simp[]
QED

val (entry_pre, entry_post) =
  dest_imp (#2 (strip_forall (concl abi_decode_caller_guarded_entry_contained)));
val ready_origin = ``(^caller_input_origin) t b``;
val guarded_origin_stmt =
  mk_imp (mk_conj (entry_pre, ready_origin), mk_conj (entry_post, ready_origin));

Theorem abi_decode_caller_guarded_entry_origin:
  ^(list_mk_forall (free_vars guarded_origin_stmt, guarded_origin_stmt))
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (assume_tac o MATCH_MP (GEN_ALL abi_decode_caller_guarded_entry_contained))
    assume_tac) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

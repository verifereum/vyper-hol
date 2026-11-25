(* Scope and ownership of the installed ABI decoder, after its argument. *)
Theory entryCreateAbiDecodeCut
Ancestors
  entryCreateEffectFocus createSizeDecodeCode abiBuiltinDecodeCorrect
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  extcallReturnDecoderCode abiDecoderVarSequence exprSimAbiDecodeSiteCoverage
  entryCreateIntervalLayout externalEntryShape exprSimAbiDecodeOblivious exprSimAbiEncodeObliviousLabels
  bodyFullAbiDecodeCallerOperands bodyFullAbiDecodeCallerCutChoice exprSimAbiGasBridgeEdge
  builtinAbi context compileEnv emitHelper emitHelperProps createSizeCutCode
  createSizeCutOpens fragExec exprLoweringProps exprSimAbiGasBridge venomInst rich_list list pair
  entryCreateAbiDecodeObserverItinerary entryCreateCompletedCut entryCreateFocusSpec
  bodyFullAbiDecodeCallerFull bodyFullAbiDecodeCallerSetupOrigin bodyFullAbiDecodeCallerCutEndpoint
  bodyFullAbiDecodeRecursive bodyFullIfExpReach fragGasOriginPtr fragGasPath vyperStorageFootprint

Theorem abi_decode_setup_cut_code[local]:
  abi_builtin_decode_setup data mn mx cap start = (ops,ready) ==>
  create_cut_code {} start ready /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code start ready)
Proof
  strip_tac >>
  `create_cut_code {} start (SND (abi_builtin_decode_setup data mn mx cap start))` by
    (simp_tac std_ss [abi_builtin_decode_setup_def, abi_builtin_decode_header_def,
       abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
       abi_builtin_eq_guard_def, abi_builtin_bound_test_def, compile_alloc_buffer_def] >>
     rpt (FIRST [CHANGED_TAC (simp[comp_ignore_bind_def, LET_THM,
                        create_cut_code_emit_op, create_cut_code_emit_void,
                        create_cut_targets_def]),
                 match_mp_tac (Q.INST [`exits` |-> `{}`] create_cut_code_bind_uniform) >> BETA_TAC,
                 conj_tac, IF_CASES_TAC, gen_tac])) >>
  conj_tac >- gvs[] >>
  qpat_x_assum `abi_builtin_decode_setup _ _ _ _ _ = _` mp_tac >>
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_setup_def, abi_builtin_decode_header_def,
    abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[frag_code_def, emitted_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem create_abi_decode_tail_code:
  lower_abi_decode data info mn mx cap start = (out,final) ==>
  create_cut_code {} start final /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code start final)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule abi_decode_setup_cut_code >> strip_tac >>
  `create_cut_code {} ready final` by
    metis_tac[SND, SIMP_RULE (srw_ss()) [create_cut_targets_def]
      (Q.INST [`load` |-> `MLOAD`] create_decode_to_buf_cut_code)] >>
  conj_tac >- metis_tac[create_cut_code_join] >>
  drule return_decoder_frag_code >> strip_tac >>
  `cs_extends start ready /\ cs_extends ready final` by fs[create_cut_code_def] >>
  drule_all abi_decode_frag_code_compose >> disch_then (fn th =>
    simp_tac bool_ss [EVERY_MEM,th]) >>
  qx_gen_tac `i` >> strip_tac
  >- (qpat_assum `EVERY _ (frag_code start ready)` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
      disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  qpat_assum `EVERY _ (frag_code ready final)` (mp_tac o REWRITE_RULE[EVERY_MEM]) >>
  disch_then (qspec_then `i` mp_tac) >> simp[abi_decoder_reentry_opcode_def] >>
  strip_tac >> simp[]
QED

Theorem create_abi_decode_tail_visit_cut:
  lower_abi_decode data info mn mx cap start = (out,final) /\
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code start final func ==>
  create_operand_cut start final explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >> drule create_abi_decode_tail_code >> strip_tac >>
  irule create_effect_suffix_cut >> metis_tac[]
QED

(* The installed layout excludes the colliding-label branch of the ABI
   caller correctness proof. In particular, an ordinary observer suffices
   at a guarded expression site. *)
Theorem create_abi_decode_tail_regular:
  lower_abi_decode data info mn mx cap a = (out,b) /\
  create_layout a b /\ data <> Label a.cs_current_bb ==>
  frag_gas_free a b /\
  ~(a.cs_blocks <> b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb)
Proof
  strip_tac >> drule lower_abi_decode_frag_facts >> strip_tac >>
  Cases_on `a.cs_blocks = b.cs_blocks` >- fs[] >>
  drule frag_extends_emitted_shape >>
  Cases_on `emitted_blocks a b = []` >> simp[] >> strip_tac >>
  `MEM (LAST (emitted_blocks a b)) (emitted_blocks a b)` by
    simp[MEM_LAST_NOT_NIL] >>
  `~MEM b.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks a b)) /\
   ~MEM a.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks a b)))` by
    (qpat_x_assum `create_layout a b` mp_tac >> simp[create_layout_def] >>
     qpat_assum `(LAST (emitted_blocks a b)).bb_label = a.cs_current_bb`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     qpat_assum `emitted_blocks a b <> []`
       (mp_tac o MATCH_MP APPEND_FRONT_LAST) >>
     disch_then (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  `a.cs_current_bb <> b.cs_current_bb` by (fs[MEM_MAP] >> metis_tac[]) >>
  `~MEM a.cs_current_bb (opened_labels a b)` by
    simp[opened_labels_def, NULL_EQ, MEM_APPEND, MAP_REVERSE] >>
  drule_all lower_abi_decode_unopened_operand >>
  fs[frag_gas_free_def, frag_ops_free_def, EVERY_MEM] >> metis_tac[]
QED

(* Reuse the ordinary caller's context, entry handoff and posts. The four
   closed producer premises are discharged by the checked decoder below. *)
local
  val caller = CONV_RULE (REPEATC (REWR_CONV boolTheory.LET_THM THENC BETA_CONV))
    abi_decode_caller_full_conditional
  val caller_pre = funpow 4 rand (lhand (concl caller))
  val (_, [params,tops,cx,st0,source,init,q,r]) = strip_comb (rand (concl caller))
in
  val scoped_decode_tail = ``^caller_pre /\ create_layout start final ==>
    scoped_operand_outcome ^params ^tops ^cx ^st0 start final ^source ^init ^q ^r``
end

Theorem create_abi_decode_selected_tail:
  ^scoped_decode_tail
Proof
  BETA_TAC >> disch_then (CONJUNCTS_THEN2 (mk_asm "entry") assume_tac) >>
  mp_tac (BETA_RULE abi_decode_caller_full_observed) >>
  impl_tac >-
    (conj_tac >-
       (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        mp_tac (SPEC_ALL (BETA_RULE abi_decode_caller_setup_origin_observed)) >>
        simp[CONJ_ASSOC] >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
     conj_tac >-
       (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
        mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] abi_decode_guarded_to_buf_joint)) >>
        CONV_TAC (REDEPTH_CONV BETA_CONV) >>
        pure_rewrite_tac [GSYM CONJ_ASSOC] >> disch_then ACCEPT_TAC) >>
     conj_tac >- ACCEPT_TAC (BETA_RULE abi_decode_caller_cut_choice) >>
     conj_tac >-
       (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
        mp_tac (SPEC_ALL abi_decode_caller_endpoint_committed) >>
        simp[boolTheory.LET_THM, CONJ_ASSOC] >> disch_then ACCEPT_TAC) >>
     asm "entry" ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`res`,`r`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS)) >>
  `create_operand_at start s` by
    (asm "entry" (CONJUNCTS_THEN2 kall_tac strip_assume_tac) >>
     pure_rewrite_tac[create_operand_at_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  asm_x "entry" (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS) kall_tac) >>
  drule create_abi_decode_tail_code >> strip_tac >>
  drule_all create_abi_decode_tail_regular >> strip_tac >>
  `gas_path ctx (frag_observer start final func 0) s 0 r` by
    (first_x_assum irule >> irule frag_observer_has_code >> simp[]) >>
  `create_operand_full_scope start final explicit ctx func s [] r` by
    (Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
       `(?t. r = OK t /\ create_operand_at final t) \/ (?v. r = Abort Revert_abort v)`
     >- (qpat_assum `(_ : bool) \/ (?v. r = Abort Revert_abort v)` mp_tac >>
         simp_tac std_ss [create_operand_at_def] >> metis_tac[]) >>
     drule_all (SIMP_RULE std_ss [LET_THM] create_regular_observer_itinerary) >>
     disch_then (qspec_then `explicit` (DISJ_CASES_THEN strip_assume_tac))
     >- (qpat_assum `r = OK _` SUBST1_TAC >>
         fs[create_operand_full_scope_def,create_operand_at_def]) >>
     `gas_origin_path T explicit ctx func s [] r` by
       (`valid_horizon cx st0 (storage_trace_horizon es1.storage_trace) es1.storage_trace` by
          (pure_rewrite_tac[GSYM storage_trace_domain_def] >> first_assum ACCEPT_TAC) >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
          (drule_then (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
        drule_then (ACCEPT_TAC o CONJUNCT1) gas_origin_ptr_path_projections) >>
     `exit_result r` by simp[exit_result_def] >>
     `gas_origin_edge T explicit ctx func u [] r` by
       (irule create_prefix_selected_terminal_edge >>
        conj_tac >- (gen_tac >> disch_tac >> drule_all body_inv_no_phi >> simp[]) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl [`start`,`final`,`s`] >> conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `r = Abort Revert_abort _` (fn th =>
       SUBST1_TAC th >> simp[create_operand_full_scope_def, NoAsms] >>
       qexists `u` >> pure_rewrite_tac[GSYM th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `~create_operand_at final u` mp_tac >>
       simp_tac std_ss [create_operand_at_def] >> metis_tac[]) >>
     first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[scoped_operand_outcome_def] >>
  qexists `[]` >> disj2_tac >> disj1_tac >>
  qexistsl [`res`,`es1`,`r`,`Gf`,`tnf`] >>
  pure_rewrite_tac[gasSummaryTheory.gas_explicit_nil, listTheory.APPEND] >>
  BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

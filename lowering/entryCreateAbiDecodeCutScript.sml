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

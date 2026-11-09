(* Observed flat-tuple execution replay, at compiler-boundary cursors. *)
Theory abiDecodePtrFlatRun
Ancestors
  abiDecodePtrFlatLayout abiDecodePtrMemberInterface abiDecodePtrSelectedMember
  abiDecodePtrSelectedAbort abiDecodePtrNormalized abiDecodePtrContinuation
  abiEncoder abiDecoderAppend abiDecoderCounters exprLoweringProps emitHelperProps
  abiDecoderReentryPointer loweringShapeRules instIdxIndep
  compileEnv context bodyPtrDefs fragGasSeqPtr instSeqComposePtr
  assignTuplePtrLocalBytesCopy fragExec venomState venomExecSemantics
  words arithmetic list

Theorem abi_decode_flat_success:
  !infos off q sa sb s G tn u.
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_flat_layout infos off q z h cap /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi infos off q sa = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    abi_decode_member_frame sa G tn s H tf
      (u with vs_inst_idx := LENGTH sb.cs_current_insts)
      (w2n d+q) (SUM (MAP (SND o SND) infos))
Proof
  Induct >- suspend "nil" >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >> strip_tac >>
  rename1 `abi_decode_flat_layout ((ei,asz,msz)::infos) off q z h cap` >>
  drule_all abi_decode_flat_compile_cons_code >> strip_tac >>
  `s.vs_inst_idx = LENGTH sa.cs_current_insts` by
    metis_tac[abi_decode_member_live_compiler] >>
  `?t. t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    run_inst_seq (emitted_insts sa sm) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
    run_inst_seq (emitted_insts sm sb) t = OK (u with vs_inst_idx := t.vs_inst_idx)` by
    suspend "split" >>
  fs[abi_decode_flat_layout_def] >>
  drule_all abi_decode_selected_member_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  suspend "tail"
QED

Resume abi_decode_flat_success[nil]:
  simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> rpt strip_tac >>
  gvs[emitted_insts_def, run_inst_seq_def, inst_seq_ptr_def] >>
  `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
    (drule abi_decode_member_live_compiler >> simp[venom_state_component_equality]) >>
  simp[abi_decode_member_frame_def]
QED

Resume abi_decode_flat_success[split]:
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_decode_run_split_normalized >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sm) = LENGTH sm.cs_current_insts` by
    fs[inst_extends_def] >> metis_tac[]
QED

Resume abi_decode_flat_success[tail]:
  `t with vs_inst_idx := LENGTH sm.cs_current_insts = t` by
    simp[venom_state_component_equality] >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `(u with vs_inst_idx := LENGTH sm.cs_current_insts) with
     vs_inst_idx := LENGTH sb.cs_current_insts =
   u with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp[venom_state_component_equality] >>
  fs[] >>
  rename1 `inst_seq_ptr D 0 ctx func PG H tf (emitted_insts sm sb) t J tj` >>
  `sa.cs_next_var <= sm.cs_next_var` by suspend "age" >>
  qexistsl_tac [`J`, `tj`] >> simp[] >>
  conj_tac >- suspend "path" >>
  irule abi_decode_member_frame_compose >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume abi_decode_flat_success[age]:
  qpat_assum `compile_getelemptr_abi _ _ _ _ _ _ sa = _` mp_tac >>
  disch_then (mp_tac o MATCH_MP abi_decoder_member_pointer_counters) >> strip_tac >>
  qpat_assum `emit_op _ _ sm' = _` (mp_tac o MATCH_MP emit_op_facts) >> strip_tac >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = ((),sm)`
    (mp_tac o MATCH_MP abi_decoder_variable_counter) >> strip_tac >>
  gvs[] >> Cases_on `dec_info_needs_offset ei` >>
  Cases_on `hi = Lit 0w` >> gvs[] >> decide_tac
QED

Resume abi_decode_flat_success[path]:
  `s.vs_inst_idx + LENGTH (emitted_insts sa sm) = LENGTH sm.cs_current_insts` by
    fs[inst_extends_def] >>
  irule inst_seq_ptr_append_run >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise abi_decode_flat_success

Theorem abi_decode_flat_abort:
  !infos off q sa sb s G tn a u.
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_flat_layout infos off q z h cap /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi infos off q sa = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = Abort a u ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf
Proof
  Induct
  >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def] >> rpt strip_tac >>
      gvs[emitted_insts_def, run_inst_seq_def]) >>
  qx_gen_tac `entry` >> PairCases_on `entry` >> rpt gen_tac >> strip_tac >>
  rename1 `abi_decode_flat_layout ((ei,asz,msz)::infos) off q z h cap` >>
  drule_all abi_decode_flat_compile_cons_code >> strip_tac >>
  fs[abi_decode_flat_layout_def] >>
  Cases_on `?r. run_inst_seq (emitted_insts sa sm) s = OK r`
  >- (pop_assum strip_assume_tac >> suspend "tail") >>
  `run_inst_seq (emitted_insts sa sm) s = Abort a u` by
    metis_tac[run_inst_seq_append_err] >>
  drule_all abi_decode_selected_member_abort >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tf`] >> irule inst_seq_ptr_abort_append >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Resume abi_decode_flat_abort[tail]:
  `run_inst_seq (emitted_insts sm sb) r = Abort a u` by
    metis_tac[run_inst_seq_append] >>
  drule_all abi_decode_selected_member_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  qmatch_asmsub_abbrev_tac `abi_decode_member_live _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sm H tf t` >>
  `run_inst_seq (emitted_insts sm sb) t =
     Abort a (u with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (qspec_then `emitted_insts sm sb` mp_tac run_inst_seq_inst_idx >>
     disch_then (qspecl_then [`r`, `LENGTH sm.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def, Abbr `t`]) >>
  first_x_assum drule_all >> strip_tac >>
  `s.vs_inst_idx = LENGTH sa.cs_current_insts` by
    metis_tac[abi_decode_member_live_compiler] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sm) = LENGTH sm.cs_current_insts` by
    fs[inst_extends_def] >>
  qexistsl_tac [`H'`, `tf'`] >>
  irule inst_seq_ptr_append_run >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> qexists_tac `r` >>
  pure_asm_rewrite_tac[] >> fs[Abbr `t`]
QED

Finalise abi_decode_flat_abort

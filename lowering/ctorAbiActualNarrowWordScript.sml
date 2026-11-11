Theory ctorAbiActualNarrowWord
Ancestors
  ctorAbiActualNarrow ctorAbiActualWordRun ctorAbiActualMemberSetup
  ctorAbiActualFrame ctorAbiActualWorld abiDecoderContract abiDecoderDynamicLoopSetup
  abiEncoderRegisteredEffect abiDecoderLoop abiDecoderReentry abiEncoderProps
  fragExec venomState venomMemDefs finite_map pred_set list arithmetic words
  abiDecoderWordTyped abiDecoderLayout abiDecoderTypedContract abiDecoderReentryPointer
  abiDecoderClampedWord abiDecoderCoherence allocaFrontierBound allocaBudgetProps
  valueEncoding compileEnv loweringStateRelDefs exprLoweringProps venomExecSemantics

(* The independent memory frame, not the broad effect, provides separation. *)
Theorem ctor_actual_frame_empty_effect:
  abi_decode_frame d n s t /\ t.vs_allocas = s.vs_allocas /\
  abi_encoder_registered_effect ids outs s t ==>
  abi_encoder_registered_effect {} [(d,n)] s t
Proof
  simp_tac bool_ss [abi_decode_frame_def, abi_encoder_registered_effect_def] >>
  strip_tac >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!p k. _` irule >> decide_tac
QED

Theorem ctor_actual_address_empty_effect:
  abi_decoder_address_frame next s t /\
  abi_encoder_registered_effect ids outs s t ==>
  abi_encoder_registered_effect {} [] s t
Proof
  simp[abi_decoder_address_frame_def, abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_scratch_same_allocas:
  t.vs_allocas = s.vs_allocas ==>
  (ctor_actual_scratch fn ids d n t <=> ctor_actual_scratch fn ids d n s)
Proof
  simp[ctor_actual_scratch_def]
QED

Theorem ctor_actual_word_narrow_fragment:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
      abi_decode_frame d 32 initial t /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\
        eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
      abi_encoder_registered_effect {} [(d,32)] initial t /\
      (alloca_inv t <=> alloca_inv initial) /\
      (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial)) (K F)
Proof
  strip_tac >> drule_all ctor_actual_word_fragment >>
  disch_then (qspecl_then [`site`, `func`, `ctx`] assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[] >> irule ctor_actual_frame_empty_effect >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Theorem ctor_actual_member_setup_narrow_fragment:
  abi_decode_member_setup dst src DLOAD (Lit 0w) hi dyn ao vo st = (ops,st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (dyn ==> abi_decode_load DLOAD (n2w (sb + ao) : bytes32) initial = n2w payload_off /\
    sb + payload_off < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d + vo)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\
      (!fn ids D N. ctor_actual_scratch fn ids D N t <=>
        ctor_actual_scratch fn ids D N initial)) (K F)
Proof
  strip_tac >> drule_all ctor_actual_member_setup_fragment >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> simp[]
  >- (irule ctor_actual_address_empty_effect >> conj_tac
      >- (goal_assum (drule_at Any)) >> goal_assum (drule_at Any)) >>
  irule ctor_actual_scratch_same_allocas >> gvs[abi_decoder_address_frame_def]
QED

Theorem ctor_actual_word_narrow_run:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_coherent ce env sf ty tv /\ abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
  ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
      [(d,type_memory_bytes ce ty)] initial actual /\
    alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
    ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
    actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
    fresh_vars_wrt limit_st actual /\ actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
   mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by
    metis_tac[] >>
  drule_all ctor_actual_word_narrow_fragment >>
  disch_then (qspecl_then [`site`, `func`, `ctx`] assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
  `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
    [(d,32)] initial actual` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[(d,32)]`] >> simp[]) >>
  `ctor_actual_scratch func ids D N actual` by
    (drule ctor_actual_scratch_same_allocas >> simp[]) >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  qexists `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live st.cs_next_var (Var x)` by
    (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
  first_x_assum drule_all >> simp[eval_operand_def]
QED

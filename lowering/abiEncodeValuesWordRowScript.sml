Theory abiEncodeValuesWordRow
Ancestors
  abiEncodeValuesStaticPrefix abiDecodeRanges
  abiEncodeValuesCode abiEncodeValuesPhases abiEncodeValuesRun abiEncoderWindowPhase
  exprSimAbiEncodePlanMetadata abiStaticAggregateProps allocaSiteResource
  abiEncoderRegisteredEffect abiEncoderWindowContract
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic fragGasOriginPtrLoop fragExec freshWrites
  emitHelper emitHelperProps exprLowering exprLoweringProps context compileEnv bodyPtrDefs loweringStateRelDefs
  ptrDiscipline vyperValue vyperTyping vyperABI valueEncodingDefs contractABI
  venomExecSemantics venomState venomInst instIdxIndep abiEncoderProps
  words list finite_map pred_set arithmetic

(* The straight-line ADD/MSTORE run underlying the saved word row.
   The endpoint uses the native cursor, while run_inst_seq leaves it raw. *)
Definition abi_word_row_run_def:
  abi_word_row_run st en s t <=>
    en.cs_current_bb = st.cs_current_bb /\
    en.cs_current_insts = st.cs_current_insts ++ emitted_insts st en /\
    EVERY (\i. i.inst_id IN frag_ids st en /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
      (emitted_insts st en) /\
    ?raw. run_inst_seq (emitted_insts st en) s = OK raw /\
          t = (raw with vs_inst_idx := LENGTH en.cs_current_insts)
End

Theorem abi_word_row_concrete_run[local]:
  emit_op ADD [Var dst;Lit (n2w off)] st = (Var p,mid) /\
  emit_void MSTORE [Var p;src] mid = ((),en) /\
  eval_operand (Var dst) s = SOME (n2w b) /\
  u = (update_var p (n2w b + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
  eval_operand (Var p) u = SOME (n2w d) /\ eval_operand src u = SOME w /\
  d < dimword (:256) /\ t = (mstore d w u with vs_inst_idx := LENGTH en.cs_current_insts) ==>
  abi_word_row_run st en s t
Proof
  strip_tac >>
  `mid.cs_current_bb = st.cs_current_bb` by
    (drule emit_op_extends >> simp[same_blocks_def]) >>
  `en.cs_current_bb = mid.cs_current_bb` by
    (drule emit_void_extends >> simp[same_blocks_def]) >>
  drule emitted_insts_emit_op >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    (irule emitted_insts_append >> simp[]) >>
  qabbrev_tac `r = update_var p (n2w b + n2w off) s` >>
  `eval_operand (Var p) r = SOME (n2w d) /\ eval_operand src r = SOME w` by
    (qpat_assum `u = _` (fn th => fs[th,eval_op_inst_idx])) >>
  `run_inst_seq (emitted_insts st mid) s = OK r` by
    simp[Abbr `r`,run_inst_seq_def,mk_inst_def,step_inst_base_opcode_eqs,
         exec_pure2_def,eval_operand_def] >>
  qpat_x_assum `p = _` kall_tac >>
  `run_inst_seq (emitted_insts mid en) r = OK (mstore d w r)` by
    (simp[run_inst_seq_def,mk_inst_def,step_inst_base_opcode_eqs,
          exec_write2_def,w2n_n2w]) >>
  `run_inst_seq (emitted_insts st en) s = OK (mstore d w r)` by
    (qpat_assum `emitted_insts st en = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `run_inst_seq (emitted_insts st mid) s = OK r`
       (fn th => SUBST1_TAC (SPEC ``emitted_insts mid en`` (MATCH_MP run_inst_seq_append th))) >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[abi_word_row_run_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[APPEND_ASSOC] >>
  conj_tac >- simp[frag_ids_def,mk_inst_def,is_terminator_def] >>
  qexists_tac `mstore d w r` >> asm_rewrite_tac[] >> simp[mstore_idx]
QED

Theorem abi_encode_values_stack_word_run:
  compile_abi_encode_value_rows ce (Var dst) cursor off [(StackValue tag src,ty)] st =
    ((),en) /\
  is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand (Var dst) s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  off + 32 <= cap /\ d + cap <= s.vs_alloca_next /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_word_row_run st en s t /\
    mem_bytes_at (d + off) 32 t.vs_memory = enc (vyper_to_abi_type env ty) av /\
    window_phase ctx func st en {} [(d + off,32)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | d + off <= i /\ i < d + off + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_value_rows_static_trace >>
  disch_then (qx_choose_then `head` (qx_choose_then `mid` strip_assume_tac)) >>
  gvs[unwrap_value_def, compile_abi_encode_value_rows_def, comp_return_def] >>
  `st.cs_next_var <= mid.cs_next_var /\ cs_extends st mid` by
    metis_tac[ci_mono_def, ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends mid en` by
    metis_tac[ci_mono_def, ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code st mid func /\ fn_has_code mid en func` by
    metis_tac[fn_has_code_split] >>
  mp_tac (Q.INST [`n` |-> `32`,`b` |-> `d`,`en` |-> `mid`]
     abi_encode_values_head_address_endpoint) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choose_then `p` (qx_choose_then `u`
    (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac)))) >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  `d + off + 32 <= u.vs_alloca_next` by
    (fs[window_alloca_growth_def] >> decide_tac) >>
  `u.vs_allocas = s.vs_allocas` by
    (simp[FLOOKUP_EXT] >>
     drule window_phase_effect >> simp[abi_encoder_registered_effect_def] >>
     metis_tac[FLOOKUP_EXT]) >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  `eval_operand src u = SOME (typed_val_to_w256 tv v)` by
    metis_tac[window_phase_operand] >>
  `op_taint tu src = {}` by
    (Cases_on `src` >> fs[op_taint_def] >> metis_tac[op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (`u.vs_initial_fmp = s.vs_initial_fmp /\ u.vs_fmp = s.vs_fmp` by
       metis_tac[abi_encode_exec_frame_def, abi_encode_semantic_obs_fields] >>
     metis_tac[allocas_below_fmp_def]) >>
  qpat_x_assum `head = Var p` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`head` |-> `p`, `d` |-> `d+off`, `st` |-> `mid`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`] abi_encode_values_word_head_endpoint) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `abi_word_row_run st en s t` by
    (drule_all abi_word_row_concrete_run >> simp[]) >>
  `window_phase ctx func st en {} [(d + off,32)] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`,`[]`,`mid`,`{}`,`[(d + off,32)]`,`u`] >> simp[]) >>
  `abi_encode_exec_frame func s t` by metis_tac[abi_encode_exec_frame_trans] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gu,tn')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]) >>
  `!x. op_taint tn' (Var x) = op_taint tu (Var x)` by simp[op_taint_def] >>
  qexistsl_tac [`t`,`Gu`,`tn'`] >> asm_rewrite_tac[] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [simp_tac bool_ss [arithmeticTheory.ADD_ASSOC], metis_tac[]]
QED

Theorem abi_encode_values_stack_word:
  compile_abi_encode_value_rows ce (Var dst) cursor off [(StackValue tag src,ty)] st =
    ((),en) /\
  is_word_type ty /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  eval_operand (Var dst) s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  off + 32 <= cap /\ d + cap <= s.vs_alloca_next /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at (d + off) 32 t.vs_memory = enc (vyper_to_abi_type env ty) av /\
    window_phase ctx func st en {} [(d + off,32)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {i | d + off <= i /\ i < d + off + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >> drule_all abi_encode_values_stack_word_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

(* A word row writes its ABI head and keeps the tail cursor unchanged. *)
Theorem abi_encode_values_word_prefix_run:
  compile_abi_encode_value_rows ce (Var dst) cursor h [(StackValue tag src,ty)] st = ((),en) /\
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type env ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h+32 <= hl /\ off <= cap /\
  sfields_tenv_consistent ce.ce_struct_fields env /\ is_word_type ty /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var dst) s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner <> loc /\
  b <= d /\ d + cap <= b+capacity /\ b+capacity <= s.vs_alloca_next /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_word_row_run st en s t /\
    abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn' /\
    window_phase ctx func st en {} [(d+h,32)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `~is_abi_dynamic ce.ce_struct_fields ty /\ ~is_dynamic at /\
    abi_member_head_size at = 32 /\ abi_member_tail_size at av = 0` by
    (drule_then (qspecl_then [`ce.ce_struct_fields`,`ce`] strip_assume_tac)
       entryDecodeStaticPropsTheory.word_type_dec_sizes >>
     drule_all abi_encode_translated_dynamic >> strip_tac >>
     drule_all abi_encode_translated_head >> strip_tac >>
     `~is_dynamic at /\ abi_member_head_size at = 32` by metis_tac[] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `~is_dynamic at` (fn th => simp_tac bool_ss [abi_member_tail_size_def,th])) >>
  `h + 32 <= cap /\ d+cap <= s.vs_alloca_next` by decide_tac >>
  `ci_mono st en` by metis_tac[ci_mono_compile_abi_encode_value_rows, pairTheory.SND] >>
  mp_tac (Q.INST [`off` |-> `h`] abi_encode_values_stack_word_run) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  `!j. d+h <= j /\ j < d+h+32 ==> j NOTIN tn'.t_mem` by
    (qpat_assum `tn'.t_mem = _ DIFF _`
      (fn th => simp_tac (srw_ss()) [th, IN_DIFF]) >> metis_tac[]) >>
  `!j. (j < d+h \/ d+h+32 <= j) ==> j IN tn'.t_mem ==> j IN tn.t_mem` by
    (qpat_assum `tn'.t_mem = _ DIFF _` (fn th => simp_tac (srw_ss()) [th, IN_DIFF])) >>
  `d + off <= b + capacity` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `d+cap` >>
     simp_tac (srw_ss()) [arithmeticTheory.LE_ADD_LCANCEL] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at (d+h) 32 t.vs_memory = enc at av` by
    (qpat_assum `at = vyper_to_abi_type env ty` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn'` by
    (mp_tac (Q.INST [`hs` |-> `32`] abi_encode_values_static_prefix) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       TRY (sym_tac >> first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_simp_tac (srw_ss()) [SUBSET_DEF, IN_DIFF]
QED

Theorem abi_encode_values_word_prefix:
  compile_abi_encode_value_rows ce (Var dst) cursor h [(StackValue tag src,ty)] st = ((),en) /\
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type env ty /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h+32 <= hl /\ off <= cap /\
  sfields_tenv_consistent ce.ce_struct_fields env /\ is_word_type ty /\
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  type_memory_bytes ce ty = type_memory_size tv /\
  eval_operand (Var dst) s = SOME (n2w d) /\ ptr_covers G tn dst s cap /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner <> loc /\
  b <= d /\ d + cap <= b+capacity /\ b+capacity <= s.vs_alloca_next /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ alloca_inv s /\ alloca_room ctx func s /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn' /\
    window_phase ctx func st en {} [(d+h,32)] s t /\ abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_word_prefix_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac)) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

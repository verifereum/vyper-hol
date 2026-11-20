Theory abiEncodeValuesPrefix
Ancestors
  abiEncodeValuesRun
  abiEncodeValuesCode abiEncodeValuesMetadata abiEncodeValuesCursorInit abiEncodeValuesFinish
  abiEncodeValuesAdvance abiEncodeValuesDynamic abiEncodeValuesLayout abiEncodeValuesPhases
  allocaSiteResource freshWrites
  abiEncoderTuple abiEncoderOpenInput abiCanonicalWindows abiEncoderWindowPhase abiEncoderWindowContract
  abiEncoderRegisteredEffect exprSimAbiEncodeExecFrame bodyFullAbiEncodeOriginFloor
  fragGasOriginPtr fragGasOriginPtrLoop fragExec exprLoweringProps
  compileEnv exprLowering emitHelperProps ptrDiscipline valueEncodingDefs
  bodyPtrDefs loweringPosts loweringStateRelDefs assignTuplePtrCopyLen
  contractABI venomState venomMemDefs venomInst finite_map pred_set list rich_list arithmetic pair

(* A word store, aggregate copy, or dynamic member supplies the bytes at
   its own window. The loop grows the two prefixes and cursor together. *)
Theorem abi_encode_values_prefix_next:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\
  abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ ts = abi_member_tail_size at av /\
  h + hs <= hl /\
  window_phase ctx func st en ids outs s t /\ ci_mono st en /\ alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (b,cap) /\ owner NOTIN ids /\
  b <= d /\ d+off+ts <= b+cap /\
  outs = (if is_dynamic at then [(d+h,hs); (d+off,ts)] else [(d+h,hs)]) /\
  (!j. EVERY (\(p,n). j < p \/ p+n <= j) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
       j < p \/ p+n <= j) /\ j IN tn'.t_mem ==> j IN tn.t_mem) /\
  (!j. d+h <= j /\ j < d+h+hs ==> j NOTIN tn'.t_mem) /\
  (!j. d+off <= j /\ j < d+off+ts ==> j NOTIN tn'.t_mem) /\
  (is_dynamic at ==>
    mem_word_at (d+h) t.vs_memory = n2w off /\
    mem_bytes_at (d+off) ts t.vs_memory = enc at av) /\
  (~is_dynamic at ==> mem_bytes_at (d+h) hs t.vs_memory = enc at av) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  mem_word_at slot t.vs_memory = n2w (off+ts) /\
  (!j. slot <= j /\ j < slot+32 ==> j NOTIN tn'.t_mem) ==>
  abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  `LENGTH (TAKE i ats) = LENGTH (TAKE i avs)` by simp[LENGTH_TAKE_EQ] >>
  `!j. d <= j /\ j < d+h ==> j NOTIN tn.t_mem` by
    (qpat_assum `h = LENGTH _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!j. d+hl <= j /\ j < d+off ==> j NOTIN tn.t_mem` by
    (qpat_assum `off = hl + _` SUBST1_TAC >>
     gen_tac >> disch_tac >>
     qpat_assum `!j. d+hl <= j /\ j < d+hl+_ ==> _` (qspec_then `j` irule) >>
     decide_tac) >>
  mp_tac (Q.INST [`pre` |-> `TAKE i ats`, `pvs` |-> `TAKE i avs`,
    `dst_base` |-> `b`, `dst_cap` |-> `cap`, `dst_site` |-> `owner`]
    abi_encode_values_phase_advance) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  strip_tac >>
  mp_tac (Q.INST [`pre` |-> `TAKE i ats`, `avs` |-> `TAKE i avs`]
     abi_encode_values_prefix_lengths) >>
  impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  `TAKE (SUC i) ats = TAKE i ats ++ [at] /\ TAKE (SUC i) avs = TAKE i avs ++ [av]` by
    simp[TAKE_SUC, TAKE1_DROP] >>
  `eval_operand (Var p) t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32` by
    (irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func st en ids outs s t` (irule_at Any) >>
     qexistsl_tac [`tn`,`G`] >> metis_tac[]) >>
  drule window_phase_effect >> drule window_phase_resources >>
  disch_then strip_assume_tac >> disch_then strip_assume_tac >>
  `loc < en.cs_next_id /\ not_fresh_at en p` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono,
      arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `FLOOKUP t.vs_allocas loc = SOME (slot,32)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `slot + 32 <= t.vs_alloca_next` by
    metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  simp_tac bool_ss [abi_encode_values_prefix_at_def, operand_11] >>
  qpat_assum `TAKE (SUC i) ats = _` (fn a =>
    qpat_assum `TAKE (SUC i) avs = _` (fn v => PURE_REWRITE_TAC [a,v])) >>
  asm_simp_tac bool_ss [ADD_ASSOC] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

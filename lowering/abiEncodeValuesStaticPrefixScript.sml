Theory abiEncodeValuesStaticPrefix
Ancestors
  abiEncodeValuesPrefix abiDecodeRanges
  abiEncodeValuesRun abiEncodeValuesStatic abiEncodeValuesSource
  abiEncodeValuesPhases abiEncoderWindowPhase abiEncoderWindowContract
  abiStaticAggregateProps allocaSiteResource exprSimAbiEncodeExecFrame
  abiCallerTupleLayout ptrDiscipline valueEncodingDefs
  compileEnv loweringStateRelDefs fragGasOriginPtr fragExec
  contractABI vyperABI vyperValue vyperTyping venomState venomMemDefs
  words finite_map pred_set list arithmetic

(* A static member writes its head window. The cursor and earlier
   prefixes stay in their original allocations. *)
Theorem abi_encode_values_static_prefix:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ ~is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h+hs <= hl /\
  window_phase ctx func st en {} [(d+h,hs)] s t /\ ci_mono st en /\ alloca_inv s /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner <> loc /\
  b <= d /\ d+off <= b+capacity /\
  mem_bytes_at (d+h) hs t.vs_memory = enc at av /\
  (!j. d+h <= j /\ j < d+h+hs ==> j NOTIN tn'.t_mem) /\
  (!j. (j < d+h \/ d+h+hs <= j) ==> (j IN tn'.t_mem ==> j IN tn.t_mem)) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  `venomMemDefs$regions_disjoint (b,capacity) (slot,32)` by
    metis_tac[alloca_site_registered_disjoint] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (slot,32) r) [(d+h,hs)]` by
    (simp_tac (srw_ss()) [venomMemDefsTheory.regions_disjoint_def] >>
     qpat_assum `venomMemDefs$regions_disjoint (b,capacity) (slot,32)`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.regions_disjoint_def]) >>
     decide_tac) >>
  mp_tac (Q.INST [`owner` |-> `loc`,`b` |-> `slot`,`sz` |-> `32`,
    `q` |-> `slot`,`n` |-> `32`, `ids` |-> `{}:num set`,
    `outs` |-> `[(d+h,hs)]`] abi_encode_values_registered_window) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    asm_simp_tac (srw_ss()) [] >> metis_tac[]) >>
  strip_tac >>
  `mem_word_at slot t.vs_memory = n2w off` by
    (PURE_REWRITE_TAC [mem_word_at_bytes] >>
     qpat_assum `mem_bytes_at slot 32 t.vs_memory = _` (fn th => PURE_REWRITE_TAC [th]) >>
     PURE_REWRITE_TAC [GSYM mem_word_at_bytes] >>
     metis_tac[]) >>
  `!j. slot <= j /\ j < slot+32 ==> j NOTIN tn'.t_mem` by metis_tac[] >>
  `abi_member_tail_size at av = 0` by simp[abi_member_tail_size_def] >>
  mp_tac (Q.INST [`cap` |-> `capacity`,`ts` |-> `0`,`ids` |-> `{}`,
    `outs` |-> `[(d+h,hs)]`] abi_encode_values_prefix_next) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    simp_tac (srw_ss()) [] >> TRY decide_tac >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED

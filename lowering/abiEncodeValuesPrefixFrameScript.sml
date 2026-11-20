Theory abiEncodeValuesPrefixFrame
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

(* Closing a delayed source does not write any part of the encoded prefix
   or the cursor. Both buffers are already allocated at that cut. *)
Theorem abi_encode_values_prefix_after_unwrap:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  wb_frame ce ee ee st s t /\ ghost_kept_at lo ce ee st G tn s G' tn' /\
  ci_mono st en /\ alloca_inv t /\
  FLOOKUP s.vs_allocas owner = SOME (b,cap) /\ owner < st.cs_next_id /\
  (!name p k. local_region ce ee.scopes s name p k ==>
    (b+cap <= p \/ p+k <= b) /\ (slot+32 <= p \/ p+k <= slot)) /\
  b <= d /\ d + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= b+cap /\
  d+hl+LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= b+cap ==>
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i en t G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`pre` |-> `TAKE i ats`, `pvs` |-> `TAKE i avs`,
    `dst_base` |-> `b`, `dst_cap` |-> `cap`, `dst_site` |-> `owner`,
    `cursor_site` |-> `loc`,
    `h` |-> `LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs)))`,
    `tl` |-> `LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))`]
    (INST_TYPE [alpha |-> ``:num # num``] abi_encode_values_unwrap_prefix)) >>
  impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
  strip_tac >>
  `eval_operand (Var p) t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32` by
    (qpat_assum `wb_frame ce ee ee st s t`
       (assume_tac o cj 1 o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `ghost_kept_at lo ce ee st G tn s G' tn'`
       (assume_tac o cj 1 o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_assum `eval_operand (Var p) s = SOME (n2w slot)`
       (assume_tac o REWRITE_RULE [eval_operand_def]) >>
     `lookup_var p t = SOME (n2w slot)` by
       (qpat_assum `!x w. not_fresh_at st x /\ _ ==> _`
         (qspecl_then [`p`,`n2w slot`] irule) >> asm_rewrite_tac[]) >>
     simp_tac bool_ss [eval_operand_def] >> asm_rewrite_tac[] >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`G`,`s`,`tn`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `not_fresh_at en p /\ loc < en.cs_next_id` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `slot+32 <= t.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  simp_tac bool_ss [abi_encode_values_prefix_at_def, operand_11] >> asm_rewrite_tac[]
QED

Theorem abi_encode_values_prefix_arith:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i st s G tn /\
  window_phase ctx func st en ids outs s t /\ ci_mono st en /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i en t G' tn'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  `eval_operand (Var p) t = SOME (n2w slot) /\ ptr_covers G' tn' p t 32` by
    (irule abi_encode_values_pointer_frame >>
     qpat_assum `window_phase ctx func st en ids outs s t` (irule_at Any) >>
     qexistsl_tac [`tn`,`G`] >> asm_rewrite_tac[]) >>
  `FLOOKUP t.vs_allocas loc = SOME (slot,32)` by
    metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `slot+32 <= t.vs_alloca_next` by
    metis_tac[window_phase_resources, allocaSiteResourceTheory.alloca_site_registered_below] >>
  `loc < en.cs_next_id /\ not_fresh_at en p` by
    (fs[ci_mono_def] >> metis_tac[not_fresh_at_mono, LESS_LESS_EQ_TRANS]) >>
  simp_tac bool_ss [abi_encode_values_prefix_at_def, operand_11] >> asm_rewrite_tac[]
QED

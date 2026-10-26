(* Compose setup, recursive child execution and cursor bookkeeping.
   TOP-LEVEL: abi_scratch_child_effect derives one enclosing precise effect;
   Helper: abi_scratch_child_operands chains the three register frames. *)
Theory abiScratchChildEffect
Ancestors
  abiScratchChildFrame abiScratchEncoderContract abiScratchEffectProtected abiScratchFootprint
  abiEncoderChildSuffixReach abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  compileEnv valueEncoding contractABI venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_child_operands:
  !next child_next suffix_st initial ready encoded actual first last child_lo child_hi
    limit_st q len b cap out h slot off.
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  abi_encoder_child_suffix_post out suffix_st limit_st h slot off len encoded actual /\
  next <= child_next /\ next <= suffix_st.cs_next_var ==>
  !op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `abi_decoder_operand_live suffix_st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `eval_operand op ready = SOME w` by fs[abi_decoder_address_frame_def] >>
  `eval_operand op encoded = SOME w` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
    (qspecl_then [`op`, `w`] mp_tac o List.last o CONJUNCTS o
      PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >> simp[]
QED

Theorem abi_scratch_child_effect:
  abi_decoder_address_frame next initial ready /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st q len b cap ready encoded /\
  abi_encoder_child_suffix_post out suffix_st limit_st h slot off len encoded actual /\
  first <= lo /\ hi <= last /\ lo <= child_lo /\ child_hi <= hi /\
  next <= child_next /\ next <= suffix_st.cs_next_var /\
  site IN abi_decoder_ids lo hi /\ FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  d <= h /\ h+32 <= d+sz /\ d <= q /\ q+len <= d+sz ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)
    initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last /\
   abi_decoder_ids child_lo child_hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids lo hi)` by simp[] >>
  `abi_decode_footprint_frame [(h,32);(slot,32)] encoded actual` by
    fs[abi_encoder_child_suffix_post_def] >>
  `abi_decode_footprint_frame
    ([(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)
    initial actual` by
    (drule_all (Q.INST [`ids` |-> `abi_decoder_ids lo hi`] abi_scratch_dynamic_child_frame) >> simp[]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(h,32);(q,len)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `n`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`d`, `sz`] >> simp[],
      qexistsl_tac [`p`, `n`] >> simp[]]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (mp_tac (Q.SPECL [`next`, `child_next`, `suffix_st`, `initial`, `ready`, `encoded`, `actual`,
       `first`, `last`, `child_lo`, `child_hi`, `limit_st`, `q`, `len`, `b`, `cap`, `out`, `h`,
       `slot`, `off`] abi_scratch_child_operands) >>
     impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  `(abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual <=>
    abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded)` by
    (irule abi_scratch_evolution_transport >>
     fs[abi_decoder_address_frame_def, abi_encoder_child_suffix_post_def]) >>
  `(abi_decoder_budget first last b cap actual <=> abi_decoder_budget first last b cap encoded)` by
    (irule abi_decoder_budget_transport >> fs[abi_encoder_child_suffix_post_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  qpat_assum `abi_encoder_child_suffix_post _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_child_suffix_post_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `!id. id < lo \/ hi <= id ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt gen_tac >> strip_tac >> `id < child_lo \/ child_hi <= id` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> gvs[] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_CHILD_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child composed effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchChildEffect");

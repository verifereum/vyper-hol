(* Compose recursive effects and account for a registered scratch-only write.
   TOP-LEVEL: effect_trans retains the initial physical footprint across
   allocation growth; single_write turns an actual cursor store into an effect. *)
Theory abiScratchEffectCompose
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiScratchEffectProtected
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry compileEnv venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_effect_trans:
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial middle /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap middle actual /\
  first <= lo /\ hi <= last ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand op middle = SOME w` by
       (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `middle:venom_state`]
         abi_scratch_effect_operand) >> asm_simp_tac bool_ss []) >>
     mp_tac (Q.INST [`s` |-> `middle:venom_state`, `t` |-> `actual:venom_state`]
       abi_scratch_effect_operand) >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial middle`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ middle actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids lo hi) b cap initial middle` by
    (irule abi_scratch_evolution_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) middle actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`, `s` |-> `initial:venom_state`,
      `t` |-> `middle:venom_state`, `u` |-> `actual:venom_state`] abi_scratch_frame_advance) >>
     asm_simp_tac (srw_ss()) []) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (drule_all abi_decode_footprint_frame_trans >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> rpt gen_tac >> strip_tac >> simp[]
QED

Theorem abi_scratch_single_write:
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
  actual.vs_halted = initial.vs_halted /\ fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w) /\
  abi_decode_footprint_frame [(slot,32)] initial actual ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `initial.vs_alloca_next <= b+cap` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> decide_tac) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (simp[abi_scratch_evolution_def] >> rpt strip_tac >> gvs[]) >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`, `id` |-> `site:num`,
      `s` |-> `initial:venom_state`, `p` |-> `slot:num`, `n` |-> `32:num`]
      abi_scratch_registered_member) >> simp[abi_decoder_ids_def]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
     asm_simp_tac (srw_ss()) [] >> qexistsl_tac [`slot`, `32`] >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_EFFECT_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch effect composition not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEffectCompose");

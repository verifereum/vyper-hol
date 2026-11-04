Theory abiScratchEffect
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiScratchSubset abiEncoderInputFrame
  abiEncoderInput abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  compileEnv valueEncoding contractABI venomState finite_map pred_set words list arithmetic
  abiDecoderArrayInitExec abiScratchFrameCompose

(* ===== Protected ===== *)

(* Complete sources and earlier cursor slots survive recursive child encoding.
   TOP-LEVEL: abi_scratch_effect_slot and abi_scratch_effect_source derive
   protection from physical footprints and the actual enclosing budget. *)

Theorem abi_scratch_effect_operand:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp_tac bool_ss [abi_scratch_effect_def] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_scratch_effect_slot:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_budget first last b cap s /\ first <= lo /\ hi <= last /\
  site IN abi_decoder_ids first last /\ ~(site IN abi_decoder_ids lo hi) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) ==>
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = mload slot s
Proof
  strip_tac >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids lo hi) /\ FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all abi_decoder_child_excludes_ancestor >> disch_then assume_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> simp[]) >>
  `abi_footprint_disjoint slot 32
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (simp_tac bool_ss [abi_scratch_disjoint_cons] >> asm_rewrite_tac[] >>
     qpat_x_assum `abi_footprint_disjoint d sz _`
       (qspecl_then [`slot`, `32`] mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
     simp[] >> decide_tac) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `site < lo \/ hi <= site` by fs[abi_decoder_ids_def] >>
  `FLOOKUP t.vs_allocas site = FLOOKUP s.vs_allocas site` by simp[] >>
  drule_all abi_decode_footprint_frame_mload >> simp[]
QED

Theorem abi_scratch_effect_source:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  first <= lo /\ hi <= last ==>
  abi_encoder_input ei at av sb source_cap t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
  `abi_footprint_disjoint sb source_cap
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    simp[abi_scratch_disjoint_cons] >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule_all abi_encoder_input_frame >> simp[]
QED

(* ===== Compose ===== *)

(* Compose recursive effects and account for a registered scratch-only write.
   TOP-LEVEL: effect_trans retains the initial physical footprint across
   allocation growth; single_write turns an actual cursor store into an effect. *)

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

(* ===== Frame ===== *)

(* Enclose a child effect in the physical footprint of its parent interval.
   TOP-LEVEL: abi_scratch_effect_frame exposes a reusable frame for preserving
   complete parent source data and initialized siblings around child execution. *)

Theorem abi_scratch_effect_frame:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t /\
  first <= lo /\ hi <= last ==>
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) s t
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_decoder_ids lo hi SUBSET abi_decoder_ids first last` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> conj_tac
  >- (qx_genl_tac [`obs`, `len`] >> strip_tac >>
      qpat_x_assum `abi_footprint_disjoint obs len (_::_)`
        (strip_assume_tac o REWRITE_RULE [abi_scratch_disjoint_cons]) >>
      `abi_footprint_disjoint obs len
        (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
        (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >> simp[]) >>
      `abi_footprint_disjoint obs len
        ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
        simp[abi_scratch_disjoint_cons] >>
      drule_all abi_decode_footprint_frame_slice >> simp[]) >>
  fs[abi_decode_footprint_frame_def]
QED

(* ===== Widen ===== *)

(* Enclose precise child effects in larger output and instruction intervals.
   TOP-LEVEL: abi_scratch_effect_widen retains allocation evolution and older
   operands while permitting only the enclosing physical write footprint. *)

Theorem abi_scratch_effect_widen:
  abi_scratch_effect first last child_lo child_hi child_next limit_st child_d child_sz b cap s t /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  d <= child_d /\ child_d+child_sz <= d+sz ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `abi_decoder_ids child_lo child_hi SUBSET abi_decoder_ids lo hi` by
    (simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  `abi_decode_footprint_frame
    ([(child_d,child_sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_scratch_frame_subset_append >> asm_simp_tac (srw_ss()) [] >>
     qexists_tac `abi_decoder_ids child_lo child_hi` >> simp[]) >>
  `abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(child_d,child_sz)] ++ abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `n`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`p`, `n`] >> simp[]]) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==> eval_operand op t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live child_next op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
     qpat_x_assum `!op w. _` irule >> simp[]) >>
  `!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (rpt gen_tac >> strip_tac >> `id < child_lo \/ child_hi <= id` by decide_tac >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> first_assum ACCEPT_TAC
QED

Theory abiScratchDecoderInitReentry
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiScratchFootprint abiScratchSequence
  abiDecoderArrayInit abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderContract abiDecoderReentry compileEnv venomState words list arithmetic pred_set
  abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderDynarrayPrefix
  abiDecoderArrayHeader abiDecoderGuards abiDecoderFrameCompose exprLoweringProps
  emitHelperProps valueEncoding abiDecoderArrayInitReentry abiDecoderDynarrayBound
  abiDecoderGuard abiDecoderReentryPointer abiDecoderVarSequence abiDecoderVarExtend emitHelper
  context fragExec venomInst finite_map rich_list

(* ===== Effect ===== *)

(* Account for a newly allocated or reused index inside the original physical footprint. *)

Theorem abi_scratch_frame_origin:
  abi_scratch_evolution ids b cap entry prepared /\ FINITE ids /\
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap prepared) before after ==>
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap entry) before after
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
  asm_simp_tac (srw_ss()) [] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _` irule >>
  qpat_x_assum `abi_footprint_disjoint _ _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [abi_scratch_disjoint_cons]) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >> asm_rewrite_tac[] >>
  drule_all abi_scratch_disjoint_advance >> simp[]
QED

Theorem abi_scratch_output_final_slot_frame:
  abi_scratch_evolution ids b cap initial actual /\ FINITE ids /\ site IN ids /\
  FLOOKUP actual.vs_allocas site = SOME (slot,n) /\
  abi_decode_footprint_frame [(d,sz);(slot,n)] initial actual ==>
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  strip_tac >>
  `MEM (slot,n) (abi_decoder_child_scratch ids b cap actual)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch ids b cap actual) initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(d,sz);(slot,n)]` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `k`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`slot`, `n`] >> simp[]]) >>
  mp_tac (Q.INST [`entry` |-> `initial:venom_state`, `prepared` |-> `actual:venom_state`,
    `before` |-> `initial:venom_state`, `after` |-> `actual:venom_state`] abi_scratch_frame_origin) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_init_effect:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial actual /\
  run_inst_seq insts initial = OK actual /\ lo <= site /\ site < hi ==>
  abi_scratch_effect first last lo hi next limit_st d 32 b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  disch_then (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids first last`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `abi_scratch_evolution (abi_decoder_ids lo hi) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids lo hi`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame
    ((d,32)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`, `sz` |-> `32:num`, `n` |-> `32:num`]
      abi_scratch_output_final_slot_frame) >>
     impl_tac >- asm_simp_tac (srw_ss()) [abi_decoder_ids_def] >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >>
  rpt gen_tac >> strip_tac >> `id <> site` by decide_tac >> asm_simp_tac bool_ss []
QED

(* ===== Sequence ===== *)

(* Physical output ownership keeps the real array count separate from its allocated index. *)

Theorem abi_scratch_sequence_slot_disjoint:
  run_inst_seq insts initial = OK actual /\ abi_decoder_budget first last b cap actual /\
  abi_footprint_disjoint d outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  site IN abi_decoder_ids first last /\ FLOOKUP actual.vs_allocas site = SOME (slot,sz) ==>
  slot + sz <= d \/ d + outsz <= slot
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids first last`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `initial.vs_alloca_next <= b + cap` by (fs[abi_scratch_evolution_def] >> decide_tac) >>
  drule_all abi_scratch_frontier_disjoint >> disch_then assume_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `p` |-> `d:num`, `n` |-> `outsz:num`, `id` |-> `site:num`, `q` |-> `slot:num`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_slot_disjoint) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> disch_then assume_tac >> decide_tac
QED

Theorem abi_scratch_decoder_init_sequence:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap s /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
  fresh_vars_wrt st s ==>
  ?t p. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\ eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\ b <= p /\ p + 32 <= b + cap /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt loop_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] s t /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (loop_st.cs_next_id-2) = SOME (p,32) /\
    (!id. id <> loop_st.cs_next_id-2 ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule_all abi_decode_array_prepare_sequence >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `header_st.cs_next_id IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `fresh_vars_wrt loop_st prepared` by
    (mp_tac (Q.SPECL [`header_st`, `loop_st`, `prepared`] fresh_vars_wrt_mono) >> simp[GREATER_EQ]) >>
  mp_tac (Q.INST [`st` |-> `header_st`, `st'` |-> `loop_st`,
    `s` |-> `prepared:venom_state`, `limit_st` |-> `loop_st`] abi_decode_index_init_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) prepared = OK actual` >>
  `!op w. eval_operand op prepared = SOME w ==> abi_decoder_operand_live header_st.cs_next_var op`
    by metis_tac[abi_decoder_operand_live_fresh] >>
  `eval_operand cnt actual = SOME (n2w n)` by metis_tac[] >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w` by metis_tac[] >>
  `abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (qpat_x_assum `abi_footprint_disjoint d 32
       (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` mp_tac >>
     asm_simp_tac bool_ss [abi_decoder_child_scratch_def]) >>
  `p + 32 <= d \/ d + 32 <= p` by
    (drule_all abi_scratch_sequence_slot_disjoint >> simp[]) >>
  `mem_word_at d actual.vs_memory = mem_word_at d prepared.vs_memory` by
    (irule abi_decode_frame_mem_word >> qexistsl_tac [`p`, `32`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(b,cap)] s actual` by
    (drule_all abi_decoder_array_init_frame >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(p,32)] s actual` by
    (drule_all abi_decoder_array_init_exact_frame >> simp[]) >>
  `run_inst_seq (emitted_insts st loop_st) s = OK actual /\ inst_extends st loop_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`, `header_st`] >> simp[]) >>
  qexistsl_tac [`actual`, `p`] >> gvs[]
QED

(* The real array initializer executes with stale local SSA bindings under physical ownership. *)
Theorem abi_scratch_decoder_child_scratch_prune[simp]:
  abi_decoder_child_scratch ids b cap (abi_decoder_prune_vars next s) =
  abi_decoder_child_scratch ids b cap s
Proof
  simp[abi_decoder_child_scratch_def, abi_decoder_prune_vars_def]
QED

Theorem abi_scratch_decoder_init_reentry:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual slot. run_inst_seq (emitted_insts st loop_st) initial = OK actual /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\
    eval_operand (SND setup) actual = SOME (n2w n) /\ mload slot actual = 0w /\
    mem_word_at d actual.vs_memory = n2w n /\ b <= slot /\ slot + 32 <= b + cap /\
    abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial actual /\
    abi_decode_footprint_frame [(d,32);(slot,32)] initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id - 2) = SOME (slot,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_halted = initial.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
    abi_scratch_decoder_init_sequence) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decoder_prune_fresh, abi_decoder_prune_eval, abi_scratch_decoder_child_scratch_prune] >>
  strip_tac >> rename1 `mload slot clean = 0w` >>
  `abi_decoder_vars_extend initial.vs_vars
    (abi_decoder_prune_vars st.cs_next_var initial) initial` by
    irule abi_decoder_prune_extension >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `abi_decoder_budget first last b cap actual` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `eval_operand (FST setup) actual = SOME (n2w slot) /\
   eval_operand (SND setup) actual = SOME (n2w n)` by
    metis_tac[abi_decoder_vars_extend_eval] >>
  `actual.vs_halted = initial.vs_halted` by
    (mp_tac (Q.INST [`insts` |-> `emitted_insts st loop_st`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
       abi_decoder_sequence_halted) >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(b,cap)] initial actual` by
    (gvs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC) >>
  `abi_decode_footprint_frame [(d,32);(slot,32)] initial actual` by
    (gvs[abi_decode_footprint_frame_def, abi_decoder_prune_vars_def] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`actual`, `slot`] >> gvs[mload_def, abi_decoder_prune_vars_def]
QED

Theorem abi_scratch_decoder_init_from_state:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st loop_st (\s. s = initial)
    (\actual. abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
        first last b cap d n initial actual /\
      abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
        limit_st d 32 b cap initial actual) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_scratch_decoder_init_reentry >> strip_tac >>
  `abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id - 2)
    first last b cap d n initial actual` by
    (simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `slot` >>
     asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d 32 b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `loop_st.cs_next_id`,
      `site` |-> `loop_st.cs_next_id-2`, `next` |-> `st.cs_next_var`,
      `insts` |-> `emitted_insts st loop_st`] abi_scratch_decoder_init_effect) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) []
QED

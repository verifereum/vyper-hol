(* The real array initializer executes with stale local SSA bindings under physical ownership. *)
Theory abiScratchDecoderInitReentry
Ancestors
  abiScratchDecoderInitSequence abiScratchDecoderInitEffect abiScratchEncoderContract
  abiDecoderFootprint abiDecoderArrayInitReentry
  abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderArrayInitReach
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuardLE abiDecoderGuards abiDecoderContract abiDecoderAllocation
  abiDecoderReentry abiDecoderReentryPrefix abiDecoderReentrySequence
  abiDecoderVarSequence abiDecoderVarExtend abiDecoderFrame
  exprLoweringProps emitHelperProps emitHelper compileEnv context
  fragExec venomState venomInst finite_map words list rich_list arithmetic


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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_INIT_REENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical decoder initializer reentry not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderInitReentry");

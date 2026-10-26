(* Whole builtin physical effects include its arbitrary-sized output allocation. *)
Theory abiScratchDecodeEffect
Ancestors
  abiScratchEncoderContract abiScratchEffectFrame abiScratchEffectProtected abiScratchFootprint
  abiBuiltinAllocationState abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderReentry abiDecoderContract compileEnv venomState finite_map words list arithmetic

Definition abi_scratch_decode_effect_def:
  abi_scratch_decode_effect first last st final limit_st site d outsz b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz s) t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame
      ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap
        (abi_builtin_allocate_state site outsz s)) s t /\
    t.vs_halted = s.vs_halted /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id)
End

Theorem abi_scratch_decode_whole_frame:
  abi_builtin_allocation_frame next site outsz initial prepared /\
  abi_scratch_effect first last lo hi child_next limit_st d outsz b cap prepared actual /\
  first <= lo /\ hi <= last ==>
  abi_decode_footprint_frame
    ((d,outsz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz initial)) initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_frame >> strip_tac >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz initial)` by
    fs[abi_builtin_allocation_frame_def, abi_decoder_child_scratch_def] >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> conj_tac
  >- fs[abi_builtin_allocation_frame_def, abi_decode_footprint_frame_def] >>
  qpat_x_assum `abi_decode_footprint_frame _ prepared actual` mp_tac >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decode_effect_compose:
  abi_builtin_allocation_frame st.cs_next_var site outsz initial prepared /\
  abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st d outsz b cap prepared actual /\
  first <= ready.cs_next_id /\ final.cs_next_id <= last /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= site /\
  site < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id ==>
  abi_scratch_decode_effect first last st final limit_st site d outsz b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decode_whole_frame >> disch_tac >>
  `!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op actual = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `eval_operand op prepared = SOME w` by fs[abi_builtin_allocation_frame_def] >>
     `abi_decoder_operand_live ready.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     drule_all abi_scratch_effect_operand >> simp[]) >>
  `(abi_scratch_evolution (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state site outsz initial) actual <=>
    abi_scratch_evolution (abi_decoder_ids first last) b cap prepared actual)` by
    (irule abi_scratch_evolution_transport >> fs[abi_builtin_allocation_frame_def]) >>
  `!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
    FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (qx_gen_tac `id` >> strip_tac >>
     `id <> site /\ (id < ready.cs_next_id \/ final.cs_next_id <= id)` by decide_tac >>
     `FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id` by
       (drule_all abi_builtin_allocation_frame_outside >> simp[]) >>
     fs[abi_scratch_effect_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac bool_ss [abi_scratch_decode_effect_def] >> fs[abi_scratch_effect_def] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODE_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical whole decoder builtin effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecodeEffect");


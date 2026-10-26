(* The complete source contract remains available after a recursive encoding.
   TOP-LEVEL: abi_scratch_input_effect transports source values, live operands
   and physical separation through the actual root allocation evolution. *)
Theory abiScratchInputEffect
Ancestors
  abiScratchEncoderContract abiScratchEffectProtected abiScratchFootprint
  abiDecoderFootprint abiDecoderReentry compileEnv venomState words arithmetic

Theorem abi_scratch_input_mono:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_input ei at av prepared src dst sb source_cap d sz first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_scratch_input_effect:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap initial /\
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
  first <= lo /\ hi <= last /\ st.cs_next_var <= next ==>
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_source >> disch_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    fs[abi_scratch_effect_def] >>
  `abi_footprint_disjoint sb source_cap
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) /\
   abi_footprint_disjoint d sz
     (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (conj_tac >> irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_input_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_INPUT_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complete input transport not kernel closed: " ^ n)
  end) (DB.thms "abiScratchInputEffect");

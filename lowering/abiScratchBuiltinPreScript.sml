(* Complete builtin input and physical resources after its output allocation.
   TOP-LEVEL: abi_scratch_builtin_pre and ready establish the core encoder
   contract while accounting separately for the full method-ID store width. *)
Theory abiScratchBuiltinPre
Ancestors
  abiScratchEncoderContract abiEncoderInput abiEncoderArrayFrame
  abiBuiltinEncodeSetupFrame abiBuiltinAllocationState abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState finite_map words list arithmetic

Definition abi_scratch_builtin_pre_def:
  abi_scratch_builtin_pre ei at av st method_id_opt src sb source_cap p maxlen first last b cap s <=>
    let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
    let write_size = case method_id_opt of NONE => 0 | SOME _ => 32 in
    let outsz = maxlen+32+mid_size in
    let allocated = abi_builtin_allocate_state st.cs_next_id outsz s in
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
    sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\ LENGTH (enc at av) <= maxlen /\
    (sb+source_cap <= p \/ p+outsz <= sb) /\
    (sb+source_cap <= p+32 \/ p+32+write_size <= sb) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
    st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
    abi_decoder_budget first last b cap allocated /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
    abi_footprint_disjoint p outsz
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated)
End

Theorem abi_scratch_builtin_ready:
  abi_scratch_builtin_pre ei at av st method_id_opt src sb source_cap p maxlen first last b cap initial /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
    (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) p
    (case method_id_opt of NONE => 0 | SOME _ => 32) initial prepared /\
  eval_operand dst prepared = SOME (n2w (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4))) /\
  st.cs_next_var <= ready.cs_next_var /\ abi_decoder_operand_live ready.cs_next_var dst ==>
  abi_scratch_input ei at av ready src dst sb source_cap
    (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) (LENGTH (enc at av))
    first last b cap prepared /\ abi_decoder_budget first last b cap prepared /\
  abi_footprint_disjoint p (32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_builtin_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_builtin_pre_def, LET_THM]) >>
  drule_all abi_builtin_encode_setup_frame_input >> disch_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (drule abi_builtin_encode_setup_frame_budget >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state st.cs_next_id
        (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) initial)` by
    fs[abi_builtin_encode_setup_frame_def, abi_decoder_child_scratch_def] >>
  `eval_operand src prepared = SOME (n2w sb)` by fs[abi_builtin_encode_setup_frame_def] >>
  `abi_decoder_operand_live ready.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_footprint_disjoint p (32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`p`, `maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_footprint_disjoint (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`p`, `maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_scratch_input_def, LESS_EQ_REFL] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_PRE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch builtin input not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinPre");

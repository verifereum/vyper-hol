(* Child inputs inherit physical separation from their enclosing buffers.
   TOP-LEVEL: abi_scratch_input_regions transfers complete child data and
   bounded subregions across allocator evolution, including reused sites. *)
Theory abiScratchInputRegions
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiEncoderArrayFrame
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  compileEnv valueEncoding contractABI venomState pred_set words list arithmetic

Theorem abi_scratch_input_regions:
  abi_scratch_input parent_ei parent_at parent_av st parent_src parent_dst
    sb source_cap d output_size first last b cap initial /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  abi_encoder_input ei at av child_sb child_cap actual.vs_memory /\
  eval_operand src actual = SOME (n2w child_sb) /\ eval_operand dst actual = SOME (n2w child_d) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  abi_decoder_operand_live prepared.cs_next_var dst /\
  sb <= child_sb /\ child_sb+child_cap <= sb+source_cap /\
  d <= child_d /\ child_d+child_size <= d+output_size /\ LENGTH (enc at av) <= child_size ==>
  abi_scratch_input ei at av prepared src dst child_sb child_cap child_d child_size
    first last b cap actual
Proof
  strip_tac >>
  qpat_x_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `abi_footprint_disjoint child_sb child_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`, `source_cap`] >> simp[]) >>
  `abi_footprint_disjoint child_d child_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`d`, `output_size`] >> simp[]) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  `abi_footprint_disjoint child_sb child_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`, `cap` |-> `cap:num`,
       `p` |-> `child_sb:num`, `n` |-> `child_cap:num`, `s` |-> `initial:venom_state`,
       `t` |-> `actual:venom_state`] abi_scratch_disjoint_advance) >> simp[]) >>
  `abi_footprint_disjoint child_d child_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`, `cap` |-> `cap:num`,
       `p` |-> `child_d:num`, `n` |-> `child_size:num`, `s` |-> `initial:venom_state`,
       `t` |-> `actual:venom_state`] abi_scratch_disjoint_advance) >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_input_def] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_INPUT_REGIONS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child regions not kernel closed: " ^ n)
  end) (DB.thms "abiScratchInputRegions");

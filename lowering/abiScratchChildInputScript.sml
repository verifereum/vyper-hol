(* Exact child destinations inherit their parent buffer's physical separation.
   TOP-LEVEL: abi_scratch_child_input_address selects a bounded output offset
   after the real register-only prefix, without a numeric arena exclusion. *)
Theory abiScratchChildInput
Ancestors
  abiScratchInputRegions abiScratchEncoderContract abiScratchFootprint
  abiEncoderInput abiDecoderDynamicLoopSetup abiDecoderReentry
  compileEnv valueEncoding contractABI venomState words arithmetic list

Theorem abi_scratch_child_input_address:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual /\
  st.cs_next_var <= prepared.cs_next_var /\
  abi_decoder_operand_live prepared.cs_next_var child_dst /\
  eval_operand child_dst actual = SOME (n2w (d+off)) /\
  off+LENGTH (enc at av) <= output_size ==>
  abi_scratch_input ei at av prepared src child_dst sb source_cap (d+off)
    (LENGTH (enc at av)) first last b cap actual
Proof
  strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  `actual.vs_memory = initial.vs_memory` by fs[abi_decoder_address_frame_def] >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by simp[] >>
  `eval_operand src actual = SOME (n2w sb)` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `sb <= sb /\ sb+source_cap <= sb+source_cap /\
   d <= d+off /\ d+off+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  mp_tac (Q.INST [`parent_ei` |-> `ei:abi_enc_info`, `parent_at` |-> `at:abi_type`,
    `parent_av` |-> `av:abi_value`, `parent_src` |-> `src:operand`, `parent_dst` |-> `dst:operand`,
    `dst` |-> `child_dst:operand`, `child_sb` |-> `sb:num`, `child_cap` |-> `source_cap:num`,
    `child_d` |-> `d+off`, `child_size` |-> `LENGTH (enc at av)`] abi_scratch_input_regions) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_CHILD_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child input not kernel closed: " ^ n)
  end) (DB.thms "abiScratchChildInput");

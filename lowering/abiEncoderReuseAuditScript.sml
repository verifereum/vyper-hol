(* Checked tag audit for the exact reusable encoder closure and new pure
   boundaries.  Importing an admitted ancestor is not itself using its proofs. *)
(* Loaded .dat files do not retain axiom dependencies.  The axiom check sees
   only current-session axioms; this does not audit upstream axiom freedom. *)
Theory abiEncoderReuseAudit
Ancestors
  abiScratchEncoderRecursive abiEncoderCorrectRecursive
  abiEncoderOpenInput abiEncoderRegisteredEffect abiEncoderStaticRepresentative

fun audit_encoder_tag (name, th) =
  let
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val bad = List.filter (fn s => s <> "DISK_THM") oracles
  in
    if null bad andalso null axioms then
      print ("ENCODER_REUSE_AUDIT_OK " ^ name ^ "\n")
    else raise Fail ("encoder reuse admission dependency: " ^ name)
  end;

val _ = List.app audit_encoder_tag
  [("abi_scratch_encoder_admissible_mutual", abi_scratch_encoder_admissible_mutual),
   ("abi_scratch_encoder_translation", abi_scratch_encoder_translation),
   ("abi_encoder_input_open", abi_encoder_input_open),
   ("abi_encoder_aligned_bytes_representative", abi_encoder_aligned_bytes_representative),
   ("abi_encoder_static_source_representative", abi_encoder_static_source_representative),
   ("abi_encoder_structural_valid_layout", abi_encoder_structural_valid_layout),
   ("abi_encoder_open_members_layout", abi_encoder_open_members_layout),
   ("abi_encoder_open_giant_zero_prefix", abi_encoder_open_giant_zero_prefix),
   ("abi_encoder_registered_effect_trans", abi_encoder_registered_effect_trans),
   ("abi_encoder_registered_effect_frame", abi_encoder_registered_effect_frame)];

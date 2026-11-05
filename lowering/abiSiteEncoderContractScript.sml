(* Generalized scratch contract. The enclosing set A and endpoint b+cap stay
   fixed when a recursive child is entered; only its write ownership narrows. *)
Theory abiSiteEncoderContract
Ancestors
  abiSiteAllocation abiScratchEncoderContract abiScratchFootprint
  abiDecoderSiteMembership abiDecoderFootprint abiDecoderAllocation abiDecoderFrame
  abiDecoderReentry abiDecoderLoop abiDecoderContract abiEncoderInput abiEncoder
  compileEnv valueEncoding contractABI instIdxIndep venomState finite_map pred_set
  words list arithmetic

Definition abi_site_encoder_input_def:
  abi_site_encoder_input ei at av st src dst sb source_cap d output_size A b cap s <=>
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    LENGTH (enc at av) <= output_size /\
    sb+source_cap < dimword (:256) /\ d+output_size < dimword (:256) /\
    (sb+source_cap <= d \/ d+output_size <= sb) /\
    abi_footprint_disjoint sb source_cap (abi_decoder_child_scratch A b cap s) /\
    abi_footprint_disjoint d output_size (abi_decoder_child_scratch A b cap s)
End

Definition abi_site_encoder_effect_def:
  abi_site_encoder_effect A lo hi next limit_st d sz b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_site_budget A b cap t /\
    abi_scratch_evolution A b cap s t /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame
      ((d,sz)::abi_decoder_child_scratch (A INTER abi_decoder_ids lo hi) b cap s) s t /\
    (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted
End

Definition abi_site_encoder_def:
  abi_site_encoder ei <=>
    !dst src start end_st out func ctx A b cap limit_st initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei start = (out,end_st) /\ fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_site_encoder_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
      A b cap initial /\ abi_site_budget A b cap initial /\
    abi_decoder_emitted_sites start.cs_next_id end_st.cs_next_id start end_st SUBSET A /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_site_encoder_effect A start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (LENGTH (enc at av)) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
End

Theorem abi_site_encoder_input_interval:
  abi_site_encoder_input ei at av st src dst sb source_cap d output_size
    (abi_decoder_ids first last) b cap s <=>
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap s
Proof
  simp[abi_site_encoder_input_def, abi_scratch_input_def]
QED

Theorem abi_site_encoder_effect_interval:
  first <= lo /\ hi <= last ==>
  (abi_site_encoder_effect (abi_decoder_ids first last) lo hi next limit_st d sz b cap s t <=>
   abi_scratch_effect first last lo hi next limit_st d sz b cap s t)
Proof
  strip_tac >>
  `abi_decoder_ids first last INTER abi_decoder_ids lo hi = abi_decoder_ids lo hi` by
    (simp[EXTENSION, abi_decoder_ids_def] >> decide_tac) >>
  simp[abi_site_encoder_effect_def, abi_scratch_effect_def, abi_site_budget_interval]
QED

Theorem abi_site_encoder_run:
  abi_site_encoder ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_encoder_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    A b cap initial /\ abi_site_budget A b cap initial /\
  abi_decoder_emitted_sites start.cs_next_id end_st.cs_next_id start end_st SUBSET A /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_site_encoder_effect A start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  rewrite_tac[abi_site_encoder_def] >> metis_tac[]
QED

(* This interface and its compatibility facts introduce no admissions. *)
val _ = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("non-clean finite-site encoder interface: " ^ name)
  end) (DB.thms "abiSiteEncoderContract");

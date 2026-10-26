(* Finite execution of actual static-element array iterations with physical frames.
   TOP-LEVEL: abi_scratch_array_static_finite_loop reaches the real exit edge.
   Helper: the actual header/body/backedge preserves the complete loop invariant. *)
Theory abiScratchArrayStaticFiniteLoop
Ancestors
  abiScratchArrayStaticRound abiScratchArrayLoopHeader abiScratchArrayLoopInvariant abiScratchArrayFiniteLoop
  abiScratchEffectWiden abiScratchEncoderContract abiEncoderArrayLoopCode abiEncoderArrayLoopHeader
  abiEncoderMembersDefs abiDecoderLoop abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState venomInst words list arithmetic

Theorem abi_scratch_array_loop_static_step:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin initial /\
  j < LENGTH avs ==>
  ?actual. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) (SUC j) origin actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `F`] abi_scratch_array_loop_header) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `j < LENGTH avs` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th, COND_CLAUSES]) >> assume_tac th) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST (SND labels)) j origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_array_loop_inv_def]) >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ origin ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  drule abi_encoder_array_loop_header_phi >> disch_then (qx_choose_then `hdr_bb` strip_assume_tac) >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  qmatch_asmsub_abbrev_tac `lookup_block body_end.cs_current_bb func.fn_blocks = SOME back_bb` >>
  `owner_st.cs_next_var <= body_st.cs_next_var /\ owner_st.cs_next_id <= body_st.cs_next_id /\
    body_end.cs_next_id+3 <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `body_st`, `end_st` |-> `body_end`, `out` |-> `idx`, `initial` |-> `ready:venom_state`,
    `lo` |-> `site:num`, `hdr` |-> `FST (labels:string # string # string)`, `bb` |-> `back_bb`]
    abi_scratch_array_static_round) >>
  impl_tac >- full_simp_tac (srw_ss()) [Abbr`back_bb`, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `body_end.cs_next_id+3`, `site`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `ready:venom_state`, `k` |-> `SUC j`,
    `label` |-> `FST (SND (labels:string # string # string))`,
    `next_label` |-> `FST (labels:string # string # string)`] abi_scratch_array_loop_inv_advance) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED

Theorem abi_scratch_array_static_finite_loop:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op
      (SND (SND labels)) (LENGTH avs) origin actual /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `i <= LENGTH avs` by (drule abi_scratch_array_loop_inv_facts >> simp[]) >>
  qabbrev_tac `loop_inv = \(j:num) (s:venom_state).
    abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) j origin s` >>
  qabbrev_tac `loop_post = \(s:venom_state).
    abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
      site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (SND (SND labels)) (LENGTH avs) origin s` >>
  mp_tac (Q.SPECL [`LENGTH (avs:abi_value list)`, `i:num`, `loop_inv`, `loop_post`, `ctx`, `func`, `initial:venom_state`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (asm_simp_tac bool_ss [Abbr`loop_inv`, Abbr`loop_post`] >> conj_tac
      >- (qx_genl_tac [`j`, `u`] >> strip_tac >>
          mp_tac (Q.INST [`j` |-> `j:num`, `initial` |-> `u:venom_state`] abi_scratch_array_loop_static_step) >>
          impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
      qx_gen_tac `u` >> strip_tac >>
      mp_tac (Q.INST [`active` |-> `F`, `initial` |-> `u:venom_state`] abi_scratch_array_loop_exit) >>
      impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [Abbr`loop_post`]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_STATIC_FINITE_LOOP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch finite static array execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayStaticFiniteLoop");

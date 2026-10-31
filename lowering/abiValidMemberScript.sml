Theory abiValidMember
Ancestors
  abiValidMembers abiValidAggregateHeads abiCanonicalHeadSize abiCanonicalHeadSize abiDecodeRanges
  abiDecoderContract vyperABI contractABI valueEncoding venomState words list rich_list
  arithmetic abiValidDecodedMetadata abiDecoderMemberSetup abiDecoderMemberCode
  abiDecoderDynamic abiDecoderCoherence abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
  abiDecoderArraySetupInputs abiDecoderTypedContract abiDecoderReentry abiEncoder compileEnv
  fragExec venomExecSemantics emitHelperProps

(* ===== Windows ===== *)

(* Actual source loads and bounded child windows for noncanonical members. *)

Definition abi_decode_member_offset_def:
  abi_decode_member_offset at bs ao =
    if is_dynamic at then abi_head_word (DROP ao bs) else ao
End

Theorem abi_head_word_bytes:
  word_of_bytes T (0w:256 word) (TAKE 32 bs) = n2w (abi_head_word bs)
Proof
  simp[abi_head_word_def, dec_number_def, dest_NumV_def]
QED

Theorem abi_valid_member_head:
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs ==>
  let ao = SUM (MAP abi_member_head_size pre) in
  ao + abi_member_head_size at <= LENGTH bs /\
  vyper_decode_valid_enc at (abi_decode_member_bytes at bs (DROP ao bs)) /\
  vyper_decode_valid_enc_tuple ats bs (DROP (ao + abi_member_head_size at) bs)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_valid_members_suffix >> strip_tac >>
  drule abi_valid_member_cons >> strip_tac >>
  asm_simp_tac (srw_ss()) [DROP_DROP_T, ADD_COMM, Excl "vyper_decode_valid_enc_def"] >>
  fs[LENGTH_DROP, DROP_DROP_T, Excl "vyper_decode_valid_enc_def"] >> decide_tac
QED

Theorem abi_valid_static_member_window:
  ~is_dynamic at /\ ao + static_length at <= LENGTH bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  ao + LENGTH (abi_decode_member_bytes at bs (DROP ao bs)) <= LENGTH bs /\
  sb + ao < dimword (:256) /\
  mem_bytes_at (sb + ao) (LENGTH (abi_decode_member_bytes at bs (DROP ao bs)))
    (abi_decode_source opc s) = abi_decode_member_bytes at bs (DROP ao bs)
Proof
  strip_tac >> `static_length at <= LENGTH (DROP ao bs)` by (simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac (srw_ss()) [abi_decode_member_bytes_def, LENGTH_TAKE_EQ] >> conj_tac
  >- decide_tac >>
  mp_tac (Q.INST [`off` |-> `ao:num`, `n` |-> `static_length at`] abi_decode_source_window) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_valid_dynamic_member_window:
  is_dynamic at /\ ao + 32 <= LENGTH bs /\
  vyper_decode_valid_enc at (DROP (abi_head_word (DROP ao bs)) bs) /\
  (!elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_head_word (DROP ao bs) + 32 <= LENGTH bs /\
  sb + abi_head_word (DROP ao bs) < dimword (:256) /\
  abi_decode_load opc (n2w (sb + ao):bytes32) s = n2w (abi_head_word (DROP ao bs)) /\
  mem_bytes_at (sb + abi_head_word (DROP ao bs))
    (LENGTH (DROP (abi_head_word (DROP ao bs)) bs)) (abi_decode_source opc s) =
    DROP (abi_head_word (DROP ao bs)) bs
Proof
  strip_tac >> drule_all abi_valid_dynamic_head_min >> strip_tac >>
  `abi_head_word (DROP ao bs) + 32 <= LENGTH bs` by (fs[LENGTH_DROP] >> decide_tac) >>
  `sb + ao < dimword (:256) /\ sb + abi_head_word (DROP ao bs) < dimword (:256)` by decide_tac >>
  `mem_bytes_at (sb + ao) 32 (abi_decode_source opc s) = TAKE 32 (DROP ao bs)` by
    (mp_tac (Q.INST [`off` |-> `ao:num`, `n` |-> `32`] abi_decode_source_window) >> simp[]) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes, abi_head_word_bytes] >>
  mp_tac (Q.INST [`off` |-> `abi_head_word (DROP ao bs)`,
    `n` |-> `LENGTH (DROP (abi_head_word (DROP ao bs)) bs)`] abi_decode_source_window) >>
  simp[LENGTH_DROP]
QED

Theorem abi_valid_member_window:
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  let ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      data = abi_decode_member_bytes at bs (DROP ao bs) in
  vyper_decode_valid_enc at data /\ off + LENGTH data <= LENGTH bs /\ sb + off < dimword (:256) /\
  mem_bytes_at (sb + off) (LENGTH data) (abi_decode_source opc s) = data /\
  (is_dynamic at ==> abi_decode_load opc (n2w (sb + ao):bytes32) s = n2w off)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic at`
  >- (qpat_assum `is_dynamic at` (fn th =>
        RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, abi_decode_member_bytes_def, abi_member_head_size_def]) >>
        assume_tac th) >>
      drule_all abi_valid_dynamic_member_window >> strip_tac >>
      asm_simp_tac (srw_ss()) [abi_decode_member_offset_def, abi_decode_member_bytes_def,
        abi_member_head_size_def, LENGTH_DROP, Excl "vyper_decode_valid_enc_def"] >>
      fs[LENGTH_DROP, Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"] >> decide_tac) >>
  `SUM (MAP abi_member_head_size pre) + static_length at <= LENGTH bs` by
    (qpat_x_assum `_ + abi_member_head_size at <= _` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  drule_all abi_valid_static_member_window >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_member_offset_def]
QED

(* ===== Entry ===== *)

(* Actual emitted member setup establishes typed, source-valid child inputs.
   Dynamic zero-length fixed arrays are explicit; their offsets are not bounded
   by validity alone. Recursive child execution is proved separately. *)

Theorem abi_valid_member_child_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap before /\
  abi_decoder_address_frame next before after /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  off + childlen <= len /\ vo + childsz <= outsz /\
  eval_operand childsrc after = SOME (n2w (sb + off)) /\
  eval_operand childdst after = SOME (n2w (d + vo)) ==>
  abi_decoder_ranges opc hi childsrc childdst (sb + off) childlen (d + vo) childsz b cap after
Proof
  strip_tac >> drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `len`, `outsz`, `sb`, `src`] >>
  asm_simp_tac arith_ss [] >> decide_tac
QED

Theorem abi_valid_member_entry:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. vyper_decode_valid_enc at childbs /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec at childbs) v /\
    abi_decoder_ranges opc hi (FST ops) (SND ops) (sb + off) (LENGTH childbs)
      (d + vo) (type_memory_bytes ce ty) b cap prepared /\
    mem_bytes_at (sb + off) (LENGTH childbs) (abi_decode_source opc prepared) = childbs /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  SUBGOAL_THEN ``is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size pre)):bytes32) initial =
      n2w (abi_decode_member_offset (vyper_to_abi_type env ty) bs
        (SUM (MAP abi_member_head_size pre))) /\
    sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre)) < dimword (:256)`` assume_tac
  >- (strip_tac >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size pre)`,
    `dyn` |-> `is_dynamic (vyper_to_abi_type env ty)`, `st'` |-> `ready`,
    `payload_off` |-> `abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))`] abi_decode_member_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb +
     abi_decode_member_offset (vyper_to_abi_type env ty) bs (SUM (MAP abi_member_head_size pre))))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[abi_decode_member_offset_def, Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"]) >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  drule_all abi_valid_member_child_ranges >> strip_tac >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

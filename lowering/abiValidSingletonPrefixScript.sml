Theory abiValidSingletonPrefix
Ancestors
  abiValidSingletonArray abiValidSingletonSetup abiDecoderPrefixPre abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiCanonicalHeadSize
  abiCanonicalHeadSize abiDecoderArrayInitReentry compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic abiDecoderArraySetupInputs abiDecoderArraySetupInputs
  abiDecoderDynamicLoopSetup abiValidSingletonReentry abiValidSingletonReentry
  abiDecoderSingletonSetup abiDecoderArraySetupCode abiDecoderAllocation abiDecoderArrayInitExec
  abiDecoderLoop abiEncoder fragExec venomExecSemantics pair

(* ===== Input ===== *)

(* Pure input observations for a dynamic singleton whose child has a canonical
   prefix. The enclosing singleton's offset may be any source-valid value. *)

Definition abi_valid_singleton_prefix_pre_def:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    is_dynamic (vyper_to_abi_type env ty) /\
    vyper_decode_valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
    dec (Tuple [vyper_to_abi_type env ty]) bs = ListV [av] /\
    abi_head_word bs <= LENGTH bs /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH (DROP (abi_head_word bs) bs) /\
    TAKE (LENGTH (enc (vyper_to_abi_type env ty) av)) (DROP (abi_head_word bs) bs) =
      enc (vyper_to_abi_type env ty) av /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi
End

Theorem abi_valid_singleton_dynamic_load:
  is_dynamic at /\ vyper_decode_valid_enc (Tuple [at]) bs /\ dec (Tuple [at]) bs = ListV [av] /\
  abi_head_word bs <= LENGTH bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  32 <= LENGTH bs /\ abi_decode_load opc (n2w sb:bytes32) s = n2w (abi_head_word bs) /\
  sb + abi_head_word bs < dimword (:256) /\
  mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source opc s) = DROP (abi_head_word bs) bs
Proof
  strip_tac >> drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (irule abi_decode_source_prefix_window >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >> conj_tac
  >- decide_tac >>
  mp_tac (Q.INST [`off` |-> `abi_head_word bs`,
    `n` |-> `LENGTH (DROP (abi_head_word bs) bs)`] abi_decode_source_window) >>
  simp[LENGTH_DROP]
QED

Theorem abi_valid_singleton_prefix_setup_pre:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap s ==>
  abi_valid_singleton_setup_pre st src dst opc hi sb d (abi_head_word bs)
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  simp_tac bool_ss [abi_valid_singleton_prefix_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_valid_singleton_dynamic_load >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_setup_pre_def, abi_decoder_prune_fresh,
    abi_decoder_prune_eval, abi_decoder_prune_load] >>
  Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `h` >> asm_simp_tac bool_ss [] >> decide_tac
QED

(* ===== Ready ===== *)

(* Transport an arbitrary singleton child window through its emitted prefix. *)

Theorem abi_decoder_suffix_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\ offset <= len /\
  eval_operand childsrc s = SOME (n2w (sb + offset)) /\
  eval_operand childdst s = SOME (n2w d) ==>
  abi_decoder_ranges opc hi childsrc childdst (sb + offset) (len - offset)
    d outsz b cap s
Proof
  strip_tac >> irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `len`, `outsz`, `sb`, `src`] >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem abi_valid_singleton_prefix_child_pre:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap before /\
  abi_decoder_address_frame st.cs_next_var before after /\
  st.cs_next_var <= ready.cs_next_var /\
  abi_decoder_reservation ready.cs_next_id last b cap before /\
  abi_decoder_operand_live ready.cs_next_var childsrc /\
  abi_decoder_operand_live ready.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_head_word bs)) /\
  eval_operand childdst after = SOME (n2w d) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    ready last childsrc childdst opc hi (sb + abi_head_word bs) d b cap
    (abi_decoder_prune_vars ready.cs_next_var after)
Proof
  simp_tac bool_ss [abi_valid_singleton_prefix_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_decoder_ranges_def] >>
  drule_all abi_valid_singleton_dynamic_load >> strip_tac >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_reservation >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
     (abi_decode_source opc after) = DROP (abi_head_word bs) bs` by
    asm_simp_tac bool_ss [] >>
  `abi_decoder_ranges opc hi childsrc childdst (sb + abi_head_word bs)
     (LENGTH (DROP (abi_head_word bs) bs)) d (type_memory_bytes ce ty) b cap after` by
    (simp_tac bool_ss [LENGTH_DROP] >> irule abi_decoder_suffix_ranges >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dst`, `src`] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_recursive_pre_from_prefix >> simp[]
QED

(* ===== Entry ===== *)

(* Actual singleton prefix execution establishes the recursive child's input. *)

Theorem abi_valid_singleton_prefix_entry:
  abi_decode_singleton_setup dst src opc hi st = ((childsrc,childdst),ready) /\
  fn_has_code st ready func /\
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      ready last childsrc childdst opc hi (sb + abi_head_word bs) d b cap
      (abi_decoder_prune_vars ready.cs_next_var prepared) /\
    abi_decoder_budget first last b cap prepared /\ first <= ready.cs_next_id /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_valid_singleton_prefix_pre_def, abi_decoder_ranges_def,
       Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  drule abi_valid_singleton_setup_live >> simp_tac bool_ss [FST, SND] >> strip_tac >>
  `first <= ready.cs_next_id` by decide_tac >>
  `abi_decoder_reservation ready.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  drule_all abi_valid_singleton_prefix_setup_pre >> strip_tac >>
  drule_all abi_valid_singleton_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_valid_singleton_prefix_child_pre >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

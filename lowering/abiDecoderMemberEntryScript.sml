(* Canonical member pointer inputs and recursive preconditions after address setup.
   TOP-LEVEL: abi_decoder_member_pre_address.
   Helper: canonical pointer load, guard and offset agreement. *)
Theory abiDecoderMemberEntry
Ancestors
  abiDecoderMemberInputs abiDecoderMemberSlice abiDecoderMembers
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiCanonicalLoad abiDecodeRanges vyperABI compileEnv valueEncoding contractABI
  venomState words list rich_list arithmetic

Theorem abi_decoder_canonical_member_inputs:
  has_types (pre ++ aty::post) (pvs ++ av::avs) /\ LENGTH pre = LENGTH pvs /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs))))
    (abi_decode_source opc s) = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::avs))) < dimword (:256) ==>
  (is_dynamic aty ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size pre)) : bytes32) s =
      n2w (head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)) /\
    sb + (head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)) < dimword (:256)) /\
  abi_tuple_child_offset (pre ++ aty::post) (pvs ++ av::avs) (LENGTH pre) =
    if is_dynamic aty then
      head_lengths (pre ++ aty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs)
    else SUM (MAP abi_member_head_size pre)
Proof
  strip_tac >>
  `TAKE (LENGTH pre) (pvs ++ av::avs) = pvs` by
    (qpat_assum `LENGTH pre = LENGTH pvs`
      (fn th => pure_rewrite_tac [th, TAKE_LENGTH_APPEND]) >> REFL_TAC) >>
  conj_tac
  >- (strip_tac >> drule_all canonical_member_offset_load >> strip_tac >>
      drule_all canonical_member_ranges >> simp_tac bool_ss [LET_THM] >> strip_tac >>
      asm_simp_tac bool_ss [] >> gvs[head_lengths_acc, Excl "enc_def"] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_tuple_child_offset_append]
QED

Theorem abi_decoder_member_pre_address:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap before /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) (abi_decode_source opc before) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  abi_decoder_address_frame next before after /\ next <= child_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  abi_decoder_reservation child_st.cs_next_id last b cap before /\
  abi_decoder_operand_live child_st.cs_next_var childsrc /\
  abi_decoder_operand_live child_st.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)) (preavs ++ av::avs) (LENGTH pretys))) /\
  eval_operand childdst after = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    child_st last childsrc childdst opc hi
    (sb + abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))
    (d + SUM (MAP (type_memory_bytes ce) pretys)) b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live child_st.cs_next_var src /\
   abi_decoder_operand_live child_st.cs_next_var dst /\
   abi_decoder_operand_live child_st.cs_next_var hi` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_reservation >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `fresh_vars_wrt child_st (abi_decoder_prune_vars child_st.cs_next_var after)`
    by irule abi_decoder_prune_fresh >>
  `abi_decoder_reservation child_st.cs_next_id last b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)` by simp[] >>
  `abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
      (ListV (preavs ++ av::avs))))
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap
    (abi_decoder_prune_vars child_st.cs_next_var after)`
    by gvs[abi_decoder_prune_ranges, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))))
    (abi_decode_source opc (abi_decoder_prune_vars child_st.cs_next_var after)) =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs))`
    by gvs[Excl "enc_def"] >>
  `eval_operand childsrc (abi_decoder_prune_vars child_st.cs_next_var after) = SOME (n2w (sb +
    abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
      (preavs ++ av::avs) (LENGTH pretys))) /\
   eval_operand childdst (abi_decoder_prune_vars child_st.cs_next_var after) =
    SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys)))`
    by gvs[abi_decoder_prune_eval, Excl "enc_def"] >>
  drule_all (Q.INST [`s` |-> `abi_decoder_prune_vars child_st.cs_next_var after`]
    abi_decoder_member_pre) >> simp[]
QED

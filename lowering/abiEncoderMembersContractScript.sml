(* Recursive member-list contract: all incoming conditions are data, layout or resources. *)
Theory abiEncoderMembersContract
Ancestors
  abiEncoderMembersDefs abiEncoderInput abiEncoderTuple abiEncoderCorrect abiCanonicalWindows
  abiDecodeRanges abiEncoder abiDecoderEffect abiDecoderAllocation abiDecoderLoop
  abiDecoderReentry abiDecoderContract fragExec compileEnv valueEncoding contractABI venomState
  words list arithmetic

Definition abi_encoder_members_inv_def:
  abi_encoder_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap s <=>
    abi_encoder_members_pre infos tys avs st src dst sb so d output_size b cap s /\
    has_types pre pvs /\ hl = head_lengths (pre++tys) 0 /\
    ho = SUM (MAP abi_member_head_size pre) /\
    LENGTH (enc (Tuple (pre++tys)) (ListV (pvs++avs))) <= output_size /\
    abi_encoder_tuple_prefix hl pre pvs d s.vs_memory /\
    abi_encoder_cursor active dyn_ptr site slot first lo st
      (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) s /\
    (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
    abi_decoder_budget first last b cap s /\ first <= st.cs_next_id /\ lo <= st.cs_next_id /\
    st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts
End

Definition abi_encoder_members_correct_def:
  abi_encoder_members_correct infos <=>
    !tys avs pre pvs active dyn_ptr site slot first last lo st end_st limit_st src dst sb so ho d hl
      output_size b cap initial out func ctx.
    EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
    compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
    fn_has_code st end_st func /\
    (st.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_encoder_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
      src dst sb so ho d hl output_size b cap initial /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
    ?t. abi_encoder_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
        end_st limit_st src dst sb (so+abi_encoder_member_span infos)
        (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
      abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
        limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
End

Theorem abi_encoder_members_empty_types:
  abi_encoder_input (AbiComplex []) (Tuple tys) (ListV avs) sb capacity mem ==>
  tys = [] /\ avs = []
Proof
  simp[abi_encoder_complex_input_iff, abi_encoder_tuple_type_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_members_correct_empty:
  abi_encoder_members_correct []
Proof
  simp_tac bool_ss [abi_encoder_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_assum `abi_encoder_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  drule abi_encoder_members_empty_types >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >>
  gvs[Excl "enc_def"] >> qexists_tac `initial` >>
  asm_simp_tac (srw_ss()) [abi_encoder_member_span_def, abi_decoder_effect_refl, abi_decode_sim_refl]
QED

Theorem abi_encoder_members_run:
  abi_encoder_members_correct infos /\ EVERY (\(ei,_,_,_). abi_encoder_correct ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_encoder_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_encoder_members_correct _` (mp_tac o PURE_REWRITE_RULE [abi_encoder_members_correct_def]) >>
  disch_then (qspecl_then [`tys`, `avs`, `pre`, `pvs`, `active`, `dyn_ptr`, `site`, `slot`,
    `first`, `last`, `lo`, `st`, `end_st`, `limit_st`, `src`, `dst`, `sb`, `so`, `ho`, `d`, `hl`,
    `output_size`, `b`, `cap`, `initial`, `out`, `func`, `ctx`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

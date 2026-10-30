(* A completed actual-source member preserves the enclosing source and inputs. *)
Theory abiDecoderValidMemberObservations
Ancestors
  abiDecoderMemberFrames abiDecoderEffect abiDecodeRanges compileEnv
  venomState words list arithmetic

Theorem abi_decoder_valid_member_after_head:
  abi_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    (d + SUM (MAP (type_memory_bytes ce) pretys)) (type_memory_bytes ce ty) b cap initial after_head /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi_op /\ st.cs_next_var <= end_st.cs_next_var ==>
  abi_decoder_ranges opc hi_op src dst sb (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))) b cap after_head /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc after_head) = bs /\
  fresh_vars_wrt limit_st after_head /\ abi_decoder_budget first last b cap after_head /\
  abi_decoder_operand_live end_st.cs_next_var src /\ abi_decoder_operand_live end_st.cs_next_var dst /\
  abi_decoder_operand_live end_st.cs_next_var hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `st.cs_next_var`, `new_next` |-> `end_st.cs_next_var`,
    `cell` |-> `d + SUM (MAP (type_memory_bytes ce) pretys)`, `sz` |-> `type_memory_bytes ce ty`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `outsz` |-> `SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys))`,
    `before` |-> `initial:venom_state`, `after` |-> `after_head:venom_state`,
    `bytes` |-> `bs:word8 list`] abi_decoder_member_observations) >>
  impl_tac >- asm_simp_tac arith_ss [MAP_APPEND, SUM_APPEND, MAP, SUM] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

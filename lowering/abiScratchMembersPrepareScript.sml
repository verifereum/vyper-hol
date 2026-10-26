(* Enter a member by running the compiler's actual source-address ADD.
   TOP-LEVEL: abi_scratch_members_prepare retains the processed prefix and
   cursor, and establishes the child's complete physical buffer contract. *)
Theory abiScratchMembersPrepare
Ancestors
  abiScratchMembersState abiScratchMembersPre abiScratchMembersSource abiScratchEncoderContract
  abiEncoderMembersDefs abiEncoderAddressReach abiEncoderTuplePrefix abiEncoderInput
  abiScratchAddress abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderLoop emitHelperProps compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_members_prepare:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var ==>
  ?ready. abi_scratch_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
      pre pvs active dyn_ptr site slot first last lo prepared limit_st
      src dst sb so ho d hl output_size b cap ready /\
    abi_scratch_input ei ty av prepared elem_src dst (sb+so) mem_sz d output_size first last b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_members_inv_layout >> strip_tac >>
  `LENGTH (enc ty av) <= output_size` by (Cases_on `dyn` >> fs[] >> decide_tac) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  `eval_operand src initial = SOME (n2w sb)` by fs[abi_scratch_members_pre_def] >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `src`, `rhs` |-> `Lit (n2w so)`,
    `st'` |-> `prepared`, `out` |-> `elem_src`, `a` |-> `n2w sb:bytes32`, `b` |-> `n2w so:bytes32`]
    abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand elem_src ready = SOME (n2w (sb+so))` by fs[word_add_n2w] >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`, `infos` |-> `(ei,abi_sz,mem_sz,dyn)::infos`,
    `tys` |-> `ty::tys`, `avs` |-> `av::avs`, `sz` |-> `output_size:num`]
    abi_scratch_members_pre_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`actual` |-> `ready:venom_state`,
    `off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `prepared:compile_state`, `s` |-> `ready:venom_state`]
    abi_scratch_members_child_buffer) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `s` |-> `initial:venom_state`,
    `t` |-> `ready:venom_state`] abi_scratch_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_tuple_prefix hl pre pvs d ready.vs_memory` by
    (qpat_assum `abi_decoder_address_frame _ _ _` (fn th =>
       assume_tac (CONJUNCT1 (CONJUNCT2 (PURE_REWRITE_RULE [abi_decoder_address_frame_def] th)))) >>
     gvs[Excl "enc_def"]) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexists_tac `ready` >> asm_simp_tac bool_ss [abi_scratch_members_inv_def] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch member preparation not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersPrepare");

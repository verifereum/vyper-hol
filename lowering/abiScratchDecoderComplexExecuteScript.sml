(* Execute a DecComplex guard and its actual noncanonical member slices.
   TOP-LEVEL: abi_scratch_decoder_complex_execute. *)
Theory abiScratchDecoderComplexExecute
Ancestors
  abiScratchDecoderContract abiScratchDecoderAddress abiScratchAfterAddress
  abiScratchDecoderComplexInputs abiValidMembers abiDecoderComplexCode abiDecoderComplexGuard abiDecoderComplexHead abiDecoderMemberInfos
  abiScratchDecoderMemberCons abiScratchDecoderMembersContract abiDecoderMembers abiDecoderValidContract
  abiDecoderArraySetupInputs abiDecoderArrayBody abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderReentry abiDecoderAllocation
  abiDecoderLoop abiDecoderTypedContract abiDecoderContract abiDecodeRanges
  abiEncoder compileEnv valueEncoding vyperABI contractABI fragExec
  venomState venomExecSemantics words list arithmetic

Theorem abi_scratch_decoder_complex_execute:
  LIST_REL (abi_scratch_decoder ce env sf) tys tvs /\
  compile_abi_decode_to_buf dst src opc hi (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    st = ((),final) /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. tuple_in_memory vs tvs d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_complex_guard_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_trace >> strip_tac >>
  rename1 `abi_decode_complex_head_guard src hi _ st = ((),middle)` >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ first <= middle.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `head_sz` |->
    `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys)`]
    abi_decode_complex_head_guard_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `new_next` |-> `middle.cs_next_var`, `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `SUM (MAP (type_memory_bytes ce) tys)`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_address_observations) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_scratch_decoder_members_list >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [MAP, SUM, APPEND, ADD_CLAUSES]
    (Q.INST [`st` |-> `middle`, `initial` |-> `prepared:venom_state`,
      `pretys` |-> `[]`]
      abi_scratch_decoder_members_run)) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Once abi_decoder_members_def, Excl "enc_def"] >>
  strip_tac >> rename1 `tuple_in_memory vs tvs d actual.vs_memory` >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (SUM (MAP (type_memory_bytes ce) tys)) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d`, `final.cs_next_id`, `middle.cs_next_id`,
       `middle.cs_next_var`, `SUM (MAP (type_memory_bytes ce) tys)`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_COMPLEX_EXECUTE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical complex execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderComplexExecute");


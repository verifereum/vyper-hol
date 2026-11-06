Theory calldataScratchArrayCompletePtr
Ancestors
  calldataScratchLoopPtr normalizationPrefixPtr pred_set
  abiScratchDecoderLoopContext abiDecoderReentry ptrDiscipline
  abiScratchDecoderLoopInvariant abiDecoderValidArrayMemory abiDecoderExecution bodyPtrDefs
  abiDecoderLoop

Theorem calldata_scratch_array_loop_complete_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var q) src (Var root)
    CALLDATALOAD (Lit 0w) hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w)
    (Var q) src (Var root) sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr 0 s /\
  fn_inst_ids_distinct func /\
  ptr_covers G tn root s (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q s 32 /\ DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  DISJOINT {a | d <= a /\ a < d+32} tn.t_mem /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?t H u.
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
      first last lo hi next limit_st b cap initial exit_lbl (LENGTH vs) t /\
    abi_decode_sim ctx func s t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem) /\
    ptr_covers H u root t (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    ptr_covers H u q t 32 /\
    DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\
    DISJOINT {a | d <= a /\ a < d+32} u.t_mem /\ DISJOINT P u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\ allocas_from lower t /\
    (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!k a. k IN abi_decoder_ids first last /\ ~(k IN abi_decoder_ids lo hi) /\
      FLOOKUP s.vs_allocas k = SOME (a,32) ==>
      FLOOKUP t.vs_allocas k = SOME (a,32) /\ mload a t = mload a s) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`j` |-> `0`, `P` |-> `P UNION {a | d <= a /\ a < d+32}`]
    calldata_scratch_loop_finite_prefix_ptr) >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    asm_simp_tac (srw_ss()) [DISJOINT_UNION])) >>
  strip_tac >>
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _` kall_tac >>
  rename1 `abi_decode_sim ctx func s h` >>
  suspend "exit"
QED

Resume calldata_scratch_array_loop_complete_ptr[exit]:
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (`abi_decoder_operand_live next src` by fs[abi_scratch_decoder_loop_data_def] >>
     qpat_assum `abi_decoder_operand_live next src` mp_tac >>
     qpat_assum `!x. abi_decoder_older_vars next x ==> _` mp_tac >>
     qpat_assum `op_taint tn src = {}` mp_tac >>
     qpat_assum `op_prov G src = NONE` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `src` >> simp[abi_decoder_operand_live_def, op_taint_def, op_prov_def] >>
     metis_tac[SPECIFICATION]) >>
  mp_tac (Q.INST [`s` |-> `h`, `G` |-> `H`, `tn` |-> `u`,
    `P` |-> `P UNION {a | d <= a /\ a < d+32}`]
    calldata_scratch_loop_exit_ptr) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  suspend "assemble"
QED

Resume calldata_scratch_array_loop_complete_ptr[assemble]:
  qhdtm_x_assum `abi_decoder_recursive_loop_compiled` kall_tac >>
  qhdtm_x_assum `abi_scratch_decoder_loop_data` kall_tac >>
  `DISJOINT {a | d <= a /\ a < d+32} u'.t_mem /\
   DISJOINT P u'.t_mem /\ DISJOINT {a | slot <= a /\ a < slot+32} u'.t_mem` by
    fs[DISJOINT_UNION] >>
  `mem_word_at d t.vs_memory = n2w (LENGTH vs)` by
    fs[abi_scratch_decoder_loop_inv_def, abi_decoder_valid_array_memory_def] >>
  `!mem. mem_agree_outside u'.t_mem t.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem` by
    (match_mp_tac robust_dynarray_clean_count_assemble >> asm_simp_tac bool_ss []) >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory` by
    (first_assum irule >> simp[mem_agree_outside_def]) >>
  `abi_decode_sim ctx func s t` by
    (irule abi_decode_sim_trans >> qexists_tac `h` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`t`,`H'`,`u'`] >> asm_simp_tac bool_ss [] >>
  suspend "site_frame"
QED

Resume calldata_scratch_array_loop_complete_ptr[site_frame]:
  qpat_assum `!k a. _ /\ _ /\ FLOOKUP h.vs_allocas k = _ ==> _` mp_tac >>
  qpat_assum `!k a. _ /\ _ /\ FLOOKUP s.vs_allocas k = _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED

Finalise calldata_scratch_array_loop_complete_ptr

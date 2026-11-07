Theory calldataScratchArrayPtr
Ancestors
  calldataScratchTuplePtr decoderArraySetupPtr decoderScratchLoopPtr
  abiScratchDecoderArrayIteration abiScratchDecoderArraySetup
  abiDecoderArraySetupCode abiScratchAfterAddress abiDecoderProtectedScratch
  abiScratchDecoderTransport abiDecoderCoherence abiDecoderValidArraySetupInputs
  abiDecoderValidArrayMemory abiDecoderContract abiDecoderReentry venomState
  abiScratchDecoderContract compileEnv exprLowering abiDecoderArraySlice words
  fragExec abiDecoderDynamicLoopSetup list exprLoweringProps emitHelperProps
  abiDecoderArraySetupInputs abiDecoderLoop entrySinkExtraction
  abiEncoder ptrDiscipline abiDecoderArrayInitExec abiScratchDecoderTuple
  decoderGhostFramePtr abiDecoderAllocation abiScratchEffect
  abiScratchDecoderLoopInput abiScratchDecoderLoopInvariant

Theorem calldata_scratch_array_body_ptr:
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
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  lookup_var q initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  slot + 32 < dimword (:256) /\ j < dimword (:256) /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q initial 32 /\
  DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  site IN abi_decoder_ids first last /\
  ~(site IN abi_decoder_ids middle.cs_next_id end_st.cs_next_id) /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_operand_live st.cs_next_var (Var q) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual H u.
    val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
      val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) mem) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\
    op_taint u (FST ops) = {} /\ op_prov H (FST ops) = NONE /\
    lookup_var q actual = SOME (n2w slot) /\ mload slot actual = n2w j /\
    ptr_covers H u root actual (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    ptr_covers H u q actual 32 /\
    DISJOINT {a | slot <= a /\ a < slot + 32} u.t_mem /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual /\
    u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    allocas_from lower actual /\
    (!site slot. site IN abi_decoder_ids first last /\
      ~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
      FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      mload slot actual = mload slot initial) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `first <= middle.cs_next_id /\ middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
   eval_operand (Var q) initial = SOME (n2w slot) /\
   mload (w2n (n2w slot:bytes32)) initial = n2w j` by
    simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, eval_operand_def] >>
  drule_all abi_scratch_decoder_array_setup_sequence >> strip_tac >>
  `eval_operand src initial = SOME (n2w sb) /\
   lookup_var root initial = SOME (n2w d) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_scratch_decoder_ranges_def, eval_operand_def] >>
  `not_fresh_at st q /\ not_fresh_at st root /\
   (!x. src = Var x ==> not_fresh_at st x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     Cases_on `src` >> fs[]) >>
  drule_all abi_decoder_valid_dynarray_values >> strip_tac >>
  `j < maxn` by decide_tac >>
  `32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
      type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (`j * type_memory_bytes ce ty + type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty`
       by simp[abi_decoder_array_cell_capacity] >>
     simp_tac bool_ss [Once type_memory_bytes_def] >> decide_tac) >>
  `d + 32 + j * type_memory_bytes ce ty < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  `!a. slot <= a /\ a < slot + 32 ==> a NOTIN tn.t_mem` by ASM_SET_TAC[] >>
  drule_all calldata_array_element_setup_original_pc_ptr >>
  disch_then (qspecl_then [`ARB`,`ARB`,`PG`,`ARB`,`D`] strip_assume_tac) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `LENGTH (emitted_insts st middle) + initial.vs_inst_idx = LENGTH middle.cs_current_insts` by
    (qpat_assum `inst_extends st middle` mp_tac >>
     simp_tac list_ss [inst_extends_def] >> strip_tac >> simp[]) >>
  qabbrev_tac `prepared = t with vs_inst_idx := LENGTH middle.cs_current_insts` >>
  `ptr_covers H u child prepared (type_memory_bytes ce ty)` by fs[Abbr `prepared`] >>
  `abi_scratch_decoder_array_setup_post ce env ty bs j middle ops sb d
     st.cs_next_var limit_st initial prepared` by simp[Abbr `prepared`] >>
  qpat_x_assum `abi_scratch_decoder_array_setup_post _ _ _ _ _ _ _ _ _ _ _ _ t` kall_tac >>
  qhdtm_x_assum `abi_scratch_decoder_array_setup_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_array_setup_post_def]) >>
  `abi_decode_sim ctx func initial prepared` by
    (`frag_exec ctx st middle (\s. s = initial) (\v. v = prepared) (K F)` by
       (irule frag_exec_run_inst_seq >> simp[Abbr `prepared`] >>
        drule_all abi_decode_array_element_setup_shape >> strip_tac >>
        fs[EVERY_CONJ] >> metis_tac[]) >>
     drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]) >>
  `prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted` by
    (drule_all abi_decode_array_element_setup_shape >> strip_tac >>
     drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
     simp[Abbr `prepared`]) >>
  suspend "child"
QED

Resume calldata_scratch_array_body_ptr[child]:
  drule abi_decode_array_element_setup_operands >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `new_next` |-> `middle.cs_next_var`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `hi_op` |-> `Lit 0w`,
    `dst` |-> `Var root`, `opc` |-> `CALLDATALOAD`]
    abi_scratch_decoder_address_observations) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST [`st` |-> `middle`,
    `s` |-> `prepared:venom_state`, `childsrc` |-> `FST (SND (ops:operand # operand # operand))`,
    `childdst` |-> `SND (SND (ops:operand # operand # operand))`,
    `dst` |-> `Var root`, `opc` |-> `CALLDATALOAD`, `hi` |-> `Lit 0w`]
    abi_scratch_decoder_array_child_input)) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  `prepared.vs_allocas = initial.vs_allocas` by simp[Abbr `prepared`] >>
  `allocas_from lower prepared` by
    (qpat_x_assum `allocas_from lower initial` mp_tac >>
     simp_tac bool_ss [allocas_from_def] >> simp[]) >>
  `DISJOINT P u.t_mem` by simp[] >>
  qpat_x_assum `SND (SND ops) = Var child`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _`
    (fn child => drule child) >>
  disch_then (drule_at (Pat `abi_scratch_decoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`limit_st`,`P`,`D`,`PG`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  strip_tac >>
  suspend "compose"
QED

Resume calldata_scratch_array_body_ptr[compose]:
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
     (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     goal_assum (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at middle x` by
    (simp[not_fresh_at_def] >> decide_tac) >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial /\
     FLOOKUP H' x = FLOOKUP G x /\ op_taint u' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at middle x` by simp[] >>
     qpat_assum `!x. _ ==> lookup_var x actual = _ /\ _`
       (qspec_then `x` assume_tac) >>
     qpat_assum `!x. _ ==> lookup_var x t = _ /\ _`
       (qspec_then `x` assume_tac) >>
     gvs[Abbr `prepared`, lookup_var_def]) >>
  `ptr_covers H' u' root actual (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
   ptr_covers H' u' q actual 32` by
    (conj_tac >> irule ptr_covers_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `u'.t_mem SUBSET tn.t_mem /\ DISJOINT {a | slot <= a /\ a < slot + 32} u'.t_mem` by
    (fs[] >> ASM_SET_TAC[]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `mload slot actual = n2w j` by
    (qpat_assum `!site slot. _ ==> FLOOKUP actual.vs_allocas site = _ /\ _`
       (qspecl_then [`site`,`slot`] assume_tac) >>
     gvs[Abbr `prepared`, mload_def]) >>
  `!site slot. site IN abi_decoder_ids first last /\
     ~(site IN abi_decoder_ids st.cs_next_id end_st.cs_next_id) /\
     FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
     FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
     mload slot actual = mload slot initial` by
    (rpt gen_tac >> strip_tac >>
     `~(site' IN abi_decoder_ids middle.cs_next_id end_st.cs_next_id)` by
       (fs[abi_decoder_ids_def] >> decide_tac) >>
     qpat_assum `!site slot. _ ==> FLOOKUP actual.vs_allocas site = _ /\ _`
       (qspecl_then [`site'`,`slot'`] mp_tac) >>
     simp[Abbr `prepared`, mload_def]) >>
  `eval_operand (FST ops) actual = SOME (n2w j)` by
    (irule abi_scratch_effect_operand >>
     qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ prepared actual`
       (fn th => irule_at Any th) >> simp[]) >>
  `op_taint u' (FST ops) = {} /\ op_prov H' (FST ops) = NONE` by
    (Cases_on `FST ops` >> simp[op_taint_def, op_prov_def] >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        not_fresh_at_def, op_taint_def, op_prov_def]) >>
  qexistsl_tac [`actual`,`H'`,`u'`] >>
  asm_simp_tac bool_ss [] >>
  metis_tac[]
QED

Finalise calldata_scratch_array_body_ptr

(* This boundary starts at the header: it does not execute the incoming jump. *)
Theorem calldata_scratch_initialized_loop_inputs:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) loop_st src (Var root) CALLDATALOAD (Lit 0w)
    sb d first last b cap s /\
  abi_decoder_valid_array_memory CALLDATALOAD bs tv vs sb d 0 s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  first <= site /\ site < last /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  eval_operand (Var q) s = SOME (n2w slot) /\
  abi_decoder_operand_live loop_st.cs_next_var (Var q) /\
  mload slot s = 0w /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w)
    (Var q) src (Var root) sb d slot first last b cap loop_st.cs_next_var s /\
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi loop_st.cs_next_var limit_st b cap s hdr 0 s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac
  >- (irule abi_scratch_decoder_loop_input >> goal_assum (drule_at Any) >>
      asm_rewrite_tac[] >> qexists_tac `site` >> asm_rewrite_tac[]) >>
  irule abi_scratch_decoder_loop_inv_init >> asm_rewrite_tac[]
QED

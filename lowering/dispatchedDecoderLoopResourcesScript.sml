Theory dispatchedDecoderLoopResources
Ancestors
  decoderArraySetupPtr decoderScratchLoopCorePtr decoderScratchLoopPtr
  abiDecoderRecursiveLoopContext abiScratchDecoderLoopContext abiDecoderExecution
  abiScratchFootprint abiScratchEncoderContract
  abiScratchDecoderArrayIteration abiScratchDecoderArraySetup
  abiDecoderArraySetupCode abiScratchAfterAddress abiDecoderProtectedScratch
  abiScratchDecoderTransport abiDecoderCoherence abiDecoderValidArraySetupInputs
  abiDecoderValidArrayMemory abiDecoderContract abiDecoderReentry venomState
  abiScratchDecoderContract compileEnv loweringStateRelDefs exprLowering abiDecoderArraySlice words
  fragExec abiDecoderDynamicLoopSetup list exprLoweringProps emitHelperProps
  abiDecoderArraySetupInputs abiDecoderLoop entrySinkExtraction
  abiEncoder ptrDiscipline abiDecoderArrayInitExec abiScratchDecoderTuple
  decoderGhostFramePtr abiDecoderAllocation abiScratchEffect
  abiScratchDecoderLoopInput abiScratchDecoderLoopInvariant

(* Specialize the position-form resource interfaces, without changing the
   source bytes or assuming a recursive decoder result. *)
fun calldata_resource th =
  SIMP_RULE bool_ss
    [cj 1 venomStateTheory.eval_operand_def, cj 1 arithmeticTheory.ADD_CLAUSES,
     cj 2 arithmeticTheory.ADD_CLAUSES]
    (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`, `src_base` |-> `0:num`] th);

Theorem calldata_decoder_array_child_resources:
  abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) st = (ops,middle) /\
  fn_has_code st middle func /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src (Var root) 0 sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  lookup_var q initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  slot + 32 < dimword (:256) /\ j < dimword (:256) /\
  ptr_covers G tn root initial (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q initial 32 /\
  DISJOINT {a | slot <= a /\ a < slot + 32} tn.t_mem /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  abi_decoder_operand_live st.cs_next_var (Var q) /\
  abi_decoder_budget first last b cap initial /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  op_taint tn src = {} /\ op_prov G src = NONE /\ allocas_from lower initial /\
  ~ctx_has_dalloca ctx /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared H u child.
    SND (SND ops) = Var child /\
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))
      (EL j vs) middle (FST (SND ops)) (Var child) CALLDATALOAD (Lit 0w) (Lit 0w) 0
      (sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))
      (d + 32 + j * type_memory_bytes ce ty) first last b cap prepared /\
    abi_decoder_budget first last b cap prepared /\ fresh_vars_wrt limit_st prepared /\
    ptr_covers H u child prepared (type_memory_bytes ce ty) /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    allocas_from lower prepared /\
    prepared.vs_allocas = initial.vs_allocas /\ prepared.vs_memory = initial.vs_memory /\
    lookup_var q prepared = SOME (n2w slot) /\ mload slot prepared = n2w j /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> lookup_var x prepared = lookup_var x initial /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
   eval_operand (Var q) initial = SOME (n2w slot) /\
   mload (w2n (n2w slot:bytes32)) initial = n2w j` by
    simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, eval_operand_def] >>
  drule_all (calldata_resource abi_scratch_decoder_array_setup_sequence) >> strip_tac >>
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
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`ARB`,`ARB`,`ARB`] strip_assume_tac) >>
  qhdtm_x_assum `frag_exec_ptr` kall_tac >>
  rename1 `op_prov H (FST ops) = NONE` >>
  `LENGTH (emitted_insts st middle) + initial.vs_inst_idx = LENGTH middle.cs_current_insts` by
    (qpat_assum `inst_extends st middle` mp_tac >>
     simp_tac list_ss [inst_extends_def] >> strip_tac >> simp[]) >>
  qabbrev_tac `prepared = t with vs_inst_idx := LENGTH middle.cs_current_insts` >>
  `ptr_covers H u child prepared (type_memory_bytes ce ty)` by fs[Abbr `prepared`] >>
  `abi_scratch_decoder_array_setup_post ce env ty bs j middle ops sb d
     st.cs_next_var limit_st initial prepared` by simp[Abbr `prepared`] >>
  qpat_x_assum `abi_scratch_decoder_array_setup_post _ _ _ _ _ _ _ _ _ _ _ _ t` kall_tac >>
  suspend "input"
QED

Resume calldata_decoder_array_child_resources[input]:
  qhdtm_x_assum `abi_scratch_decoder_array_setup_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_array_setup_post_def]) >>
  `abi_decode_sim ctx func initial prepared` by
    (`frag_exec ctx st middle (\s. s = initial) (\v. v = prepared) (K F)` by
       (irule frag_exec_run_inst_seq >> simp[Abbr `prepared`] >>
        drule_all (calldata_resource abi_decode_array_element_setup_shape) >> strip_tac >>
        fs[EVERY_CONJ] >> metis_tac[]) >>
     drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]) >>
  `prepared.vs_current_bb = middle.cs_current_bb /\
   prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted` by
    (drule_all (calldata_resource abi_decode_array_element_setup_shape) >> strip_tac >>
     drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
     simp[Abbr `prepared`]) >>
  drule (calldata_resource abi_decode_array_element_setup_operands) >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `new_next` |-> `middle.cs_next_var`,
    `len` |-> `LENGTH (bs:word8 list)`,
    `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`, `hi_op` |-> `Lit 0w`,
    `dst` |-> `Var root`, `opc` |-> `CALLDATALOAD`]
    (calldata_resource abi_scratch_decoder_address_observations)) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST [`st` |-> `middle`,
    `s` |-> `prepared:venom_state`, `childsrc` |-> `FST (SND (ops:operand # operand # operand))`,
    `childdst` |-> `SND (SND (ops:operand # operand # operand))`,
    `dst` |-> `Var root`, `opc` |-> `CALLDATALOAD`, `hi` |-> `Lit 0w`]
    (calldata_resource abi_scratch_decoder_array_child_input))) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  qexistsl_tac [`prepared`,`H`,`u`,`child`] >>
  fs[Abbr `prepared`, allocas_from_def, mload_def, lookup_var_def] >> metis_tac[]
QED

Finalise calldata_decoder_array_child_resources

Theorem calldata_resource_loop_cfg[local]:
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl id ip src opc (Lit 0w) first <=>
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl id ip src opc
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3)))
Proof
  simp[abi_decode_position_loop_cfg_def, abi_decode_loop_cfg_def,
    abi_decode_position_header_zero]
QED

Theorem calldata_decoder_loop_child_resources:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var q) src (Var root)
    CALLDATALOAD (Lit 0w) (Lit 0w) hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w) (Lit 0w)
    (Var q) src (Var root) 0 sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  fn_inst_ids_distinct func /\ j < LENGTH vs /\
  ptr_covers G tn root s (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q s 32 /\ DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx ==>
  ?prepared H u child.
    SND (SND ops) = Var child /\
    abi_scratch_decoder_input ce env sf ty tv
      (abi_decode_member_bytes (vyper_to_abi_type env ty) (DROP 32 bs)
        (DROP (j * abi_member_head_size (vyper_to_abi_type env ty)) (DROP 32 bs)))
      (EL j vs) middle (FST (SND ops)) (Var child) CALLDATALOAD (Lit 0w) (Lit 0w) 0
      (sb + (32 + abi_decode_member_offset (vyper_to_abi_type env ty) (DROP 32 bs)
        (j * abi_member_head_size (vyper_to_abi_type env ty))))
      (d + 32 + j * type_memory_bytes ce ty) first last b cap prepared /\
    abi_decoder_budget first last b cap prepared /\ fresh_vars_wrt limit_st prepared /\
    ptr_covers H u child prepared (type_memory_bytes ce ty) /\
    op_taint u (FST (SND ops)) = {} /\ op_prov H (FST (SND ops)) = NONE /\
    allocas_from lower prepared /\
    prepared.vs_allocas = s.vs_allocas /\ prepared.vs_memory = s.vs_memory /\
    lookup_var q prepared = SOME (n2w slot) /\ mload slot prepared = n2w j /\
    (!k a. FLOOKUP s.vs_allocas k = SOME (a,32) ==>
      FLOOKUP prepared.vs_allocas k = SOME (a,32) /\ mload a prepared = mload a s) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func s prepared
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule (calldata_resource abi_scratch_decoder_loop_data_facts) >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all (calldata_resource abi_decoder_recursive_compiled_facts) >> strip_tac >>
  qhdtm_assum `abi_decoder_recursive_loop_compiled`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_decoder_recursive_loop_compiled_def,
       calldata_resource_loop_cfg,
       abiDecoderExecutionTheory.abi_decode_position_header_delta_def,
       cj 1 arithmeticTheory.ADD_CLAUSES, cj 2 arithmeticTheory.ADD_CLAUSES]) >>
  qhdtm_assum `abi_scratch_decoder_loop_data`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_scratch_decoder_loop_data_def, cj 1 arithmeticTheory.ADD_CLAUSES,
       cj 1 venomStateTheory.eval_operand_def]) >>
  `abi_decoder_budget first last b cap s /\ FLOOKUP s.vs_allocas site = SOME (slot,32)` by
    fs[abi_scratch_decoder_loop_inv_def, abi_scratch_effect_def, Excl "enc_def"] >>
  `site IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot + 32 < dimword (:256)` by
    (qpat_assum `abi_decoder_budget first last b cap s` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
  `sb + LENGTH bs < dimword (:256) /\ eval_operand src initial = SOME (n2w sb)` by
    fs[abi_scratch_decoder_ranges_def, cj 1 venomStateTheory.eval_operand_def] >>
  drule_at (Pat `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`) decoder_scratch_header_ptr_core >>
  disch_then (drule_at (Pat `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`header_var`,`ctx`,`ARB`,`ARB`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> gvs[])) >> strip_tac >>
  rename1 `abi_decode_sim ctx func s h` >>
  suspend "prepare"
QED

Resume calldata_decoder_loop_child_resources[prepare]:
  `h.vs_memory = s.vs_memory` by
    (qpat_assum `h = _` (fn th => pure_rewrite_tac [th]) >>
     simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  `~MEM root [STRING #"%" (toString header_var); STRING #"%" (toString (header_var+1));
      STRING #"%" (toString (header_var+2)); STRING #"%" (toString (header_var+3))] /\
   (!x. src = Var x ==> ~MEM x [STRING #"%" (toString header_var);
      STRING #"%" (toString (header_var+1)); STRING #"%" (toString (header_var+2));
      STRING #"%" (toString (header_var+3))])` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> rpt strip_tac >>
     fs[] >> metis_tac[DECIDE ``next <= header_var ==> next <= header_var + (n:num)``]) >>
  `ptr_covers H u root h (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `allocas_from lower h` by (fs[allocas_from_def] >> metis_tac[]) >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src (Var root) 0 sb (LENGTH bs)
     d (32 + maxn * type_memory_bytes ce ty) first last b cap initial` by gvs[] >>
  drule_at (Pat `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h`)
    (calldata_resource abi_scratch_decoder_body_inputs) >>
  disch_then (drule_at (Pat `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`Var q`,`st.cs_next_var`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src (Var root) 0 sb (LENGTH bs)
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap h` by gvs[] >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD h) = bs` by
    fs[abi_decoder_valid_array_memory_def] >>
  `lookup_var q h = SOME (n2w slot) /\ j < dimword (:256)` by
    (fs[eval_operand_def] >> decide_tac) >>
  drule_all (calldata_resource abi_decoder_array_body_code) >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `h.vs_current_bb = st.cs_current_bb /\
   h.vs_inst_idx = LENGTH st.cs_current_insts /\
   DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem` by simp[] >>
  drule_all calldata_decoder_array_child_resources >> strip_tac >>
  qexistsl_tac [`prepared`,`H'`,`u'`,`child`] >>
  simp[] >>
  conj_tac >- simp[mload_def] >>
  irule abi_decode_sim_trans >> goal_assum (drule_at Any) >> simp[]
QED

Finalise calldata_decoder_loop_child_resources

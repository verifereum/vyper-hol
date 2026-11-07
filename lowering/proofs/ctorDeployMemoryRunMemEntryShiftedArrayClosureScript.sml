Theory ctorDeployMemoryRunMemEntryShiftedArrayClosure
Ancestors
 ctorDeployMemoryRunMemEntryShiftedComplex
 ctorDeployMemoryRunMemEntryShiftedIndex ASCIInumbers pred_set
 ctorDeployMemoryRunMemEntryShiftedCheckedArrayFinite
 ctorDeployMemoryRunMemEntryShiftedCheckedArrayEntry
 ctorDeployMemoryRunMemEntryShiftedCheckedArrayEdges
 ctorDeployMemoryRunMemEntryShiftedObservation ctorDeployMemoryRunMemEntryShiftedFrame
 ctorDeployMemoryFrontier ctorDeployMemoryRunMemEntryArraySteps
 ctorDeployMemoryRunMemEntryBulk ctorDeployMemoryRunMemEntryWord
 ctorAbiActualBulk abiDecoderBulkReentry abiDecoderBulkExecute abiDecoderBulk
 ctorAbiActualObservations venomState venomExecSemantics venomInst list
 abiDecoderReentryPointer ctorAbiActualWorld instIdxIndep
 ctorAbiActualArrayClosure abiDecoderFixedInputs abiDecoderFixedMemory
 abiDecoderMemberInfos rich_list vyperABI vyperTypeABI compileEnv
 ctorAbiActualArrayInvariant ctorAbiActualArrayEntry ctorAbiActualArrayContext
 ctorDeployMemoryRunMemEntryCompositeEdges
 abiDecoderLoop arithmetic ctorAbiActualArrayRun ctorAbiActualArrayLayout
 abiDecoderRecursiveLoopContext abiDecoderLoopEmit abiDecoderArrayLoopInit
 abiDecoderIndexInit abiDecoderReentry allocaFrontierBound ctorAbiActualFrame exprLowering
 abiDecoderCode abiDecoderCounters abiDecoderArraySetupCode ctorAbiActualSites
 abiDecoderRecursiveLoopLayout abiDecoderCorrectPrimitiveArray
 abiDecoderRecursiveLoopEntry abiDecoderRecursiveArray
 abiCanonicalHeadSize abiDecoderTypedContract abiDecoderContract
 abiDecoderCoherence abiEncoderRegisteredEffect fragGasPathMem allocaHistory
 valueEncodingProps valueEncoding ctorAbiActualMemory
 abiDecoderDynamicLoopSetup allocaBudgetProps venomMemDefs abiDecoderLoopRegisters

val O = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s``;

Theorem ctor_actual_array_observation_self_from:
  (^O) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot s prefix cursor s
Proof
  simp_tac bool_ss [] >> strip_tac >>
  simp[abi_encoder_registered_effect_refl]
QED

Theorem ctor_actual_array_observation_compose_from:
  (^O) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot prepared prefix cursor final ==>
  (^O) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial prefix cursor final
Proof
  simp_tac bool_ss [] >> rpt strip_tac
  >- (first_x_assum irule >> simp[] >>
      `abi_decoder_older_vars next x` by
        (fs[abi_decoder_older_vars_def, IN_DEF] >> metis_tac[LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]
QED

Theorem ctor_actual_array_observation_exit_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp[val_in_memory_dynarray, mem_word_at_eq_mload]
QED

Theorem ctor_checked_array_prefix_header_index_entry_from:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\ sb < dimword (:256) /\
  sb+32 <= LENGTH initial.vs_data_section /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb+32+LENGTH vs*asz <= h /\ h < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func initial ==>
  ?actual slot. eval_operand ip actual = SOME (n2w slot) /\
    (^O) k ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
    actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all ctor_checked_array_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial guard` >>
  `guard.vs_allocas = initial.vs_allocas /\
    guard.vs_alloca_next = initial.vs_alloca_next` by fs[abi_decoder_address_frame_def] >>
  `alloca_inv guard /\ alloca_frontier_inv_from k ctx func site guard /\
    ctor_actual_scratch func ids D N guard /\ D+N <= guard.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv_from k ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def, ctor_actual_scratch_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `eval_operand src guard = SOME (n2w sb) /\
    eval_operand dst guard = SOME (n2w d)` by fs[abi_decoder_address_frame_def] >>
  `guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `sb+32 <= LENGTH guard.vs_data_section` by simp[] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_load_def, abi_decode_source_def] >> asm_rewrite_tac[]) >>
  `abi_decoder_operand_live guard_st.cs_next_var src /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all ctor_checked_array_header_index_entry_from >>
  disch_then (qspec_then `tv` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func guard actual` >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
    guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  drule_at (Pat `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    ctor_actual_array_observation_rebase_from >>
  disch_then (qspecl_then [`initial`, `st.cs_next_var`] mp_tac) >>
  (impl_tac >- (simp[] >>
    rpt strip_tac >> irule ctor_actual_address_old_vars >>
    goal_assum (drule_at Any) >> qexists `st.cs_next_var` >> simp[])) >>
  disch_tac >>
  qexistsl [`actual`, `slot`] >> asm_simp_tac bool_ss [] >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `guard` >> simp[]) >>
  drule_all gas_path_mem_then >> simp[]
QED

val Ck = ``\ty tv.
 !r dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

val P = ``
 abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
   hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
 abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
   sb d slot b cap next prepared /\
 fn_inst_ids_distinct func /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH prepared.vs_data_section /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
 frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
 slot_id IN ctor_actual_sites func ids /\
 venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem ctor_actual_array_observation_jump_eq_from[local]:
  ((^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (jump_to lbl s)) =
  ((^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s)
Proof
  BETA_TAC >>
  pure_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def,
    alloca_next_valid_def, alloca_frontier_inv_from_def, remaining_alloca_budget_def,
    ctor_actual_scratch_def, fresh_vars_wrt_def,
    lookup_var_def, mload_def, abi_encoder_registered_effect_def] >>
  simp_tac (srw_ss()) [jump_to_def]
QED

Theorem ctor_actual_array_observation_jump_from[local]:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s ==>
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor (jump_to lbl s)
Proof
  rewrite_tac [ctor_actual_array_observation_jump_eq_from]
QED

Theorem ctor_checked_array_entry_jump_from:
  (^O) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial i i s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH prefix /\ alloca_history func s ==>
  ?h. (^O) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial i i h /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s h /\ gas_path_mem ctx func s 0 (OK h) /\
    h.vs_gas_readings = s.vs_gas_readings /\ alloca_history func h
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all ctor_checked_jump_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_actual_array_observation_jump_from >>
  disch_then (qspec_then `hdr` assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  qexists `jump_to hdr s` >> asm_simp_tac bool_ss [] >> simp[jump_to_def]
QED

Theorem ctor_checked_array_prepared_run_from:
 (^Ck) ty tv /\ ^P /\
 (^O) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
 lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH prefix /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared ==>
 ?actual.
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   (^O) k ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
     tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
   actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^O) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule ctor_actual_array_observation_self_from >> goal_assum (drule_at Any)) >>
 drule_all ctor_checked_array_entry_jump_from >>
 disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 asm "child" assume_tac >>
 drule_all ctor_checked_array_loop_finite_from >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^O) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual` by
   (irule ctor_actual_array_observation_compose_from >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> conj_tac
 >- (irule ctor_actual_array_observation_exit_from >> goal_assum (drule_at Any)) >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 asm_x "child" kall_tac >> metis_tac[gas_path_mem_then, ADD_0]
QED

Theorem ctor_actual_array_setup_ranges_from[local]:
  (^O) k ctx func site ids D N d outsz earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\
  abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
  abi_decoder_operand_live earlier hi /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + len < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256)) /\
  0 < outsz /\ D <= d /\ d + outsz <= D+N /\
  k + unit_alloca_budget ctx < dimword (:256) /\ slot_id IN ctor_actual_sites func ids ==>
  abi_decoder_ranges DLOAD hi src dst sb len d outsz slot 32 prepared /\
  slot < dimword (:256) /\ venomMemDefs$regions_disjoint (slot,32) (d,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!op w. abi_decoder_operand_live earlier op /\ eval_operand op initial = SOME w ==>
    eval_operand op prepared = SOME w` by
    (rpt strip_tac >> irule ctor_actual_array_observation_operand_from >>
     goal_assum (drule_at (Pat `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `eval_operand src prepared = SOME (n2w sb) /\
   eval_operand dst prepared = SOME (n2w d)` by metis_tac[] >>
  `hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb + len <= h /\ h < dimword (:256)` by metis_tac[] >>
  qpat_assum `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  `slot < dimword (:256)` by
    (drule_all ctor_actual_index_slot_bound_from >> simp[]) >>
  drule_all ctor_actual_sites_scratch >> strip_tac >>
  `venomMemDefs$regions_disjoint (d,outsz) (slot,32)` by
    (irule ctor_actual_region_contained >> qexistsl [`D`, `N`] >> simp[]) >>
  `d + outsz < dimword (:256)` by
    (drule_all alloca_frontier_inv_from_word_bound >> strip_tac >>
     metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
  gvs[venomMemDefsTheory.regions_disjoint_def] >>
  disj2_tac >> qexists `h` >> simp[]
QED

Theorem ctor_actual_array_setup_context_from[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
    tv vs slot_id slot initial 0 0 prepared /\
  abi_decode_index_init header_st = (ip,loop_st) /\ earlier <= loop_st.cs_next_var /\
  eval_operand ip prepared = SOME (n2w slot) /\
  abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
  abi_decoder_operand_live earlier hi /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= h /\
    h < dimword (:256)) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  k + unit_alloca_budget ctx < dimword (:256) /\ slot_id IN ctor_actual_sites func ids ==>
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot slot 32 loop_st.cs_next_var prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
    tv vs slot_id slot prepared 0 0 prepared /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `0 < type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  drule_all ctor_actual_array_setup_ranges_from >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var ip` by
    (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var dst /\
   abi_decoder_operand_live loop_st.cs_next_var hi` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `(^O) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
    tv vs slot_id slot prepared 0 0 prepared` by
    (irule ctor_actual_array_observation_self_from >> goal_assum (drule_at Any)) >>
  qpat_x_assum `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial _ _ prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
  fs[abi_decoder_recursive_loop_data_def, Excl "enc_def"]
QED

Theorem ctor_checked_dynamic_array_loop_run_from:
 (^Ck) ty tv /\
 (is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 qabbrev_tac `Child = (^Ck) ty tv` >>
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `compile_abi_decode_to_buf dst src DLOAD hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all ctor_actual_array_prefix_inputs >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all alloca_frontier_inv_from_word_bound >> strip_tac >> decide_tac) >>
 `sb < dimword (:256) /\ sb+32 <= LENGTH initial.vs_data_section` by
   (`has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
      fs[abi_decoder_metadata_def, Once vyper_to_abi_type_def] >>
    drule abi_decoder_array_encoding_head_bound >> strip_tac >> decide_tac) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 drule_all ctor_checked_array_prefix_header_index_entry_from >>
 disch_then (qspec_then `tv`
   (qx_choose_then `prepared` (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_var <= loop_st.cs_next_var` by
   (drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
    drule_all abi_decode_array_header_shape >> strip_tac >>
    drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
 drule_all ctor_actual_array_setup_context_from >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
 `?bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
   bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by simp[] >>
 pop_assum strip_assume_tac >>
 `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
   LENGTH prepared.vs_data_section` by
   (qpat_x_assum `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
    simp_tac bool_ss [] >> strip_tac >>
    fs[Once vyper_to_abi_type_def, Excl "enc_def"]) >>
 asm_x "child" mp_tac >> simp_tac bool_ss [Abbr `Child`] >> disch_tac >>
 qpat_x_assum `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ initial _ _ prepared`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 qpat_x_assum `(^O) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ prepared _ _ prepared`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 drule_all (BETA_RULE ctor_checked_array_prepared_run_from) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `ctor_actual_scratch func ids D N actual` by
   (simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
    Cases_on `inst.inst_id IN frag_ids st st'`
    >- (qpat_x_assum `ctor_actual_scratch func (frag_ids st st') _ _ actual` mp_tac >>
        simp_tac bool_ss [ctor_actual_scratch_def] >>
        disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
    `inst.inst_id NOTIN ctor_actual_sites func (frag_ids st st')` by
      simp[ctor_actual_sites_def] >>
    qpat_x_assum `abi_encoder_registered_effect _ _ initial actual` mp_tac >>
    simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
    `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
    qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
    simp_tac bool_ss [ctor_actual_scratch_def] >>
    disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum irule >>
     fs[abi_decoder_older_vars_def, not_fresh_at_def]) >>
 drule abi_decoder_array_setup_head >> strip_tac >>
 qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> simp[]
QED

Theorem ctor_checked_dynamic_array_bulk_run_from:
 ~(is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
   (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256)` by
   (drule_all alloca_frontier_inv_from_word_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs))
   st st.cs_next_id src dst DLOAD hi sb d initial.vs_alloca_next 0
   (abi_decoder_prune_vars st.cs_next_var initial)` by
   (irule ctor_actual_bulk_empty_window_pre >>
    asm_simp_tac bool_ss [vyper_to_abi_type_def] >> goal_assum (drule_at Any)) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 gnvs[Excl "enc_def"] >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next` by decide_tac >>
 drule_all (SIMP_RULE bool_ss [vyper_to_abi_type_def] ctor_checked_bulk_sequence) >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 drule_all ctor_word_path_sim >> strip_tac >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 drule_all ctor_actual_sequence_labels >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 `alloca_frontier_inv_from r ctx func site actual` by
   (irule alloca_frontier_inv_from_frame >> goal_assum (drule_at Any) >>
    qexists `site` >> simp[]) >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`]
   strip_assume_tac) >>
 qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
 simp[] >> conj_tac
 >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     simp[abi_encoder_registered_effect_def]) >>
 conj_tac
 >- (qpat_x_assum `alloca_frontier_inv_from _ _ _ _ actual` mp_tac >>
     simp[alloca_frontier_inv_from_def, remaining_alloca_budget_def]) >>
 conj_tac
 >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >> simp[ctor_actual_scratch_def]) >>
 qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
 simp[abi_decode_frame_def] >> strip_tac >> simp[] >>
 reverse conj_tac
 >- (qpat_x_assum `fresh_vars_wrt _ actual` mp_tac >> simp[fresh_vars_wrt_def]) >>
 rpt strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var x)` by
   (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
 first_x_assum drule_all >> simp[eval_operand_def, lookup_var_def]
QED

Theorem ctor_checked_dynamic_array_run_from:
 (^Ck) ty tv ==> (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 strip_tac >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
 >- (match_mp_tac ctor_checked_dynamic_array_loop_run_from >> asm_rewrite_tac[]) >>
 match_mp_tac ctor_checked_dynamic_array_bulk_run_from >> asm_rewrite_tac[]
QED

Theorem ctor_checked_array_run_from:
 (^Ck) ty tv ==> (^Ck) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd` >> BETA_TAC
 >- MATCH_ACCEPT_TAC (BETA_RULE ctor_checked_fixed_array_run_from) >>
 MATCH_ACCEPT_TAC (BETA_RULE ctor_checked_dynamic_array_run_from)
QED

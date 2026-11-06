(* Complete depth-two canonical array execution: caller bridges and iteration. *)
Theory entryReachBodyNestedArrayExecution
Ancestors
  entryReachBodyNestedBytesExecution entryReachBodyEnclosingCounter
  entryReachBodyNestedScratchTransport entryReachBodyOwnedBytesArray
  abiDecoderValidArraySetupInputs abiDecoderCorrectPrimitiveArray
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract
  valueTypingMemoryProps vyperTyping valueEncoding compileEnv
  entryReachBodyExactArrayLoop abiDecoderLoopRegisters abiDecoderExecution abiDecoderContract
  calldataRecursiveProducers abiDecoderDynamicLoopSetup abiEncoderRegisteredEffect
  fragExec exprLoweringProps calldataDynOwned abiDecoderCounters abiDecoderLoopCode
  entryReachBodyOwnedLoop entryReachBodyOwnedRegion entryReachBodyActualOwnedLoop
  entryReachBodyIndexedLoopInput abiDecoderArrayBackedge
  emitHelperProps valueEncodingProps venomExecSemantics venomState
  removeUnusedSsaProofs
  words finite_map list rich_list arithmetic

(* Extract the actual child lists and all bytes-array typing inputs directly
   from outer canonical metadata, rather than requiring a per-child contract. *)
Theorem nested_child_canonical_inputs[local]:
  abi_decoder_coherent ce env sf
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) di
    (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs ==>
  ?iavs ixs.
    EL j avs = ListV iavs /\ EL j xs = ArrayV (DynArrayV ixs) /\
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic inner)) (ArrayTV tv (Dynamic inner)) /\
    abi_decoder_metadata ce env (ArrayT ty (Dynamic inner)) (ArrayTV tv (Dynamic inner))
      (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic inner)))
      (ListV iavs) (ArrayV (DynArrayV ixs)) /\
    LENGTH ixs = LENGTH iavs /\ LENGTH ixs <= inner /\ EVERY (val_wf tv) ixs
Proof
  strip_tac >> drule_all abi_decoder_valid_array_metadata_child >> strip_tac >>
  drule abi_decoder_dynarray_metadata_shape >>
  disch_then (qx_choose_then `iavs` (qx_choose_then `ixs` strip_assume_tac)) >>
  gvs[Excl "enc_def"] >>
  qpat_assum `abi_decoder_metadata _ _ (ArrayT ty (Dynamic inner)) _ _ _ _`
    (mp_then Any strip_assume_tac abi_decoder_dynarray_values) >>
  simp[Excl "enc_def"] >>
  fs[all_have_type_EVERY, EVERY_MEM] >> rpt strip_tac >>
  irule value_has_type_memory_wf >> metis_tac[]
QED

(* Compiler phases and code containment are supplied directly by the existing
   calldata_nonbulk_parent_intervals, at both array levels. *)

(* The allocating outer invariant deliberately does not equate allocation maps
   or frontiers. Ownership and prefix memory are carried by the owned loop. *)
Definition nested_array_inv_def:
  nested_array_inv next limit_st d ncount prepared iid b cap u <=>
    entry_loop_fields prepared u /\ fresh_vars_wrt limit_st u /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
      eval_operand op u = SOME w) /\
    mem_word_at d u.vs_memory = n2w ncount /\
    entry_nested_scratch_ready iid b cap u
End

Theorem nested_array_inv_init[local]:
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w ncount /\
  entry_nested_scratch_ready iid b cap prepared ==>
  nested_array_inv next limit_st d ncount prepared iid b cap prepared
Proof
  simp[nested_array_inv_def, entry_loop_fields_def]
QED

Theorem nested_array_inv_header[local]:
  next+4 <= limit_st.cs_next_var /\
  nested_array_inv next limit_st d ncount prepared iid b cap u ==>
  nested_array_inv next limit_st d ncount prepared iid b cap
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j n u))
Proof
  simp_tac bool_ss [nested_array_inv_def] >> strip_tac >>
  drule_all abiDecoderLoopRegistersTheory.abi_decoder_header_registers >>
  disch_then (qspecl_then [`n`,`j`] strip_assume_tac) >>
  asm_simp_tac (srw_ss()) [] >>
  fs[entry_loop_fields_def, entry_nested_scratch_ready_def,
     jump_to_def, abi_decode_header_state_def, update_var_def]
QED

Theorem nested_array_inv_backedge[local]:
  next <= nv /\ nv < limit_st.cs_next_var /\ (d+32 <= q \/ q+32 <= d) /\
  nested_array_inv next limit_st d ncount prepared iid b cap u ==>
  nested_array_inv next limit_st d ncount prepared iid b cap
    (jump_to hdr (mstore q w (update_var (STRING #"%" (toString nv)) v u)))
Proof
  simp_tac bool_ss [nested_array_inv_def] >> strip_tac >>
  drule_all abi_decoder_generated_update_fresh >> disch_then (qspec_then `v` assume_tac) >>
  `!op w. abi_decoder_operand_live next op /\ eval_operand op prepared = SOME w ==>
    eval_operand op (update_var (STRING #"%" (toString nv)) v u) = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live nv op` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists_tac `next` >> simp[]) >>
     simp[abi_decoder_generated_update_operand]) >>
  `mem_word_at d (mstore q w (update_var (STRING #"%" (toString nv)) v u)).vs_memory =
    n2w ncount` by
    (asm_simp_tac (srw_ss()) [mstore_mem_word_at_disjoint, update_var_def]) >>
  asm_simp_tac (srw_ss()) [eval_operand_mstore,
    fresh_vars_wrt_def, lookup_var_def] >>
  fs[entry_loop_fields_def, entry_nested_scratch_ready_def, jump_to_def,
     mstore_def, write_memory_with_expansion_def, update_var_def,
     fresh_vars_wrt_def, lookup_var_def]
QED

Theorem nested_array_count_preserved[local]:
  entry_owned_region oid root extent d outsz s /\ 32 <= outsz /\
  oid NOTIN ids /\ alloca_inv t /\ d+32 <= cell /\
  abi_encoder_registered_effect ids [(cell,sz)] s t ==>
  mem_word_at d t.vs_memory = mem_word_at d s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (irule entryReachBodyRegisteredChildTheory.entry_registered_child_slice >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
     fs[entryReachBodyOwnedRegionTheory.entry_owned_region_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[mem_word_at_def, mem_bytes_at_def]
QED

Theorem nested_array_inv_child[local]:
  nested_array_inv next limit_st d ncount prepared iid b cap s /\
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
  entry_nested_scratch_ready iid b cap t /\ next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  entry_owned_region oid root extent d outsz s /\ 32 <= outsz /\
  oid NOTIN ids /\ alloca_inv t /\ d+32 <= cell /\
  abi_encoder_registered_effect ids [(cell,sz)] s t ==>
  nested_array_inv next limit_st d ncount prepared iid b cap t
Proof
  simp_tac bool_ss [nested_array_inv_def] >> strip_tac >>
  drule_all nested_array_count_preserved >> disch_then SUBST1_TAC >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[entryReachBodyRegisteredChildTheory.entry_registered_fields_trans] >>
  rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `next` >> simp[]) >>
  metis_tac[]
QED

Theorem nested_array_inv_inputs[local]:
  nested_array_inv next limit_st d ncount prepared iid b cap u /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz ab ac prepared /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD prepared) = bytes ==>
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb len d outsz ab ac u /\
  mem_bytes_at sb len (abi_decode_source CALLDATALOAD u) = bytes
Proof
  simp_tac bool_ss [nested_array_inv_def] >> strip_tac >>
  fs[abiDecoderTypedContractTheory.abi_decoder_ranges_def,
     abiDecoderContractTheory.abi_decode_source_def, entry_loop_fields_def] >>
  metis_tac[]
QED

(* Restore the complete outer invariant at the existing child's endpoint.
   In particular this permits the child's first allocation and later reuse. *)
Theorem nested_array_child_restore[local]:
  nested_array_inv next limit_st d ncount prepared iid b cap s /\
  entry_owned_loop_resources ctx fn site cid p oid root extent d outsz s /\
  entry_owned_loop_resources ctx fn site iid q oid root extent cell sz t /\
  abi_encoder_registered_effect {iid} [(cell,sz)] s t /\
  oid <> iid /\ cid <> iid /\ cid <> oid /\ 32 <= outsz /\
  d+32 <= cell /\ cell+sz <= d+outsz /\
  entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\
  entry_nested_scratch_ready iid b cap t /\ next <= child_next /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  nested_array_inv next limit_st d ncount prepared iid b cap t /\
  entry_owned_loop_resources ctx fn site cid p oid root extent d outsz t /\
  mload p t = mload p s
Proof
  strip_tac >>
  `alloca_inv t /\ entry_owned_region oid root extent d outsz s /\ cid <> oid` by
    fs[entryReachBodyOwnedLoopTheory.entry_owned_loop_resources_def] >>
  `oid NOTIN {iid} /\ cid NOTIN {iid}` by simp[] >>
  conj_tac
  >- (drule_all nested_array_inv_child >> simp[]) >>
  conj_tac
  >- (irule entry_enclosing_resources_restore >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  `d <= cell` by decide_tac >>
  drule_all entry_enclosing_counter_preserved >> simp[]
QED

Definition nested_array_body_def:
  nested_array_body next limit_st d ncount prepared iid b cap ip src p srcaddr j u <=>
    nested_array_inv next limit_st d ncount prepared iid b cap u /\
    eval_operand ip u = SOME p /\ mload (w2n p) u = n2w j /\
    eval_operand src u = SOME srcaddr /\
    abi_decode_load CALLDATALOAD srcaddr u = n2w ncount
End

Theorem nested_array_header_body[local]:
  nested_array_inv next limit_st d ncount prepared iid b cap s /\
  abi_decode_loop_ready hdr ip src CALLDATALOAD p srcaddr ncount j s /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  next+4 <= limit_st.cs_next_var ==>
  nested_array_body next limit_st d ncount prepared iid b cap ip src p srcaddr j
    (jump_to body_lbl (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j ncount s))
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st s` by fs[nested_array_inv_def] >>
  drule_all abi_decoder_header_registers >>
  disch_then (qspecl_then [`ncount`,`j`] strip_assume_tac) >>
  simp_tac bool_ss [nested_array_body_def] >> conj_tac
  >- (irule nested_array_inv_header >> asm_rewrite_tac[]) >>
  fs[abi_decode_loop_ready_def] >> asm_simp_tac (srw_ss()) [] >>
  fs[abi_decode_load_def, abi_decode_source_def, jump_to_def,
     abi_decode_header_state_def, update_var_def, mload_def]
QED

(* The nested producer's stable old operands and current-index output suffice
   for the actual outer backedge; no second execution witness is selected. *)
Theorem nested_array_backedge_endpoint[local]:
  nested_array_body next limit_st d ncount prepared iid b cap ip src p srcaddr j s /\
  abi_decoder_operand_live child_next ip /\ abi_decoder_operand_live child_next src /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  entry_loop_fields s t /\ eval_operand (FST ops) t = SOME (n2w j) /\
  FST ops = Var iv /\ ~t.vs_halted /\
  t.vs_current_bb = last.cs_current_bb /\
  t.vs_inst_idx = LENGTH last.cs_current_insts /\
  (?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = last.cs_current_insts ++
      abi_decode_backedge_insts last.cs_next_id iv nv ip hdr) ==>
  entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
    iv nv ip hdr src p srcaddr ncount j t
Proof
  simp_tac bool_ss [nested_array_body_def, entry_loop_child_end_def] >> strip_tac >>
  asm_rewrite_tac[] >>
  `eval_operand ip t = SOME p /\ eval_operand src t = SOME srcaddr` by metis_tac[] >>
  asm_rewrite_tac[] >>
  fs[entry_loop_fields_def, abi_decode_load_def, abi_decode_source_def]
QED

(* The initial arena budget covers both actual counter sites only when both
   are absent. Once the inner site exists, no fresh-space margin is needed. *)
Theorem nested_array_initializer_scratch[local]:
  cid <> iid /\ b <= s.vs_alloca_next /\
  (!id. id <> cid ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (if FLOOKUP s.vs_allocas cid = NONE then
     t.vs_alloca_next = s.vs_alloca_next+32 else t.vs_alloca_next = s.vs_alloca_next) /\
  (FLOOKUP s.vs_allocas iid = NONE ==>
     s.vs_alloca_next + (if FLOOKUP s.vs_allocas cid = NONE then 32 else 0) + 32 <= b+cap) /\
  (!q. FLOOKUP s.vs_allocas iid = SOME (q,32) ==> b <= q /\ q+32 <= b+cap) ==>
  entry_nested_scratch_ready iid b cap t
Proof
  Cases_on `FLOOKUP s.vs_allocas cid = NONE` >>
  simp[entry_nested_scratch_ready_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_allocas iid = FLOOKUP s.vs_allocas iid` by metis_tac[] >>
  gvs[]
QED

(* Static facts only: no per-element execution or callback is hidden here. *)
Definition nested_array_child_code_def:
  nested_array_child_code sf ce ty inner ip src dst st ops middle final
    guard_st header_st loop_st iip cnt fn limit_st iv nv hdr <=>
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner))) middle = ((),final) /\
    abi_decode_dynarray_prefix (FST (SND ops)) CALLDATALOAD (Lit 0w) inner
      (abi_embedded_static_size ce.ce_struct_fields ty) middle = ((),guard_st) /\
    abi_decode_array_header (SND (SND ops)) (FST (SND ops)) CALLDATALOAD guard_st =
      (cnt,header_st) /\ abi_decode_index_init header_st = (iip,loop_st) /\
    fn_has_code st middle fn /\ fn_has_code middle final fn /\
    (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
    (!ins. MEM ins (emitted_insts middle loop_st) ==> MEM ins (fn_insts fn)) /\
    (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    middle.cs_next_var <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
    FST ops = Var iv /\
    (?bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb /\
      bb.bb_instructions = final.cs_current_insts ++
        abi_decode_backedge_insts final.cs_next_id iv nv ip hdr)
End

Theorem nested_array_allocating_callback[local]:
  nested_array_child_code sf ce ty inner ip src dst st ops middle final
    guard_st header_st loop_st iip cnt fn limit_st iv nv hdr /\
  nested_array_body next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap
    ip src p srcaddr j s /\
  abi_decoder_coherent ce env sf
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) parent_di
    (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    d (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) b cap prepared /\
  mem_bytes_at sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  next <= st.cs_next_var /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  is_dynamic (vyper_to_abi_type env ty) /\
  is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  inner < dimword (:256) /\ n < dimword (:256) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  b <= s.vs_alloca_next /\ oid <> header_st.cs_next_id /\ cid <> header_st.cs_next_id /\ cid <> oid /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) s /\
  32 <= type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)) /\
  d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner))+
    type_memory_bytes ce (ArrayT ty (Dynamic inner)) <=
    d+type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap t /\
    entry_loop_child_end fn final.cs_current_bb final.cs_current_insts final.cs_next_id
      iv nv ip hdr src p srcaddr (LENGTH xs) j t /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) t /\
    val_in_memory (ArrayTV tv (Dynamic inner)) (EL j xs)
      (d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner))) t.vs_memory /\
    entry_loop_fields s t /\ entry_decode_path ctx fn s t /\
    abi_encoder_registered_effect {header_st.cs_next_id}
      [(d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner)),
        type_memory_bytes ce (ArrayT ty (Dynamic inner)))] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `nested_array_child_code`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [nested_array_child_code_def]) >>
  qpat_assum `nested_array_body _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [nested_array_body_def]) >>
  drule_all nested_child_canonical_inputs >> strip_tac >>
  drule_all nested_array_inv_inputs >> strip_tac >>
  `fresh_vars_wrt limit_st s /\ entry_nested_scratch_ready header_st.cs_next_id b cap s` by
    fs[nested_array_inv_def] >>
  qhdtm_x_assum `entry_nested_scratch_ready`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [entry_nested_scratch_ready_def]) >>
  qpat_assum `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) = _`
    (fn th => qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all (entry_nested_owned_bytes_execution |> SPEC_ALL |>
    Q.INST [`ity` |-> `ArrayT ty (Dynamic inner)`,
            `itv` |-> `ArrayTV tv (Dynamic inner)`] |>
    SIMP_RULE bool_ss []) >>
  disch_then (qx_choose_then `t` (qx_choose_then `q` strip_assume_tac)) >>
  suspend "restore"
QED
Resume nested_array_allocating_callback[restore]:
  `d+32 <= d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner))` by simp[] >>
  drule_all nested_array_child_restore >> strip_tac >>
  drule_all nested_array_backedge_endpoint >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac []
QED
Finalise nested_array_allocating_callback

(* Extract the allocating child's static phases from its actual compilation. *)
Theorem nested_array_child_code_producer[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
    (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
    (type_memory_bytes ce (ArrayT ty (Dynamic inner))) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner))) middle = ((),final) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  fn_has_code st middle fn /\ fn_has_code middle final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  middle.cs_next_var <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  FST ops = Var iv /\
  lookup_block final.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = final.cs_current_insts ++
    abi_decode_backedge_insts final.cs_next_id iv nv ip hdr ==>
  ?guard_st header_st loop_st iip cnt.
    nested_array_child_code sf ce ty inner ip src dst st ops middle final
      guard_st header_st loop_st iip cnt fn limit_st iv nv hdr /\
    middle.cs_next_id <= header_st.cs_next_id
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) = _`
    (fn th => qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all (calldata_nonbulk_parent_intervals |> SPEC_ALL |>
    Q.INST [`dyn` |-> `T`] |> SIMP_RULE bool_ss []) >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderArrayInitTheory.abi_decode_array_loop_init_shape >> strip_tac >>
  `!ins. MEM ins (emitted_insts middle loop_st) ==> MEM ins (fn_insts fn)` by
    suspend "emitted" >>
  qexistsl_tac [`guard_st`,`header_st`,`loop_st`,`ip'`,`cnt`] >>
  asm_rewrite_tac[nested_array_child_code_def] >> qexists_tac `bb` >> simp[]
QED
Resume nested_array_child_code_producer[emitted]:
  qpat_x_assum `fn_has_code middle loop_st fn` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [fragExecTheory.fn_has_code_def] >> strip_tac >> rpt strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  irule rich_listTheory.IS_PREFIX_MEM >>
  qexists_tac `loop_st.cs_current_insts` >> asm_rewrite_tac [] >>
  irule rich_listTheory.MEM_DROP_IMP >>
  qexists_tac `LENGTH middle.cs_current_insts` >>
  fs[emitted_insts_def]
QED
Finalise nested_array_child_code_producer

(* Immutable compiler/canonical facts shared by every outer iteration. *)
Definition nested_array_loop_config_def:
  nested_array_loop_config
    ((ce,env,sf,ty,tv,inner,outer,parent_di,avs,xs,n),
     (ip,src,dst,st,ops,middle,last,guard_st,header_st,loop_st,iip,cnt,limit_st,iv,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,cap,prepared,p,srcaddr,sb),
     (hdr,body_lbl,exit_lbl,hid,next)) <=>
  nested_array_child_code sf ce ty inner ip src dst st ops middle last
    guard_st header_st loop_st iip cnt fn limit_st iv (STRING #"%" (toString nv)) hdr /\
  st.cs_current_bb = body_lbl /\ st.cs_current_insts = [] /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src CALLDATALOAD
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3))) /\
  src <> Var (STRING #"%" (toString next)) /\
  STRING #"%" (toString next) <> STRING #"%" (toString (next+1)) /\
  next+4 <= limit_st.cs_next_var /\ next <= nv /\ nv < limit_st.cs_next_var /\
  next <= st.cs_next_var /\
  abi_decoder_operand_live next ip /\ abi_decoder_operand_live next src /\
  abi_decoder_operand_live next dst /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_coherent ce env sf
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) parent_di
    (ListV avs) (ArrayV (DynArrayV xs)) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  is_dynamic (vyper_to_abi_type env ty) /\
  is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce (ArrayT ty (Dynamic inner)) =
    type_memory_size (ArrayTV tv (Dynamic inner)) /\
  EVERY (val_wf (ArrayTV tv (Dynamic inner))) xs /\
  LENGTH xs < dimword (:256) /\ inner < dimword (:256) /\ n < dimword (:256) /\
  32+LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner)) <=
    type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  oid <> header_st.cs_next_id /\ cid <> header_st.cs_next_id /\ cid <> oid /\
  (d+32 <= w2n p \/ w2n p+32 <= d) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    d (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) b cap prepared /\
  mem_bytes_at sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    (abi_decode_source CALLDATALOAD prepared) =
    enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)
End

Theorem nested_array_actual_contract[local]:
  cfg = ((ce,env,sf,ty,tv,inner,outer,parent_di,avs,xs,n),
     (ip,src,dst,st,ops,middle,last,guard_st,header_st,loop_st,iip,cnt,limit_st,iv,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,cap,prepared,p,srcaddr,sb),
     (hdr,body_lbl,exit_lbl,hid,next)) /\ nested_array_loop_config cfg ==>
  entry_actual_owned_indexed_contract ctx fn site hdr body_lbl exit_lbl hid
    last.cs_current_bb last.cs_current_insts last.cs_next_id ip src
    (STRING #"%" (toString next)) iv (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
    (STRING #"%" (toString nv)) p srcaddr (ArrayTV tv (Dynamic inner)) xs d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))
    cid oid root extent {cid;header_st.cs_next_id} {header_st.cs_next_id}
    (\j s. nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap s)
    (nested_array_body next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap
      ip src p srcaddr)
    (\j s. nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap s)
    (nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `nested_array_loop_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [nested_array_loop_config_def]) >>
  `ip <> Var (STRING #"%" (toString nv)) /\ src <> Var (STRING #"%" (toString nv))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >>
     qexists_tac `next` >> simp[]) >>
  simp_tac bool_ss [entry_actual_owned_indexed_contract_def] >>
  asm_rewrite_tac [] >> simp[Excl "enc_def"] >> rpt conj_tac
  >- suspend "header"
  >- suspend "child"
  >> suspend "successor"
QED
Resume nested_array_actual_contract[header]:
  rpt strip_tac >> Cases_on `j < LENGTH xs`
  >- (simp[] >> irule nested_array_header_body >>
      fs[entry_owned_loop_inv_def, SF SFY_ss, Excl "enc_def"]) >>
  simp[] >> irule nested_array_inv_header >> asm_rewrite_tac []
QED
Resume nested_array_actual_contract[child]:
  rpt strip_tac >>
  `d+32+j*type_memory_bytes ce (ArrayT ty (Dynamic inner))+
     type_memory_bytes ce (ArrayT ty (Dynamic inner)) <=
     d+type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))` by
    (`(j+1)*type_memory_size (ArrayTV tv (Dynamic inner)) <=
       LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner))` by
       simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `(j+1)*_ <= _` mp_tac >>
     qpat_x_assum `32+LENGTH xs*_ <= _` mp_tac >>
     qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic inner)) = _`
       (fn th => pure_rewrite_tac [th]) >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, MULT_CLAUSES] >>
     decide_tac) >>
  `32 <= type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))` by
    (qpat_x_assum `32+LENGTH xs*_ <= _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp_tac arith_ss []) >>
  `b <= u.vs_alloca_next` by
    fs[nested_array_body_def, nested_array_inv_def, entry_nested_scratch_ready_def,
       Excl "enc_def"] >>
  `u.vs_current_bb = st.cs_current_bb /\
   u.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all nested_array_allocating_callback >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >>
  qhdtm_x_assum `val_in_memory` mp_tac >>
  qhdtm_x_assum `abi_encoder_registered_effect` mp_tac >>
  asm_simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM]
QED
Resume nested_array_actual_contract[successor]:
  rpt strip_tac >> irule nested_array_inv_backedge >> asm_rewrite_tac []
QED
Finalise nested_array_actual_contract

Theorem nested_array_loop_endpoint[local]:
  cfg = ((ce,env,sf,ty,tv,inner,outer,parent_di,avs,xs,n),
     (ip,src,dst,st,ops,middle,last,guard_st,header_st,loop_st,iip,cnt,limit_st,iv,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,cap,prepared,p,srcaddr,sb),
     (hdr,body_lbl,exit_lbl,hid,next)) /\ nested_array_loop_config cfg /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr (ArrayTV tv (Dynamic inner)) xs d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))
    cid oid root extent 0 s /\
  nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap s ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) t /\
    nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap t /\
    val_in_memory (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer))
      (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_trace ctx fn {cid;header_st.cs_next_id}
      [(d,32+LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner)))] s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all nested_array_actual_contract >> strip_tac >>
  drule entry_actual_owned_indexed_array_loop_from_index >>
  simp_tac bool_ss [] >> disch_then drule >>
  asm_rewrite_tac [] >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac [] >>
  irule (cj 2 calldata_terminal_array_memory) >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `nested_array_loop_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [nested_array_loop_config_def]) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  fs[entry_loop_prefix_def, nested_array_inv_def, Excl "enc_def"] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Both depths are extracted from one actual outer compilation. *)
Theorem nested_array_compiler_phases[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) T outer) initial = ((),final) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  fn_has_code initial final fn /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_operand_live initial.cs_next_var src /\
  abi_decoder_operand_live initial.cs_next_var dst /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?ip cnt pguard pheader ploop labels st ops middle last
    guard_st header_st loop_st iip icnt.
    abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) outer
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner))) initial =
      ((ip,cnt),ploop) /\
    abi_decode_index_init pheader = (ip,ploop) /\
    abi_decode_loop_prefix ip src CALLDATALOAD ploop = (labels,st) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner))) middle = ((),last) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) last = ((),final) /\
    nested_array_child_code sf ce ty inner ip src dst st ops middle last
      guard_st header_st loop_st iip icnt fn limit_st
      (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString last.cs_next_var))
      (FST labels) /\
    pheader.cs_next_id < header_st.cs_next_id /\
    st.cs_current_bb = FST (SND labels) /\ st.cs_current_insts = [] /\
    final.cs_current_bb = SND (SND labels) /\ final.cs_current_insts = [] /\
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) outer
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      initial = ((),pguard) /\
    abi_decode_array_header dst src CALLDATALOAD pguard = (cnt,pheader) /\
    abi_decode_loop_cfg fn (FST labels) (FST (SND labels)) (SND (SND labels))
      (ploop.cs_next_id+1) ip src CALLDATALOAD
      (STRING #"%" (toString ploop.cs_next_var))
      (STRING #"%" (toString (ploop.cs_next_var+1)))
      (STRING #"%" (toString (ploop.cs_next_var+2)))
      (STRING #"%" (toString (ploop.cs_next_var+3))) /\
    src <> Var (STRING #"%" (toString ploop.cs_next_var)) /\
    STRING #"%" (toString ploop.cs_next_var) <>
      STRING #"%" (toString (ploop.cs_next_var+1)) /\
    ploop.cs_next_var+4 <= limit_st.cs_next_var /\
    ploop.cs_next_var <= last.cs_next_var /\
    last.cs_next_var < limit_st.cs_next_var /\
    ploop.cs_next_var <= st.cs_next_var /\
    abi_decoder_operand_live ploop.cs_next_var ip /\
    abi_decoder_operand_live ploop.cs_next_var src /\
    abi_decoder_operand_live ploop.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var ip /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\
    fn_has_code ploop final fn /\
    fn_has_code initial ploop fn /\
    (!i. MEM i (emitted_insts initial ploop) ==> MEM i (fn_insts fn))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (calldata_nonbulk_parent_shell |> SPEC_ALL |>
    Q.INST [`dyn` |-> `T`] |> SIMP_RULE bool_ss []) >> strip_tac >>
  rename1 `compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops))
    CALLDATALOAD (Lit 0w) _ middle = ((),last)` >>
  qpat_assum `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) = _`
    (fn th => qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `last.cs_current_insts = []` by
    (drule (calldata_nonbulk_empty_exit |> SPEC_ALL |>
      Q.INST [`dyn` |-> `T`] |> SIMP_RULE bool_ss []) >> simp[]) >>
  `!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ last = _` mp_tac >>
     qpat_assum `FST ops = _` (fn th => pure_rewrite_tac [th]) >>
     disch_then (mp_then Any mp_tac calldata_loop_child_continuation_phi) >>
     simp[abi_decode_backedge_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def]) >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var` by
    suspend "bounds" >>
  `?bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = last.cs_current_insts ++
      abi_decode_backedge_insts last.cs_next_id (STRING #"%" (toString st0.cs_next_var))
        (STRING #"%" (toString last.cs_next_var)) ip (FST labels)` by simp[] >>
  drule_all nested_array_child_code_producer >> strip_tac >>
  suspend "witnesses"
QED
Resume nested_array_compiler_phases[bounds]:
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
    (mp_then Any strip_assume_tac abi_decoder_variable_counter) >>
  qpat_assum `abi_decode_loop_suffix _ _ _ _ last = _` mp_tac >>
  qpat_assum `FST ops = _` (fn th => pure_rewrite_tac [th]) >>
  disch_then (mp_then Any strip_assume_tac
    abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_suffix_facts) >> decide_tac
QED
Resume nested_array_compiler_phases[witnesses]:
  drule_all entryReachBodyCanonicalBytesArrayTheory.entry_bytes_array_initial_live >> strip_tac >>
  drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_prefix_facts >> strip_tac >>
  `st0.cs_next_var <= last.cs_next_var` by
    (qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ st0 = _`
       (mp_then Any strip_assume_tac abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands) >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
       (mp_then Any strip_assume_tac abi_decoder_variable_counter) >> decide_tac) >>
  `last.cs_next_var < limit_st.cs_next_var` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ last = _` mp_tac >>
     qpat_assum `FST ops = _` (fn th => pure_rewrite_tac [th]) >>
     disch_then (mp_then Any strip_assume_tac
       abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_suffix_facts) >> decide_tac) >>
  `abi_decoder_operand_live st0.cs_next_var ip /\
   abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    (rpt conj_tac >> irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `loop_st.cs_next_var` >> simp[]) >>
  `fn_has_code loop_st final fn` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ initial = _`
       (mp_then Any mp_tac (calldata_nonbulk_parent_intervals |> SPEC_ALL |>
         Q.INST [`dyn` |-> `T`] |> SIMP_RULE bool_ss [])) >>
     simp[] >> strip_tac >> gvs[]) >>
  suspend "code_witnesses"
QED
Resume nested_array_compiler_phases[code_witnesses]:
  rename1 `nested_array_child_code _ _ _ _ _ _ _ _ _ _ _ iguard iheader iloop iip icnt _ _ _ _ _` >>
  qexistsl_tac [`ip`,`cnt`,`guard_st`,`header_st`,`loop_st`,`labels`,`st0`,`ops`,
    `middle`,`last`,`iguard`,`iheader`,`iloop`,`iip`,`icnt`] >>
  asm_rewrite_tac [] >>
  `abi_decode_loop_cfg fn (FST labels) (FST (SND labels)) (SND (SND labels))
    (loop_st.cs_next_id+1) ip src CALLDATALOAD
    (STRING #"%" (toString loop_st.cs_next_var))
    (STRING #"%" (toString (loop_st.cs_next_var+1)))
    (STRING #"%" (toString (loop_st.cs_next_var+2)))
    (STRING #"%" (toString (loop_st.cs_next_var+3)))` by
    (simp_tac bool_ss [abi_decode_loop_cfg_def] >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  asm_rewrite_tac [] >> rpt conj_tac
  >- decide_tac >- decide_tac >- decide_tac >- decide_tac >>
  rpt strip_tac >>
  `?bb. lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX loop_st.cs_current_insts bb.bb_instructions` by
    (drule abi_decoder_loop_prefix_extends >> strip_tac >>
     drule_all fn_has_code_start >> simp[]) >>
  rename1 `isPREFIX loop_st.cs_current_insts init_bb.bb_instructions` >>
  irule lookup_block_fn_insts >>
  qexistsl_tac [`init_bb`,`loop_st.cs_current_bb`] >> asm_simp_tac bool_ss [] >>
  irule rich_listTheory.IS_PREFIX_MEM >>
  qexists_tac `loop_st.cs_current_insts` >> simp[] >>
  irule rich_listTheory.MEM_DROP_IMP >>
  qexists_tac `LENGTH initial.cs_current_insts` >>
  drule abiDecoderArrayInitTheory.abi_decode_array_loop_init_shape >>
  simp[abi_decode_source_opcode_def] >> strip_tac >>
  fs[emitted_insts_def]
QED
Finalise nested_array_compiler_phases

(* Pure outer input facts follow from the same canonical metadata used by
   the callback, including the empty-array case. *)
Theorem nested_array_canonical_facts[local]:
  abi_decoder_coherent ce env sf
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env
    (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) di
    (ListV avs) (ArrayV (DynArrayV xs)) /\ outer < dimword (:256) ==>
  LENGTH xs = LENGTH avs /\ LENGTH xs <= outer /\ LENGTH xs < dimword (:256) /\
  EVERY (val_wf (ArrayTV tv (Dynamic inner))) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce (ArrayT ty (Dynamic inner)) =
    type_memory_size (ArrayTV tv (Dynamic inner)) /\
  is_dynamic (vyper_to_abi_type env (ArrayT ty (Dynamic inner))) /\
  32+LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner)) <=
    type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
Proof
  strip_tac >> drule abi_decoder_dynarray_values >> strip_tac >>
  `EVERY (val_wf (ArrayTV tv (Dynamic inner))) xs` by
    (fs[all_have_type_EVERY, EVERY_MEM] >> rpt strip_tac >>
     irule value_has_type_memory_wf >> metis_tac[]) >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [abi_decoder_coherent_array_iff] >> strip_tac >>
  qpat_assum `abi_decoder_coherent _ _ _ ty tv`
    (mp_then Any assume_tac abi_decoder_coherent_header) >>
  fs[abi_decoder_header_def, Excl "enc_def"] >>
  simp[Once vyperABITheory.vyper_to_abi_type_def] >>
  qpat_x_assum `LENGTH xs <= outer` mp_tac >>
  qpat_x_assum `type_memory_size (ArrayTV tv (Dynamic inner)) = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compileEnvTheory.type_memory_bytes_def, LE_MULT_RCANCEL]
QED

(* Header entry changes control only: the allocating nested invariant and
   enclosing resources describe exactly the initializer's endpoint. *)
Theorem nested_array_header_entry[local]:
  ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid p oid root extent d capacity prepared /\
  eval_operand ip prepared = SOME (n2w p) /\ eval_operand src prepared = SOME srcaddr /\
  mload p prepared = 0w /\ abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st prepared /\
  mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  entry_nested_scratch_ready iid b cap prepared ==>
  entry_decode_path ctx fn prepared (jump_to hdr prepared) /\
  entry_owned_loop_inv ctx fn site hdr ip src (n2w p) srcaddr tv xs
    d capacity cid oid root extent 0 (jump_to hdr prepared) /\
  nested_array_inv next limit_st d (LENGTH xs) prepared iid b cap (jump_to hdr prepared) /\
  entry_loop_fields prepared (jump_to hdr prepared) /\
  abi_encoder_registered_effect ids outs prepared (jump_to hdr prepared)
Proof
  strip_tac >> conj_tac
  >- (`prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts = prepared` by
        simp[venom_state_component_equality] >>
      drule_all entryReachBodyOperationalHeaderTheory.entry_initializer_header_jump_path >> simp[]) >>
  `remaining_alloca_budget (fn_insts fn) (jump_to hdr prepared) =
   remaining_alloca_budget (fn_insts fn) prepared` by
    (irule allocaBudgetPropsTheory.remaining_alloca_budget_domain_cong >> simp[jump_to_def]) >>
  gvs[entry_owned_loop_inv_def, entry_owned_loop_resources_def, entry_owned_region_def,
     abi_decode_loop_ready_def, entry_loop_prefix_def, nested_array_inv_def,
     entry_nested_scratch_ready_def, entry_loop_fields_def, abi_encoder_registered_effect_def,
     jump_to_def, allocaFrontierBoundTheory.alloca_frontier_inv_def,
     abiAllocationHistoryTheory.abi_alloca_history_def, venomMemDefsTheory.alloca_inv_def,
     venomMemDefsTheory.allocas_non_overlapping_def, venomMemDefsTheory.alloca_next_valid_def,
     compileEnvTheory.fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
     abi_decode_load_def, abi_decode_source_def, mload_def,
     abiDecoderFrameTheory.abi_decode_footprint_frame_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem nested_array_prepared_endpoint[local]:
  cfg = ((ce,env,sf,ty,tv,inner,outer,parent_di,avs,xs,n),
     (ip,src,dst,st,ops,middle,last,guard_st,header_st,loop_st,iip,cnt,limit_st,iv,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,cap,prepared,p,srcaddr,sb),
     (hdr,body_lbl,exit_lbl,hid,next)) /\ nested_array_loop_config cfg /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = ploop.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ploop.cs_current_insts /\
  lookup_block ploop.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ploop.cs_current_bb; bb_instructions :=
      ploop.cs_current_insts ++ [mk_inst ploop.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) prepared /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME srcaddr /\
  mload (w2n p) prepared = 0w /\
  abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  entry_nested_scratch_ready header_st.cs_next_id b cap prepared ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    val_in_memory (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer))
      (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) t /\
    nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap t /\
    entry_loop_fields prepared t /\ entry_decode_path ctx fn prepared t /\
    abi_encoder_registered_effect {cid;header_st.cs_next_id}
      [(d,type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))] prepared t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `entry_decode_path ctx fn prepared (jump_to hdr prepared) /\
   entry_owned_loop_inv ctx fn site hdr ip src p srcaddr (ArrayTV tv (Dynamic inner)) xs d
     (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))
     cid oid root extent 0 (jump_to hdr prepared) /\
   nested_array_inv next limit_st d (LENGTH xs) prepared header_st.cs_next_id b cap
     (jump_to hdr prepared) /\ entry_loop_fields prepared (jump_to hdr prepared) /\
   abi_encoder_registered_effect {cid;header_st.cs_next_id}
     [(d,type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))]
     prepared (jump_to hdr prepared)` by
    (qspec_then `p` (fn th => once_rewrite_tac [GSYM th]) n2w_w2n >>
     irule nested_array_header_entry >> simp[w2n_lt, SF SFY_ss] >>
     qexists_tac `ploop` >> simp[]) >>
  drule_all nested_array_loop_endpoint >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac [] >> suspend "frames"
QED
Resume nested_array_prepared_endpoint[frames]:
  `32+LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner)) <=
   type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))` by
    (qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
     fs[nested_array_loop_config_def, Excl "enc_def"]) >>
  qpat_x_assum `entry_loop_trace _ _ _ _ _ t`
    (strip_assume_tac o PURE_REWRITE_RULE [entryReachBodyOperationalLoopTheory.entry_loop_trace_def]) >>
  `entry_loop_fields prepared t` by
    (qpat_x_assum `nested_array_inv _ _ _ _ _ _ _ _ t` mp_tac >>
     simp_tac bool_ss [nested_array_inv_def] >> metis_tac[]) >>
  asm_rewrite_tac [] >> conj_tac >- metis_tac[entryReachBodyOperationalPathTheory.entry_decode_path_trans] >>
  irule abi_encoder_registered_effect_trans >>
  qexists_tac `jump_to hdr prepared` >> asm_rewrite_tac [] >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`{cid;header_st.cs_next_id}`,
    `[(d,32+LENGTH xs*type_memory_size (ArrayTV tv (Dynamic inner))) ]`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED
Finalise nested_array_prepared_endpoint

(* Initial resources identify the two actual emitted counter sites using
   deterministic compiler computations, never an execution callback. *)
Definition entry_nested_array_init_resources_def:
  entry_nested_array_init_resources sf ce ty inner outer dst src st
    (ctx,fn,site,d,b,cap,p,oid,root,extent,initial) cid iid <=>
  ?pg ph pl ip cnt labels body ops middle ig ih icnt.
    entry_array_init_resources dst src outer
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (st,pg,ph,pl,ip,cnt)
      (ctx,fn,site,d,type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)),
       b,cap,p,initial) /\
    abi_decode_loop_prefix ip src CALLDATALOAD pl = (labels,body) /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) body = (ops,middle) /\
    abi_decode_dynarray_prefix (FST (SND ops)) CALLDATALOAD (Lit 0w) inner
      (abi_embedded_static_size ce.ce_struct_fields ty) middle = ((),ig) /\
    abi_decode_array_header (SND (SND ops)) (FST (SND ops)) CALLDATALOAD ig = (icnt,ih) /\
    cid = ph.cs_next_id /\ iid = ih.cs_next_id /\
    entry_owned_region oid root extent d
      (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) initial /\
    oid <> cid /\ oid <> iid /\ b <= initial.vs_alloca_next /\
    (FLOOKUP initial.vs_allocas iid = NONE ==>
      initial.vs_alloca_next + (if FLOOKUP initial.vs_allocas cid = NONE then 32 else 0) + 32 <= b+cap) /\
    (!q. FLOOKUP initial.vs_allocas iid = SOME (q,32) ==> b <= q /\ q+32 <= b+cap)
End

Theorem nested_array_initial_site_alignment[local]:
  entry_nested_array_init_resources sf ce ty inner outer dst src initial
    (ctx,fn,site,d,b,cap,p,oid,root,extent,s) cid iid /\
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) outer
    (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner))) initial =
    ((ip,cnt),pl) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) outer
    (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner))) initial = ((),pg) /\
  abi_decode_array_header dst src CALLDATALOAD pg = (cnt,ph) /\
  abi_decode_index_init ph = (ip,pl) /\
  abi_decode_loop_prefix ip src CALLDATALOAD pl = (labels,body_st) /\
  nested_array_child_code sf ce ty inner ip src dst body_st ops middle last
    ig ih il iip icnt fn limit_st iv nv hdr /\ ph.cs_next_id < ih.cs_next_id ==>
  entry_array_init_resources dst src outer
    (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
    (initial,pg,ph,pl,ip,cnt)
    (ctx,fn,site,d,type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)),
     b,cap,p,s) /\
  cid = ph.cs_next_id /\ iid = ih.cs_next_id /\ cid <> iid /\
  entry_owned_region oid root extent d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) s /\
  oid <> cid /\ oid <> iid /\ b <= s.vs_alloca_next /\
  (FLOOKUP s.vs_allocas iid = NONE ==>
    s.vs_alloca_next + (if FLOOKUP s.vs_allocas cid = NONE then 32 else 0) + 32 <= b+cap) /\
  (!q. FLOOKUP s.vs_allocas iid = SOME (q,32) ==> b <= q /\ q+32 <= b+cap)
Proof
  simp_tac bool_ss [entry_nested_array_init_resources_def,
    entryReachBodyCanonicalBytesArrayTheory.entry_array_init_resources_def,
    nested_array_child_code_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_owned_canonical_nested_bytes_array_execution:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) T outer) st = ((),final) /\
  fn_has_code st final fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer)) /\
  abi_decoder_metadata ce env (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))
    (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer))
    (DecDynArray (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
      (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
      (type_memory_bytes ce (ArrayT ty (Dynamic inner))) T outer)
    (ListV avs) (ArrayV (DynArrayV xs)) /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic inner)) =
    DecDynArray (DecBytestring n) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) T inner /\
  is_dynamic (vyper_to_abi_type env ty) /\
  outer < dimword (:256) /\ inner < dimword (:256) /\ n < dimword (:256) /\
  entry_nested_array_init_resources sf ce ty inner outer dst src st
    (ctx,fn,site,d,b,cap,p,oid,root,extent,initial) cid iid /\
  abi_alloca_history (fn_insts fn) initial /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    d (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) b cap initial /\
  mem_bytes_at sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs)))
    (abi_decode_source CALLDATALOAD initial) =
    enc (Array NONE (vyper_to_abi_type env (ArrayT ty (Dynamic inner)))) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  fresh_vars_wrt limit_st initial /\ final.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV (ArrayTV tv (Dynamic inner)) (Dynamic outer))
      (ArrayV (DynArrayV xs)) d t.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ fresh_vars_wrt limit_st t /\
    entry_owned_loop_resources ctx fn site cid p oid root extent d
      (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) t /\
    entry_loop_fields initial t /\ entry_decode_path ctx fn initial t /\
    abi_encoder_registered_effect {cid;iid}
      [(d,type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)))] initial t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all nested_array_compiler_phases >> strip_tac >>
  drule_all nested_array_initial_site_alignment >> strip_tac >>
  drule_all nested_array_canonical_facts >> strip_tac >>
  `LENGTH avs <= outer` by decide_tac >>
  `ploop.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `oid <> pheader.cs_next_id` by metis_tac[] >>
  drule_all owned_array_canonical_initializer >>
  disch_then (qx_choose_then `prepared` strip_assume_tac) >>
  qpat_x_assum `cid = _` SUBST_ALL_TAC >>
  qpat_x_assum `iid = _` SUBST_ALL_TAC >>
  drule_all nested_array_initializer_scratch >> strip_tac >>
  qpat_assum `entry_array_init_resources _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [entryReachBodyCanonicalBytesArrayTheory.entry_array_init_resources_def]) >>
  `p < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv _ _ _ initial` mp_tac >>
     simp_tac bool_ss [allocaFrontierBoundTheory.alloca_frontier_inv_def] >> strip_tac >>
     qpat_x_assum `FLOOKUP initial.vs_allocas _ = NONE /\ _ \/ _` strip_assume_tac >>
     gvs[] >> decide_tac) >>
  SUBGOAL_THEN ``d+type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer)) <= p \/ p+32 <= d`` assume_tac
  >- (drule entry_owned_region_counter_separation >>
     disch_then (qspecl_then [`p`,`pheader.cs_next_id`] mp_tac) >>
     asm_rewrite_tac [] >> metis_tac[]) >>
  `nested_array_loop_config
    ((ce,env,sf,ty,tv,inner,outer,
      DecDynArray (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic inner)))
        (abi_embedded_static_size ce.ce_struct_fields (ArrayT ty (Dynamic inner)))
        (type_memory_bytes ce (ArrayT ty (Dynamic inner))) T outer,avs,xs,n),
     (ip,src,dst,st',ops,middle,last,guard_st,header_st,loop_st,iip,icnt,limit_st,
       STRING #"%" (toString st'.cs_next_var),last.cs_next_var),
     (ctx,fn,site,pheader.cs_next_id,oid,root,extent,d,b,cap,prepared,
       (n2w p:bytes32),(n2w sb:bytes32),sb),
     (FST labels,FST (SND labels),SND (SND labels),ploop.cs_next_id+1,ploop.cs_next_var))` by
    (simp_tac bool_ss [nested_array_loop_config_def] >>
     asm_simp_tac (srw_ss()) [w2n_n2w, venomWfTheory.fn_inst_ids_distinct_def, Excl "enc_def"] >>
     conj_tac
     >- (qpat_x_assum `ALL_DISTINCT (MAP _ (fn_insts fn))` mp_tac >>
         simp[venomInstTheory.fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
           MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
     qpat_x_assum `d+type_memory_bytes ce _ <= p \/ _` mp_tac >>
     qpat_x_assum `32 <= type_memory_bytes ce _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `nested_array_loop_config cfg` >>
  suspend "configured"
QED
Resume entry_owned_canonical_nested_bytes_array_execution[configured]:
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderRecursiveLoopEntryTheory.abi_decoder_loop_phase_entry >> strip_tac >>
  drule_all abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_phase_lookups >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     pure_rewrite_tac [abi_decoder_ranges_def] >> metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w sb:bytes32) prepared = n2w (LENGTH avs)` by
    (irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     qexists_tac `vyper_to_abi_type env (ArrayT ty (Dynamic inner))` >>
     asm_rewrite_tac [] >>
     qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     pure_rewrite_tac [abi_decoder_ranges_def] >> metis_tac[]) >>
  qpat_assum `Abbrev (cfg = _)`
    (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `entry_owned_loop_resources ctx fn site pheader.cs_next_id (w2n (n2w p:bytes32))
    oid root extent d
    (type_memory_bytes ce (ArrayT (ArrayT ty (Dynamic inner)) (Dynamic outer))) prepared` by
    simp[] >>
  `mload (w2n (n2w p:bytes32)) prepared = 0w /\
   mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
   abi_decode_load CALLDATALOAD (n2w sb:bytes32) prepared = n2w (LENGTH xs)` by
    simp[] >>
  `phi_prefix_length (abi_decode_header_insts (ploop.cs_next_id+1) ip src CALLDATALOAD
    (STRING #"%" (toString ploop.cs_next_var))
    (STRING #"%" (toString (ploop.cs_next_var+1)))
    (STRING #"%" (toString (ploop.cs_next_var+2)))
    (STRING #"%" (toString (ploop.cs_next_var+3))) st'.cs_current_bb (SND (SND labels))) = 0` by
    simp[abi_decode_header_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
  drule nested_array_prepared_endpoint >>
  disch_then (qspec_then `ploop` mp_tac) >>
  disch_then (drule_at (Pat `lookup_block (FST labels) _ = SOME _`)) >>
  impl_tac >- simp[abi_decode_header_insts_def, phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "endpoint"
QED

Resume entry_owned_canonical_nested_bytes_array_execution[endpoint]:
  qpat_x_assum `nested_array_inv _ _ _ _ _ _ _ _ t`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [nested_array_inv_def]) >>
  qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  simp[w2n_n2w] >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac (srw_ss()) [w2n_n2w] >>
  conj_tac >-
    (qpat_x_assum `entry_loop_fields initial prepared` mp_tac >>
     qpat_x_assum `entry_loop_fields prepared t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[entry_loop_fields_def]) >>
  conj_tac >- metis_tac[entryReachBodyOperationalPathTheory.entry_decode_path_trans] >>
  conj_tac >- suspend "effects" >>
  rpt strip_tac >>
  `abi_decoder_operand_live ploop.cs_next_var op` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[] >>
     drule abiDecoderArrayInitTheory.abi_decode_array_loop_init_shape >>
     simp[abi_decode_source_opcode_def]) >>
  metis_tac[]
QED
Resume entry_owned_canonical_nested_bytes_array_execution[effects]:
  irule abi_encoder_registered_effect_trans >>
  qexists_tac `prepared` >> asm_rewrite_tac [] >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl_tac [`{pheader.cs_next_id}`,`[(d,32)]`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED
Finalise entry_owned_canonical_nested_bytes_array_execution

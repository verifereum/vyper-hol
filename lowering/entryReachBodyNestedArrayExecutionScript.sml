(* Complete depth-two canonical array execution: caller bridges and iteration. *)
Theory entryReachBodyNestedArrayExecution
Ancestors
  entryReachBodyNestedBytesExecution entryReachBodyEnclosingCounter
  entryReachBodyNestedScratchTransport entryReachBodyOwnedBytesArray
  abiDecoderValidArraySetupInputs abiDecoderCorrectPrimitiveArray
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract
  valueTypingMemoryProps vyperTyping valueEncoding compileEnv
  entryReachBodyExactArrayLoop abiDecoderLoopRegisters abiDecoderExecution abiDecoderContract
  emitHelperProps valueEncodingProps venomExecSemantics venomState
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

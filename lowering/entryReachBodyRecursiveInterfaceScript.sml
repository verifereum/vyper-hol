(* Ambient scratch readiness at recursive decoder consumer boundaries. *)
Theory entryReachBodyRecursiveInterface
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyScratchSet entryReachBodyScratchExecution entryReachBodyScratchCapacity
  entryReachBodyNestedOwnedPath abiDecoderFootprint venomMemDefs
  abiDecoderTypedContract
  finite_map pred_set arithmetic

Theorem entry_scratch_initializer_room:
  entry_scratch_ready sites b cap s /\ id IN sites ==>
  b <= s.vs_alloca_next /\
  (FLOOKUP s.vs_allocas id = NONE ==> s.vs_alloca_next+32 <= b+cap) /\
  (!q. FLOOKUP s.vs_allocas id = SOME (q,32) ==> b <= q /\ q+32 <= b+cap)
Proof
  strip_tac >> conj_tac >- fs[entry_scratch_ready_def] >>
  conj_tac >- metis_tac[entry_scratch_ready_fresh] >>
  metis_tac[entry_scratch_ready_existing]
QED

Theorem entry_scratch_child_excludes_ancestor:
  entry_scratch_ready sites b cap s /\ child_sites SUBSET sites /\
  ancestor IN sites /\ ancestor NOTIN child_sites /\
  FLOOKUP s.vs_allocas ancestor = SOME (p,32) /\ alloca_inv s ==>
  abi_footprint_disjoint p 32 (abi_decoder_child_scratch child_sites b cap s)
Proof
  strip_tac >> drule_all entry_scratch_ready_existing >> strip_tac >>
  `FINITE child_sites` by
    (fs[entry_scratch_ready_def] >> metis_tac[SUBSET_FINITE]) >>
  `s.vs_alloca_next <= b+cap` by (fs[entry_scratch_ready_def] >> decide_tac) >>
  irule abi_decoder_child_scratch_disjoint >>
  reverse conj_tac >- simp[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def] >> rpt strip_tac >>
  `id <> ancestor` by metis_tac[] >> metis_tac[]
QED

Theorem entry_nested_owned_ready_initializer:
  ity = ArrayT ty (Dynamic inner) /\ itv = ArrayTV tv (Dynamic inner) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ity) (abi_embedded_static_size ce.ce_struct_fields ity)
    (type_memory_bytes ce ity) st = (ops,middle) /\
  abi_decoder_coherent ce env sf (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer)) /\
  abi_decoder_metadata ce env (ArrayT ity (Dynamic outer)) (ArrayTV itv (Dynamic outer))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  j < LENGTH xs /\ is_dynamic (vyper_to_abi_type env ity) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ity (Dynamic outer))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Array NONE (vyper_to_abi_type env ity)) (ListV avs) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st middle fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT ity (Dynamic outer))) s /\
  abi_decode_dynarray_prefix (FST (SND ops)) CALLDATALOAD (Lit 0w) inner
    (abi_embedded_static_size ce.ce_struct_fields ty) middle = ((),guard_st) /\
  abi_decode_array_header (SND (SND ops)) (FST (SND ops)) CALLDATALOAD guard_st =
    (cnt,header_st) /\
  abi_decode_index_init header_st = (iip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  entry_scratch_ready sites b cap s /\ header_st.cs_next_id IN sites ==>
  ?u q. eval_operand (FST ops) u = SOME (n2w j) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_address_frame st.cs_next_var s u /\
    entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\ fresh_vars_wrt limit_st u /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ity (Dynamic outer))) u /\
    entry_owned_region oid root extent (d+32+j*type_memory_bytes ce ity)
      (type_memory_bytes ce ity) u /\
    abi_alloca_history (fn_insts fn) u /\
    abi_decoder_coherent ce env sf ity itv /\
    abi_decoder_metadata ce env ity itv (type_to_abi_dec_info ce.ce_struct_fields ce ity)
      (EL j avs) (EL j xs) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    mem_bytes_at (sb+abi_array_child_offset NONE (vyper_to_abi_type env ity) avs j)
      (LENGTH (enc (vyper_to_abi_type env ity) (EL j avs)))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ity) (EL j avs) /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) (FST (SND ops)) (SND (SND ops)) 0
      (sb+abi_array_child_offset NONE (vyper_to_abi_type env ity) avs j)
      (LENGTH (enc (vyper_to_abi_type env ity) (EL j avs)))
      (d+32+j*type_memory_bytes ce ity) (type_memory_bytes ce ity) b cap u /\
    entry_array_init_resources (SND (SND ops)) (FST (SND ops)) inner
      (abi_embedded_static_size ce.ce_struct_fields ty)
      (middle,guard_st,header_st,loop_st,iip,cnt)
      (ctx,fn,site,d+32+j*type_memory_bytes ce ity,type_memory_bytes ce ity,b,cap,q,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all entry_scratch_initializer_room >> strip_tac >>
  drule_all entry_nested_owned_initializer_boundary >>
  disch_then MATCH_ACCEPT_TAC
QED

(* Recursive execution checkpoint (proposal only; not an admitted theorem).

   General decoder interface, with all parameters universally generalized:
   compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) di st = ((),last),
   di = type_to_abi_dec_info sf ce ty, coherent ce env sf ty tv,
   metadata ce env ty tv di av v, canonical bytes at sb, eval src = n2w sb,
   eval dst = n2w d, sb+LENGTH(enc (vyper_to_abi_type env ty) av) < 2^256,
   d+type_memory_bytes ce ty < 2^256, live src/dst at st.cs_next_var,
   last.cs_next_var <= limit_st.cs_next_var, fresh_vars_wrt limit_st s,
   fn_has_code st last fn, abi_decoder_code st last,
   fn_inst_ids_distinct fn, unit_alloca_budget ctx < 2^256,
   alloca_inv s, abi_alloca_history (fn_insts fn) s,
   alloca_frontier_inv ctx fn site s,
   entry_owned_region oid root extent d (type_memory_bytes ce ty) s,
   oid outside abi_decoder_ids st.cs_next_id last.cs_next_id,
   child_sites = window_alloca_sites fn
     (abi_decoder_ids st.cs_next_id last.cs_next_id),
   child_sites SUBSET sites, oid NOTIN sites,
   entry_scratch_ready sites b cap s,
   ~s.vs_halted, s at (st.cs_current_bb,LENGTH st.cs_current_insts).

   Proposed conclusion: one t, simultaneously satisfying
   val_in_memory tv v d t.vs_memory, entry_decode_path ctx fn s t,
   entry_loop_fields s t, fresh_vars_wrt limit_st t,
   entry_scratch_ready sites b cap t,
   alloca_inv t, abi_alloca_history (fn_insts fn) t,
   alloca_frontier_inv ctx fn site t,
   entry_owned_region oid root extent d (type_memory_bytes ce ty) t,
   abi_encoder_registered_effect child_sites
     [(d,type_memory_bytes ce ty)] s t,
   preservation of every live st operand, ~t.vs_halted,
   t at (last.cs_current_bb,LENGTH last.cs_current_insts).
   This is a proposed contract, not an assertion that these premises suffice.

   Branch audit against compile_abi_decode_to_buf_def (440-588):
   - PrimWord: abi_decoder_primitive_memory_reentry gives actual sequence,
     exact v, frame, freshness and allocation equality. Operational lifting
     and full field observations still need assembling at this endpoint.
   - Bytestring: entry_canonical_bytes_sequence gives actual sequence, exact
     BytesV, frame, live operands and allocation equality. StringV metadata
     conversion and the generic observed endpoint still need assembling.
   - Bulk DecDynArray: abi_decoder_typed_bulk_sequence gives an exact-value
     sequence, but its recursive_pre includes interval budget/range premises.
     abi_decode_bulk_sequence and calldata_bulk_accepted_live_mod are lower
     operational boundaries to reuse without that obsolete resource premise.
   - Nonbulk DecDynArray: entry_actual_owned_indexed_array_loop_from_index
     supplies finite operational iteration with a callback. The new wrapper
     above validates initializer room, NOT ambient readiness at its endpoint.
     General child metadata/address (static as well as dynamic), callback
     production, ambient readiness through initializer/header/backedge, and
     exact list assembly must still be connected for arbitrary element types.
   - DecComplex: Lit 0w removes its outer guard. Empty members are return (),
     so reflexive path/effect/readiness suffice. For cons, reuse member pointer
     execution from calldataMembers, canonical metadata from
     abi_decoder_valid_member_entry, and prefix protection via
     entry_registered_child_slice. Need an owned ambient-ready member-suffix
     contract with exact tuple memory and one shared operational endpoint;
     abi_decoder_valid_members_correct_run exports only sim and uses interval
     budgets, hence is not that contract.
   - Dyn-loop body: setup, recursive child, increment/store, jump. Existing
     entry_canonical_dynamic_child_address handles dynamic children;
     owned_header_phase/owned_backedge_phase and
     entry_actual_owned_compiler_backedge handle shell phases. Child exclusion
     above protects ancestor storage only together with a child footprint
     frame. Ambient readiness alone does not preserve counter contents.

   Important remaining interface conflict: abi_decoder_ranges_def requires
   d+outsz <= b OR b+cap <= d. With b=0 and cap=unit_alloca_budget ctx,
   a nonempty destination inside the global allocation arena cannot satisfy
   that condition. Do not instantiate it with the ambient scratch budget.
   Global readiness and destination/source range facts must be separate;
   owner/child-site exclusion plus alloca_inv should justify actual scratch
   separation. Existing specialized wrappers remain valid conditionally,
   but do not establish the proposed global contract. Also
   entry_scratch_sequence covers straight instruction sequences, not CFG
   reachability; no arbitrary-path readiness theorem is claimed here.
*)

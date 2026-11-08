(* Successful typed-prefix traversal of allocated decoder arrays. *)
Theory abiValidAllocatedArrayLoop
Ancestors
  abiValidAllocatedArrayPrefix abiValidAllocatedArraySource abiValidAllocatedMembers
  abiMalformedTraversal abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiDecoderExecution abiDecoderLoop abiDecoderContract abiDecoderReentry
  abiValidAllocatedContract abiDecoderArrayBackedge abiMalformedMemberSetup
  abiDecoderDynamicLoopSetup abiDecoderReentryAddress abiDecoderOffset
  abiDecoderIndexedAddress localPtrsProps emitHelperProps abiMalformedNavigation
  exprSimDefs exprLoweringProps compileEnv venomState venomMemDefs venomMemProps
  valueEncodingProps valueEncoding venomExecSemantics finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_backedge_effect:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ st.cs_next_var <= first /\ first <= next /\
  next < ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\ inst.inst_id IN sites ==>
  abi_valid_allocated_effect ctx func cenv cx es first sites dstid 0 0 s
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s))) /\
  fresh_vars_wrt ceiling
    (jump_to hdr (mstore slot w (update_var (STRING #"%" (toString next)) w s)))
Proof
  strip_tac >> drule_all abi_malformed_backedge_resource >>
  disch_then (qspecl_then [`w`, `hdr`, `dstid`] strip_assume_tac) >>
  simp[abi_valid_allocated_effect_def] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  simp[abi_valid_allocated_frame_def] >> rpt strip_tac >>
  `a+1 <= slot \/ slot+32 <= a` by
    (qpat_x_assum `~abi_malformed_site_range _ _ _ _ _` mp_tac >>
     simp[abi_malformed_site_range_def, jump_to_def, mstore_def,
       update_var_def, write_memory_with_expansion_def] >>
     rpt strip_tac >>
     Cases_on `a+1 <= slot \/ slot+32 <= a` >> simp[] >>
     `slot <= a /\ a+1 <= slot+32` by decide_tac >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s`, `w` |-> `w`, `p` |-> `slot`,
    `q` |-> `a`, `n` |-> `1`] mstore_mem_bytes_at_disjoint) >>
  simp[mstore_def, update_var_def, write_memory_with_expansion_def]
QED

(* Scratch-only effects preserve every initialized destination element. *)
Theorem abi_valid_allocated_array_prefix_scratch:
  abi_valid_allocated_array_prefix tv vs j d s /\
  EVERY (val_wf tv) vs /\
  abi_valid_allocated_frame sites 0 0 s t /\ alloca_inv s /\
  FLOOKUP s.vs_allocas aid = SOME (B,cap) /\ aid NOTIN sites /\
  B <= d /\ d+32+j*type_memory_size tv <= B+cap ==>
  abi_valid_allocated_array_prefix tv vs j d t
Proof
  strip_tac >> irule abi_valid_allocated_array_prefix_frame >>
  qpat_assum `abi_valid_allocated_frame _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas aid = _` (irule_at Any) >> simp[]
QED

(* Reassemble the loop invariant after an independently framed phase. *)
Theorem abi_valid_allocated_array_inv_resume:
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin j s /\
  abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
    sites dstid d outsz s u /\
  abi_valid_allocated_array_prefix tv vs k d u /\
  eval_operand ip u = SOME (n2w slot) /\ mload slot u = n2w k /\
  fresh_vars_wrt ceiling u /\ ~u.vs_halted /\
  u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 ==>
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin k u
Proof
  strip_tac >>
  qhdtm_x_assum `abi_valid_allocated_array_inv`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_valid_allocated_array_inv_def]) >>
  `abi_malformed_resource_post ctx func cenv cx es start.cs_next_var
     sites dstid s u` by fs[abi_valid_allocated_effect_def] >>
  `abi_malformed_entry ctx func cenv cx es start sites dstid live
    base_op hi src dst B L xs p d outsz u` by
    (irule abi_malformed_aggregate_reentry >> simp[] >>
     fs[abi_malformed_entry_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz origin u` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `s` >> simp[]) >>
  simp[abi_valid_allocated_array_inv_def] >>
  fs[abi_malformed_resource_post_def]
QED

Theorem abi_valid_allocated_array_backedge_advance:
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin j s /\
  abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
    sites dstid d outsz s u /\
  abi_valid_allocated_array_prefix tv vs (SUC j) d u /\
  EVERY (val_wf tv) vs /\ 32+SUC j*type_memory_size tv <= outsz /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt ceiling u /\ ~u.vs_halted /\
  abi_decoder_operand_live start.cs_next_var ip /\
  start.cs_next_var <= next /\ next < ceiling.cs_next_var ==>
  abi_valid_allocated_array_inv ctx func cenv cx es start ceiling
    sites dstid live base_op hi src dst B L xs p d outsz
    ip slot inst q hdr tv vs origin (SUC j)
    (jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString next)) (n2w (SUC j)) u)))
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv start /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32) /\
   MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
   inst.inst_id IN sites` by
    (fs[abi_valid_allocated_array_inv_def, abi_valid_allocated_effect_def,
        abi_malformed_entry_def, abi_malformed_resource_post_def] >> metis_tac[]) >>
  `start.cs_next_var <= start.cs_next_var` by simp[] >>
  drule_all abi_valid_allocated_backedge_effect >>
  disch_then (qspecl_then [`n2w (SUC j)`, `hdr`, `dstid`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `abi_valid_allocated_effect ctx func cenv cx es
    start.cs_next_var sites dstid 0 0 u v` >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz u v` by
    fs[abi_valid_allocated_effect_def, abi_valid_allocated_frame_def] >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz s v` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `u` >> simp[]) >>
  `abi_malformed_destination func cenv es.scopes dstid d outsz u /\
    dstid NOTIN sites` by
    (fs[abi_valid_allocated_array_inv_def, abi_valid_allocated_effect_def,
        abi_malformed_entry_def] >>
     irule abi_malformed_resource_destination >>
     metis_tac[]) >>
  `abi_valid_allocated_array_prefix tv vs (SUC j) d v` by
    (irule abi_valid_allocated_array_prefix_scratch >>
     `abi_valid_allocated_frame sites 0 0 u v` by fs[abi_valid_allocated_effect_def] >>
     pop_assum (irule_at Any) >>
     fs[abi_malformed_destination_def, stmt_state_rel_def] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  irule abi_valid_allocated_array_inv_resume >>
  qhdtm_assum `abi_valid_allocated_array_inv` (irule_at Any) >>
  simp[] >>
  fs[abi_valid_allocated_effect_def, abi_malformed_resource_post_def,
     abi_valid_allocated_array_inv_def] >>
  simp[Abbr `v`, abi_decode_mload_jump, mload_mstore_same,
       jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

(* The successful pointer guard eliminates the malformed setup's abort arm. *)
Theorem abi_valid_allocated_dynamic_setup:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,en) /\
  dec_info_needs_offset di /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  eval_operand ip s = SOME ipw /\ mload (w2n ipw) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var ip /\
  p+32+j*asz+32 <= L /\ p+32+off+asz <= L /\
  off = abi_head_word (DROP (p+32+j*asz) xs) /\
  d+32+j*msz+childsz <= d+outsz /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_entry ctx func cenv cx es en sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs
      (p+32+off) (d+32+j*msz) childsz t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand ip t = SOME ipw /\ fresh_vars_wrt ceiling t /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w p) /\ eval_operand dst s = SOME (n2w d) /\
   eval_operand base_op s = SOME (n2w B) /\ eval_operand hi s = SOME (n2w L) /\
   B+L < dimword (:256) /\ mem_bytes_at B L (abi_decode_source MLOAD s) = xs /\
   EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst]` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def, abi_decode_source_def] >>
  `abi_decode_load MLOAD (n2w (B+(p+32+j*asz)):bytes32) s = n2w off` by
    (metis_tac[abi_checked_offset_load]) >>
  qhdtm_assum `EVERY` (strip_assume_tac o PURE_REWRITE_RULE [EVERY_DEF]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi s = SOME (n2w hb) /\
    p+32+off+asz <= hb /\ hb < dimword (:256)`` assume_tac
  >- (disj2_tac >> qexists_tac `L` >> simp[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynamic_element_setup_reentry >> strip_tac >>
  qpat_x_assum `hi = Lit 0w \/ _` kall_tac >>
  `stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv st` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    (irule abi_malformed_setup_resource >>
     qhdtm_assum `abi_decode_array_element_setup` (irule_at Any) >> simp[]) >>
  `st.cs_next_var <= en.cs_next_var` by
    (drule abi_decode_dynamic_element_setup_counters >> strip_tac >>
     Cases_on `base_op = Lit 0w` >> fs[] >> decide_tac) >>
  `local_ptrs_reserved cenv en` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `eval_operand ip t = SOME ipw` by
    (fs[abi_decoder_address_frame_def] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `t` >> simp[] >> irule abi_malformed_child_entry >>
  qhdtm_assum `abi_malformed_entry` (irule_at Any) >>
  qhdtm_assum `abi_malformed_resource_post` (irule_at Any) >>
  fs[abi_malformed_entry_def, EVERY_DEF] >>
  rpt conj_tac >> TRY (irule abi_decoder_operand_live_mono >>
    qexists_tac `st.cs_next_var` >> simp[] >> NO_TAC) >> decide_tac
QED

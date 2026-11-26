(* Normalize the physical unwrap at its selected exit, without advancing the row. *)
Theory bodyAbiTupleUnwrapNormalizeMods
Ancestors
  bodyAbiTupleRowRestoreMods bodyAbiTupleBufferStateMods abiEncodeValuesRun
  exprSimSubscriptArrayFrame exprLoweringProps localPtrsProps stateRelProj
  loweringStateRelDefs loweringPosts finite_map list arithmetic

Theorem unwrap_local_region_separation[local]:
  local_ptrs_reserved ce a /\ wb_frame ce ee ee a u z /\
  local_ptrs_rel func ce ee.scopes u /\ local_ptrs_rel func ce ee.scopes z /\
  venomMemDefs$alloca_inv z /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [out] /\
  not_local_ptr ce ee.scopes out /\ FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) ==>
  !name p k. local_region ce ee.scopes u name p k ==> p+k <= b \/ b+n <= p
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  `local_region ce ee.scopes z name p k` by
    (drule_all_then (fn th => simp[th]) local_region_wb_frame) >>
  once_rewrite_tac[DISJ_COMM] >>
  pure_rewrite_tac[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  irule local_ptrs_rel_alloca_disjoint >>
  qpat_assum `FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n)` (irule_at Any) >>
  qpat_assum `inst.inst_outputs = [out]` (irule_at Any) >>
  qpat_assum `local_region ce ee.scopes z name p k` (irule_at Any) >>
  qpat_assum `local_ptrs_rel func ce ee.scopes z` (irule_at Any) >>
  simp[]
QED

Theorem abi_tuple_materialized_unwrap_normalize_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace /\
       stmt_state_rel H ctx func ce cx ee s) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ ci_mono a r /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = a.cs_next_id /\ a.cs_next_id < r.cs_next_id /\
  inst.inst_operands = [Lit szw] /\ inst.inst_outputs = [out] /\
  not_local_ptr ce ee.scopes out /\
  exec_alloca inst u szw = OK mid /\ copy_static z = copy_static mid /\
  FLOOKUP z.vs_allocas a.cs_next_id = SOME (b,n) /\ lo <= b /\
  (!id pair. FLOOKUP u.vs_allocas id = SOME pair ==> FLOOKUP z.vs_allocas id = SOME pair) /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= b \/ b+n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
  (!i. i < b \/ b+n <= i ==> i IN tz.t_mem ==> i IN tu.t_mem) /\
  (!x. not_fresh_at a x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
     op_taint tz (Var x) = op_taint tu (Var x)) /\
  tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
  ~z.vs_halted /\ z.vs_current_bb = r.cs_current_bb /\
  z.vs_inst_idx = LENGTH r.cs_current_insts /\ return_buf_frame d ce r z /\
  wb_frame ce ee ee a u z /\ ghost_kept_at lo ce ee a Gu tu u Gz tz /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu /\
  MEM owner (fn_insts func) /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP u.vs_allocas owner.inst_id = SOME (pbase,capacity) /\
  owner.inst_id < a.cs_next_id /\
  MEM cur (fn_insts func) /\ cur.inst_id = loc /\
  cur.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  pbase + dst_offset + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  pbase + dst_offset + hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix r z Gz tz /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset
    loc a u Gu tu r z Gz tz /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i r z Gz tz
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!j. j < b \/ b+n <= j ==>
    mem_bytes_at j 1 z.vs_memory = mem_bytes_at j 1 u.vs_memory` by
    (gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`j`,`1`] irule) >> decide_tac) >>
  `(loc = a.cs_next_id ==> n = 32)` by
    (`FLOOKUP u.vs_allocas loc = SOME (slot,32)` by
       (qhdtm_assum `abi_encode_values_prefix_at`
          (strip_assume_tac o REWRITE_RULE[abi_encode_values_prefix_at_def]) >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `!id pair. FLOOKUP u.vs_allocas id = SOME pair ==> _`
       (qspec_then `loc` (drule_then assume_tac)) >>
     disch_tac >> fs[]) >>
  `local_ptrs_reserved ce a` by
    (irule local_ptrs_reserved_next_var >> qexists `se` >>
     qhdtm_assum `abi_tuple_buffer_state_mods`
       (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >> simp[]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace /\ _`
    (qx_choose_then `hz` strip_assume_tac) >>
  `!name p k. local_region ce ee.scopes u name p k ==> p+k <= b \/ b+n <= p` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u`
       (drule_then (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ z /\ _`
       (drule_then (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca o CONJUNCT1)) >>
     rpt gen_tac >> disch_tac >>
     irule unwrap_local_region_separation >>
     qpat_assum `inst.inst_outputs = [out]` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee a u z` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func ce ee.scopes u` (irule_at Any) >>
     qpat_assum `local_region ce ee.scopes u _ _ _` (irule_at Any) >>
     simp[]) >>
  irule abi_tuple_unwrap_endpoint_packet_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (irule_at Any o SPEC_ALL) >>
  qpat_assum `exec_alloca inst u szw = OK mid` (irule_at Any) >>
  qpat_assum `cur.inst_id = loc` (irule_at Any) >>
  qpat_assum `inst.inst_outputs = [out]` (irule_at Any) >>
  qpat_assum `cur.inst_outputs = [cursor_var]` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas a.cs_next_id = SOME (b,n)` (irule_at Any) >>
  qpat_assum `FLOOKUP u.vs_allocas owner.inst_id = SOME (pbase,capacity)` (irule_at Any) >>
  qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
  asm_rewrite_tac[] >> simp[]
QED

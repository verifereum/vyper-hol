Theory bodyIntCallReturnPrefixMods
Ancestors
  bodyIntCallStagePacketMods bodyCreateAllocBufferEntryMods
  bodyAbiTupleBufferStateMods fragGasOriginPtr wordArgsPtr exprSimWordArgs
  valueEncodingDefs ptrDiscipline exprLoweringProps loweringHalt freshWrites
  loweringStateRelDefs vyperStorageFootprint venomExecSemantics venomInst
  finite_map words venomState bodyFullShadowBodyInv bodyPtrDefs

(* Reserve result space before evaluating any actual argument. The pin is
   retained even in the register-return convention, where it is not in argv. *)
Theorem intcall_return_prefix_mods:
  let cap = if 0 < (ret_count:num) then 32 * ret_count else rbs in
  (if 0 < cap then ?buf. compile_alloc_buffer cap sa = (buf,s2) else s2 = sa) /\
  cap < dimword (:256) /\ fn_has_code sa s2 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
    (sa,ee,s,G,tn) (sa,ee,s,G,tn) NONE ==>
  ?u Gu tu pin.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    intcall_stage_frame_mods (DF,lo,d,ctx,func) ce cx st0
      (sa,ee,s,G,tn) (s2,ee,u,Gu,tu) pin /\
    intcall_stage_ops_mods (lo,func) ce cx sa (s2,ee,u,Gu,tu) pin ([],[],[],[],[]) /\
    local_ptrs_reserved ce s2 /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
    (if 0 < cap then
       ?buf root b inst.
         compile_alloc_buffer cap sa = (buf,s2) /\ buf.buf_operand = Var root /\
         buf.buf_size = cap /\ pin = SOME (root,b,cap) /\ ptr_covers Gu tu root u cap /\
         b+cap < dimword (:256) /\ MEM inst (fn_insts func) /\
         inst.inst_opcode = ALLOCA /\ inst.inst_id = sa.cs_next_id /\
         inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root
     else pin = NONE /\ (u,Gu,tu) = (s,G,tn))
Proof
  pure_rewrite_tac [LET_THM] >> qabbrev_tac `cap = if 0 < (ret_count:num) then 32 * ret_count else rbs` >>
  Cases_on `0 < cap` >> simp[] >> disch_then (map_every assume_tac o CONJUNCTS)
  >- (qpat_x_assum `?buf. compile_alloc_buffer _ _ = _` (qx_choose_then `buf` assume_tac) >>
      suspend "alloc") >>
  simp[intcall_stage_ops_mods_def, eval_operands_def] >>
  qhdtm_assum `intcall_stage_frame_mods` mp_tac >>
  fs[intcall_stage_frame_mods_def, cj 1 gas_origin_ptr_path_rules]
QED

Resume intcall_return_prefix_mods[alloc]:
  qpat_assum `intcall_stage_frame_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intcall_stage_frame_mods_def, optionTheory.option_case_def]) >>
  qpat_assum `storage_trace_domain _ _ _`
    (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    immutable_frame_mods func ce cx ee s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ immutable_frame_mods _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then
    (qspecl_then [`explicit`,`PG`]
      (qx_choosel_then [`root`,`b`,`inst`,`u`,`Gu`,`tu`] strip_assume_tac))
    create_alloc_buffer_entry_mods >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `!n base sz. local_region ce ee.scopes s n base sz <=>
              local_region ce ee.scopes u n base sz` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions) >>
     qpat_assum `wb_frame _ _ _ _ s u` (irule_at Any) >>
     qexistsl [`func`,`cx`,`ctx`,`storage_trace_horizon ee.storage_trace`] >> simp[]) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `lookup_var root u = SOME (n2w b)` by fs[eval_operand_def] >>
  `op_taint tu (Var root) = {}` by fs[ptr_covers_def] >>
  `buf.buf_size = cap` by drule_then (ACCEPT_TAC o cj 2) compile_alloc_buffer_parts >>
  `local_ptrs_reserved ce s2` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  qexistsl [`u`,`Gu`,`tu`,`SOME (root,b,cap)`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "packet" >>
  conj_tac >- simp[intcall_stage_ops_mods_def, eval_operands_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  qexistsl [`buf`,`root`,`b`,`inst`] >> simp[]
QED

Resume intcall_return_prefix_mods[packet]:
  simp[intcall_stage_frame_mods_def] >>
  conj_tac >- (pure_rewrite_tac[GSYM regions_disjoint_def] >> first_assum ACCEPT_TAC) >>
  simp[arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise intcall_return_prefix_mods

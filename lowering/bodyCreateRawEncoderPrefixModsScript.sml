(* Compose the registered RawCreate allocation, MCOPY and payload cursor ADD. *)
Theory bodyCreateRawEncoderPrefixMods
Ancestors
  bodyCreateAllocBufferEntryMods bodyCreateRawPrefixCopyMods
  bodyCreateRawPrefixOffsetMods bodyAbiTupleBufferResourcesMods
  abiDecodeValidFiniteLoop fragGasOriginPtrLoop appendStorageGhostPtr
  bodyAbiTupleBufferStateMods vyperStorageFootprint ptrDiscipline
  freshWrites exprLoweringProps bodyMemoryDefs context compileEnv words venomState
Libs horizonTypeLib

Theorem raw_create_encoder_saved_prefix_mods:
  compile_alloc_buffer cap se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) len a = ((),b) /\
  emit_op ADD [buf.buf_operand;len] b = (op,c) /\
  fn_has_code a b func /\ fn_has_code b c func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  LENGTH bs <= cap /\ cap < dimword (:256) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    immutable_frame_mods func ce cx ee s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  not_fresh_at se src /\ (!x. len = Var x ==> not_fresh_at se x) /\
  (!label. len <> Label label) /\ source < dimword (:256) /\
  lookup_var src s = SOME (n2w source) /\ ptr_covers G tn src s (LENGTH bs) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\ op_taint tn len = {} /\ op_prov G len = NONE /\
  read_memory source (LENGTH bs) s = bs /\ source + LENGTH bs <= s.vs_alloca_next /\
  (!i. source <= i /\ i < source+LENGTH bs ==> i NOTIN tn.t_mem) ==>
  ?root dst pbase inst z Gz tz.
    buf.buf_operand = Var root /\ op = Var dst /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase cap root dst (LENGTH bs) bs c z Gz tz /\
    eval_operand len z = SOME (n2w (LENGTH bs)) /\ op_taint tz len = {} /\ op_prov Gz len = NONE /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?H. valid_horizon cx st0 H ee.storage_trace` by
    (qexists `storage_trace_horizon ee.storage_trace` >> fs[storage_trace_domain_def]) >>
  drule_all create_alloc_buffer_entry_mods >>
  disch_then (qspecl_then [`ARB`,`PG`]
    (qx_choosel_then [`root`,`pbase`,`inst`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (qhdtm_assum `abi_tuple_buffer_state_mods`
       (strip_assume_tac o REWRITE_RULE[abi_tuple_buffer_state_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand len u = SOME (n2w (LENGTH bs)) /\ op_taint tu len = {} /\ op_prov Gu len = NONE` by
    (Cases_on `len` >> fs[eval_operand_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  `lookup_var src u = SOME (n2w source)` by
    (qpat_assum `!x. not_fresh_at se x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `ptr_covers Gu tu src u (LENGTH bs)` by
    (irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`se`,`tn`] >> simp[]) >>
  `read_memory source (LENGTH bs) u = bs` by fs[read_memory_def] >>
  `source + LENGTH bs <= u.vs_alloca_next` by decide_tac >>
  `!i. source <= i /\ i < source+LENGTH bs ==> i NOTIN tu.t_mem` by
    (rpt strip_tac >>
     `i < s.vs_alloca_next` by decide_tac >>
     qpat_assum `!j. j IN tu.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `!j. source <= j /\ j < source+LENGTH bs ==> _` (qspec_then `i` mp_tac) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  `compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
   emit_op ADD [Var root;len] b = (op,c)` by gvs[] >>
  qpat_assum `inst.inst_id = se.cs_next_id` (fn th =>
    qhdtm_assum `abi_tuple_buffer_state_mods` (assume_tac o PURE_REWRITE_RULE [GSYM th])) >>
  drule raw_create_prefix_copy_mods >>
  disch_then (drule_at (Pat `compile_copy_memory_dynamic (Var _) (Var _) _ _ = _`)) >>
  disch_then (drule_at (Pat `read_memory _ _ _ = _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (simp[] >> qexists `H` >> simp[])) >>
  disch_then (strip_assume_tac o SIMP_RULE pure_ss [LET_THM]) >>
  qabbrev_tac `v = mcopy pbase source (LENGTH bs) u with vs_inst_idx := LENGTH b.cs_current_insts` >>
  qabbrev_tac `tv = tu with t_mem := tu.t_mem DIFF {i | pbase <= i /\ i < pbase+LENGTH bs}` >>
  suspend "add"
QED

Resume raw_create_encoder_saved_prefix_mods[add]:
  `ci_mono se a` by
    (qspecl_then [`cap`,`se`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono a b` by
    (qpat_assum `compile_copy_memory_dynamic (Var root) _ _ _ = _`
       (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     qspecl_then [`MCOPY`,`[Var root;Var src;len]`,`a`] mp_tac ci_mono_emit_void >> simp[]) >>
  `se.cs_next_var <= b.cs_next_var` by fs[ci_mono_def] >>
  `!x. len = Var x ==> not_fresh_at b x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `se` >> simp[]) >>
  `allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 [] b v _ _`
       (mp_then Any mp_tac abi_tuple_buffer_resources_mods) >>
     (impl_tac >- (qexists `H` >> simp[])) >> simp[]) >>
  drule_all raw_create_prefix_offset_mods >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`dst`,`z`,`Gz`,`tz`] strip_assume_tac)) >>
  qpat_assum `inst.inst_id = se.cs_next_id` (fn th =>
    qhdtm_assum `abi_tuple_buffer_state_mods` (assume_tac o PURE_REWRITE_RULE [th])) >>
  qexistsl [`root`,`dst`,`pbase`,`inst`,`z`,`Gz`,`tz`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac) >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    metis_tac[finite_array_empty_path_explicit] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gu,tv)` by
    (irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`v`,`tv`] >> simp[]
QED

Finalise raw_create_encoder_saved_prefix_mods

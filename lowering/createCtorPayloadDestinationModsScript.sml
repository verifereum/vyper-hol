(* Select the saved encoder state at the observed constructor prologue cut. *)
Theory createCtorPayloadDestinationMods
Ancestors
  createCtorRawEntryMods createCtorBlueprintEntryMods venomInst words

Theorem ctor_payload_destination_post_mods:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK sa') /\
  (if raw then
    compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
    fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
    fn_has_code b st func /\ w2n nword <= capacity /\
    not_fresh_at se src /\ not_fresh_at se len /\
    lookup_var src s = SOME p /\ lookup_var len s = SOME nword /\
    ptr_covers G tn src s (w2n nword) /\ op_taint tn (Var len) = {} /\
    w2n p + w2n nword <= s.vs_alloca_next /\
    gas_origin_edge F explicit ctx func sa' bm (OK sb') /\
    gas_origin_edge F explicit ctx func sb' cm (OK u)
   else st = a /\ dst_op = buf.buf_operand /\ u = sa') ==>
  ?root dst pbase inst Gu tu.
    buf.buf_operand = Var root /\ dst_op = Var dst /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst (if raw then w2n nword else 0) [] st u Gu tu /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu))
Proof
  Cases_on `raw` >> simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (drule_all ctor_raw_destination_actual_mods >>
      disch_then (qspec_then `PG` (qx_choosel_then
        [`root`,`pbase`,`dst`,`Gu`,`tu`,`inst`] strip_assume_tac)) >>
      qexistsl_tac [`root`,`dst`,`pbase`,`inst`,`Gu`,`tu`] >> simp[mk_inst_def]) >>
  drule_all (Q.INST [`F` |-> `F`, `explicit` |-> `explicit`, `PG` |-> `PG`]
                  ctor_encoder_blueprint_entry_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then
    [`root`,`pbase`,`entry`,`Gu`,`tu`,`inst`] strip_assume_tac)) >>
  `sa' = entry` by
    (qpat_assum `!ms v. gas_origin_edge F explicit ctx func s ms (OK v) ==> _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`,`root`,`pbase`,`inst`,`Gu`,`tu`] >> simp[mk_inst_def]
QED

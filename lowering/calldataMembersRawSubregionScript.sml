(* Logical root coverage is independent of the physical allocation extent. *)
Theory calldataMembersRawSubregion
Ancestors
  calldataChildFrame bodyPtrBytestringBuiltinsWindowGhost assignTuplePtrCopyLen
  exprSimProps abiDecoderContract abiDecoderFrame actualAllocExec valueEncodingDefs
  compileEnv exprLowering freshWrites ptrDiscipline bodyPtrDefs
  venomState venomExecSemantics venomInst loweringStateRelDefs
  words finite_map pred_set list arithmetic

Theorem calldata_member_raw_prefix_frame_subregion:
  abi_decode_footprint_frame ((d,sz)::scratch) s t /\ alloca_inv t /\
  (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  (!q len. MEM (q,len) scratch ==>
    ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,len)) /\
  EVERY (\(tv,x,b). base_addr <= b /\
    b + type_memory_size tv <= base_addr + cap /\
    (b + type_memory_size tv <= d \/ d + sz <= b) /\ val_wf tv x /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv x b m)) prefix /\
  u.t_mem SUBSET tn.t_mem /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) /\
  (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
    FLOOKUP u.t_var name = FLOOKUP tn.t_var name) /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\ not_fresh_at st root /\
  ptr_covers G tn root s root_extent /\
  abi_decoder_operand_live st.cs_next_var src /\
  (!name. src = Var name ==> not_fresh_at st name) /\
  op_taint tn src = {} /\ op_prov G src = NONE ==>
  FLOOKUP t.vs_allocas oid = SOME (base_addr,cap) /\
  ptr_covers H u root t root_extent /\
  eval_operand src t = eval_operand src s /\
  op_taint u src = {} /\ op_prov H src = NONE /\
  t.vs_call_ctx = s.vs_call_ctx /\
  EVERY (\(tv,x,b). !m. mem_agree_outside u.t_mem t.vs_memory m ==>
    val_in_memory tv x b m) prefix
Proof
  strip_tac >>
  `lookup_var root t = lookup_var root s /\
   FLOOKUP H root = FLOOKUP G root /\
   op_taint u (Var root) = op_taint tn (Var root)` by
    (gvs[op_taint_def] >> metis_tac[eval_operand_def]) >>
  `ptr_covers H u root t root_extent` by metis_tac[ptr_covers_lookup_frame] >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by fs[abi_decode_footprint_frame_def] >>
  simp[EVERY_MEM] >> qx_gen_tac `e` >> disch_tac >> PairCases_on `e` >>
  qpat_x_assum `EVERY _ prefix` mp_tac >> rewrite_tac[EVERY_MEM] >>
  disch_then (qspec_then `(e0,e1,e2)` mp_tac) >> simp[] >> strip_tac >>
  `mem_bytes_at e2 (type_memory_size e0) t.vs_memory =
   mem_bytes_at e2 (type_memory_size e0) s.vs_memory` by
    (irule (cj 2 calldata_child_preserves_allocated_region) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`base_addr`,`cap`,`d`,`last.cs_next_id`,`st.cs_next_id`,
       `oid`,`scratch`,`sz`] >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  irule robust_val_in_memory_window_transport >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`tn.t_mem`,`u.t_mem`,`type_memory_size e0`,`s.vs_memory`,`t.vs_memory`] >>
  simp[val_footprint_le] >> fs[SUBSET_DEF] >> metis_tac[]
QED

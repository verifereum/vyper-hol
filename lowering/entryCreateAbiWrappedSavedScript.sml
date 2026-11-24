(* Interpret the indexed saved-value encoder at the wrapped AbiEncode payload. *)
Theory entryCreateAbiWrappedSaved
Ancestors
  createCtorEncoderLength entryCreateFocusSpec entryCreatePathScope
  entryCreateStmtCases createSizeEncodeCode createSizeCutRegion
  exprLowering fragExec abiEncoderProps

Definition abi_wrapped_fenced_scope_def:
  abi_wrapped_fenced_scope explicit ctx func a b r z <=>
    ((!bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
             get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
             b.cs_next_id <= j.inst_id) ==>
     create_operand_full_scope a b explicit ctx func r [] (OK z))
End

(* The row is scoped when its actual exit is fenced. The fold's own
   exit fence is supplied by the installed finish. *)
Theorem abi_wrapped_payload_from_saved_laws:
  ctor_saved_row_law ctx func ce cx DF lo explicit PG
    (abi_wrapped_fenced_scope explicit ctx func) /\
  ctor_saved_fold_law ctx func ce cx DF lo explicit PG
    (abi_wrapped_fenced_scope explicit ctx func)
    (abi_wrapped_fenced_scope explicit ctx func) /\
  (!bb j. lookup_block body_end.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH body_end.cs_current_insts) = SOME j ==>
          body_end.cs_next_id <= j.inst_id) /\
  body_inv tops ctx ce cx /\
  (!e. MEM e args ==> ?es'. expr_body_pre ce cx env e es') /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    extcall_positional_post T DF lo d ctx func ce cx env [] args svs sa st es s0 G0 tn0
      H (INL vs) ee G1 tn1 t) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ann.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
    value_has_type tv (EL i vs)) /\
  tys = MAP (lowered_value_type ce) args /\
  ats = vyper_to_abi_types (get_tenv cx) tys /\
  vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) (ZIP (svs,tys)) ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= capacity-(32+k) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d st t G1 tn1
    st.cs_next_id pbase capacity root dst (32+k) prefix ready pre Gpre tnpre /\
  local_ptrs_reserved ce st /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = st.cs_next_id /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_payload ce F svs tys (Var dst) ready = (alen,body_end) /\
  fn_has_code ready body_end func ==>
  ?q Gq tq.
    (pure_frame ce func ee st pre q /\ wb_frame ce ee ee st pre q) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d st t G1 tn1
      st.cs_next_id pbase capacity root dst (32+k) prefix body_end q Gq tq /\
    eval_operand alen q = SOME (n2w (LENGTH bytes)) /\ op_taint tq alen = {} /\
    (!x. alen = Var x ==> not_fresh_at body_end x) /\
    mem_bytes_at (pbase+(32+k)) (LENGTH bytes) q.vs_memory = bytes /\
    (!j. pbase+(32+k) <= j /\ j < pbase+(32+k) + LENGTH bytes ==> j NOTIN tq.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (pre,Gpre,tnpre) [] (OK q,Gq,tq)) /\
    create_operand_full_scope ready body_end explicit ctx func pre [] (OK q)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_abi_encode_values_to_buf ce (Var dst) (ZIP (svs,tys)) ready = (alen,body_end)` by
    fs[compile_abi_encode_payload_def] >>
  `!a r z. abi_wrapped_fenced_scope explicit ctx func a body_end r z <=>
      create_operand_full_scope a body_end explicit ctx func r [] (OK z)` by
    simp[abi_wrapped_fenced_scope_def] >>
  qpat_x_assum `!a r z. abi_wrapped_fenced_scope _ _ _ _ _ _ _ <=> _`
    (pure_rewrite_tac o single o GSYM) >>
  irule ctor_encoder_length_witness_from_saved_laws >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `inst` >> asm_rewrite_tac[])
  >- (qexistsl_tac [`G0`,`args`,`ats`,`avs`,`env`,`es`,`T`,`ZIP (svs,tys)`,
                    `s0`,`sa`,`svs`,`tn0`,`vs`] >>
      qpat_assum `tys = MAP _ args` (pure_rewrite_tac o single o GSYM) >>
      rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC))
  >- (qexists_tac `tops` >> first_assum ACCEPT_TAC) >>
  qexists_tac `abi_wrapped_fenced_scope explicit ctx func` >> asm_rewrite_tac[]
QED

(* Fetch ownership is static; it is also valid when the argument evaluation
   fails and this successful encoder witness does not exist. *)
Theorem abi_wrapped_payload_cut:
  compile_abi_encode_payload ce F svs tys dst ready = (alen,body_end) /\
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code ready body_end func /\
  (!i. MEM i (frag_code ready body_end) ==> ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) ==>
  create_operand_cut ready body_end explicit ctx func tops cx st0 source (es,s)
Proof
  strip_tac >>
  `create_cut_code {} ready body_end` by
    (qpat_assum `compile_abi_encode_payload _ _ _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     simp_tac std_ss [] >> disch_then (SUBST1_TAC o SYM) >>
     irule create_encode_payload_cut_code) >>
  rw[create_operand_cut_def] >>
  `create_operand_at ready s` by fs[create_interior_visit_def] >>
  drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region ready body_end s` by
    (qpat_assum `!u. _ /\ _ ==> create_cut_region ready body_end u` irule >>
     fs[create_operand_at_def]) >>
  `!left u i. create_expr_prefix ready body_end explicit ctx func s left u /\
              create_operand_fetch ready body_end func u i ==>
              ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]` by
    (rpt strip_tac >> drule_all create_expr_prefix_cut_region >> strip_tac >>
     fs[create_operand_fetch_def, create_operand_at_def] >>
     drule_all create_cut_region_rules >> metis_tac[]) >>
  drule create_interior_visit_cases >> rw[]
  >- (irule create_cut_noncreate_visit >> metis_tac[listTheory.MEM]) >>
  metis_tac[listTheory.MEM]
QED

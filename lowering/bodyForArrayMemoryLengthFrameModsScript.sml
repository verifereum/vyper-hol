(* Transport the linked landing over the fixed-length identity or memory
   header load, keeping the original statement frame as the anchor. *)
Theory bodyForArrayMemoryLengthFrameMods
Ancestors
  bodyForArrayLengthLinkedTransportMods bodyForArrayExprRunMods
  bodyFullTargetArrayLoad bodyForArrayHeaderMods bodyFullPostsMods
  context compileEnv emitHelperProps exprLoweringProps
  loweringPosts loweringStateRelDefs stmtSimProps fragGasOriginPtr
  ptrDiscipline venomState venomInst venomExecSemantics
  vyperStorageTrace vyperStorageFootprint finite_map list words

Theorem memory_length_code[local]:
  (case bd of Fixed k => comp_return (Lit (n2w k))
   | Dynamic _ => compile_ptr_load ctor imm LocMemory op) se = (len_op,saL) ==>
  saL.cs_current_bb = se.cs_current_bb /\
  saL.cs_current_insts = se.cs_current_insts ++ emitted_insts se saL /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts se saL)
Proof
  Cases_on `bd` >> simp[comp_return_def,compile_ptr_load_def]
  >- simp[emitted_insts_def] >>
  strip_tac >>
  drule emitted_insts_emit_op >>
  drule emit_op_same_blocks >>
  simp[same_blocks_def,mk_inst_def]
QED

Theorem memory_length_frame_effects[local]:
  array_length_frame se r Gr traw z Gz tz ==>
  z = r with <|vs_vars := z.vs_vars; vs_inst_idx := z.vs_inst_idx|> /\
  (!x. not_fresh_at se x ==> lookup_var x z = lookup_var x r /\
       FLOOKUP Gz x = FLOOKUP Gr x /\ op_taint tz (Var x) = op_taint traw (Var x)) /\
  tz.t_mem = traw.t_mem /\ tz.t_stor = traw.t_stor /\
  tz.t_trans = traw.t_trans /\ tz.t_imm = traw.t_imm
Proof
  simp[array_length_frame_def,op_taint_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem for_array_memory_length_frame_mods:
  (!h. valid_horizon cx st0 h em.storage_trace ==>
     for_array_expr_landed_mods (DF,lo,d,ctx,func) mods cx c env e vv se
       (es,sa0,s0,G0,tn0) h raw em Gr traw r) /\
  storage_trace_domain cx st0 em.storage_trace /\
  (case bd of Fixed k => comp_return (Lit (n2w k))
   | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory
                     (vv_operand vv)) se = (len_op,saL) /\
  fn_has_code se saL func /\ local_ptrs_reserved c se /\
  sa0.cs_next_var <= se.cs_next_var /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa0 x) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  array_length_frame se r Gr traw z Gz tz /\
  z.vs_inst_idx = LENGTH saL.cs_current_insts /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (r,Gr,traw) [] (OK z,Gz,tz)) ==>
  ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c em z /\
  (!fn inst q. frag_reachable ctx func z fn inst q ==> dalloca_fmp_headroom inst q) /\
  for_array_outer_frame_mods ctx func c sa0 es s0 G0 tn0 em Gz tz z /\
  (!h. valid_horizon cx st0 h em.storage_trace ==>
       stmt_state_rel h ctx func c cx em z /\ immutable_frame_mods func c cx em z /\
       storage_well_formed_on cx em (FST h) /\ ghost_inv_at_mods (DF h) lo d c cx em Gz tz z)
Proof
  strip_tac >>
  drule_then strip_assume_tac memory_length_code >>
  drule_then strip_assume_tac memory_length_frame_effects >>
  `!h. valid_horizon cx st0 h em.storage_trace ==>
       ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\ return_buf_sep d c em z /\
       stmt_state_rel h ctx func c cx em z /\ immutable_frame_mods func c cx em z /\
       storage_well_formed_on cx em (FST h) /\ ghost_inv_at_mods (DF h) lo d c cx em Gz tz z /\
       for_array_outer_frame_mods ctx func c sa0 es s0 G0 tn0 em Gz tz z /\
       (!fn inst q. frag_reachable ctx func z fn inst q ==> dalloca_fmp_headroom inst q)` by
    (qx_gen_tac `h` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_expr_landed_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [for_array_expr_landed_mods_def])) >>
     qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF h` assume_tac) >>
     irule for_array_length_linked_transport_mods >>
     qpat_assum `gas_origin_ptr_path _ _ _ _` (irule_at Any) >>
     qpat_assum `fn_has_code se saL func` (irule_at Any) >>
     qpat_assum `saL.cs_current_insts = _ ++ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> ret_pc_ok _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ret_pc_ok _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

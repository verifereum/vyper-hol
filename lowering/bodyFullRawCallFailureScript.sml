(* The failure branch forwards the actual returndata on the specified run. *)
Theory bodyFullRawCallFailure
Ancestors
  rawCallBufferPtr bodyFullAllocGeneric fragGasSeqPtr fragGasOriginPtr
  fragGasOrigin fragGasPathPtr fragExecMem fragExec gasEvents gasCount
  exprSimRawCallCalldata ptrSafetyTransport ptrSafeRun ptrDiscipline
  contextCodegenRel contextCodegenRelProps venomExecSemantics venomExecProps
  venomInstProps venomInstProofs venomState venomInst emitHelper compileEnv
  context exprLoweringProps instMemFrontier memSafeRun unitTransformDefs codegenRel
  ghostPcTransportPtr instIdxIndep
  finite_map rich_list list

Theorem raw_call_forward_pair_origin_ptr[local]:
 !ctx func PG lo explicit s G tn bb cid rid dst sz u t.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx = SOME (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) /\
 get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst rid REVERT [dst;sz] []) /\
 op_taint tn dst = {} /\ op_taint tn sz = {} /\
 step_inst_base (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) s = OK u /\
 step_inst_base (mk_inst rid REVERT [dst;sz] [])
   (u with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort t ==>
 !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
   (Abort Revert_abort t,
    step_prov PG G (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) u,
    step_taint (mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []) s u tn)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  qabbrev_tac `copy = mk_inst cid RETURNDATACOPY [dst;Lit 0w;sz] []` >>
  qabbrev_tac `rev = mk_inst rid REVERT [dst;sz] []` >>
  `step_inst 0 ctx copy s = OK u` by
    simp[Abbr `copy`, step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (drule step_preserves_halted >> drule step_preserves_control_flow >>
     simp[Abbr `copy`, is_terminator_def]) >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `in_revert_forward func s /\ in_revert_forward func v` by
    (conj_tac >> irule forwarding_pair_active >>
     simp[Abbr `v`] >>
     qexistsl_tac [`copy`,`s.vs_inst_idx`,`dst`,`sz`,`rev`] >>
     simp[Abbr `copy`, Abbr `rev`]) >>
  `about_to_revert func copy s` by
    (simp[about_to_revert_def, active_inst_def, Abbr `copy`] >>
     qexists_tac `rev` >> simp[Abbr `rev`] >> qexists_tac `bb` >>
     drule lookup_block_MEM >> drule lookup_block_label >>
     fs[get_instruction_def, AllCaseEqs()]) >>
  `allocas_from lo u` by
    (gvs[Abbr `copy`, step_inst_base_opcode_eqs, AllCaseEqs(),
         write_memory_with_expansion_def, write_memory_def, allocas_from_def] >>
     metis_tac[]) >>
  `access_ok lo G func copy s /\ taint_ok func tn copy s` by
    (irule revert_forward_access_taint >> simp[Abbr `copy`] >>
     simp[op_taint_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn copy s` by
    (simp[ptr_inst_ok_def] >>
     simp[Abbr `copy`, step_inst_non_invoke, step_inst_base_opcode_eqs,
          write_memory_with_expansion_def, write_memory_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs(),
       write_memory_with_expansion_def, write_memory_def]) >>
  `access_ok lo (step_prov PG G copy u) func rev v /\
   taint_ok func (step_taint copy s u tn) rev v` by
    (irule revert_forward_access_taint >>
     simp[Abbr `rev`, about_to_revert_def, forwarding_copy_operand_taint,
          Abbr `copy`]) >>
  `ptr_inst_ok D lo 0 ctx func (step_prov PG G copy u)
    (step_taint copy s u tn) rev v` by
    (simp[ptr_inst_ok_def, Abbr `v`, allocas_from_def] >>
     simp[Abbr `rev`, step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     gvs[allocas_from_def]) >>
  `revert_forward_at bb s.vs_inst_idx /\ revert_forward_at bb v.vs_inst_idx` by
    (simp[Abbr `v`] >> irule revert_forward_pair_adjacent >>
     metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK v,step_prov PG G copy u,step_taint copy s u tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
     >- (simp[gas_origin_edge_def] >> qexists_tac `0` >>
         simp[Abbr `copy`, Abbr `v`, gas_events_step_def, is_terminator_def,
              step_inst_non_invoke, exit_result_def]) >>
     simp[gas_path_ptr_edge_def] >> qexists_tac `0` >>
     simp[Abbr `copy`, Abbr `v`, is_terminator_def, gas_count_step_def,
          ptr_safe_step_def, step_inst_non_invoke, ghost_step_non_invoke,
          exit_result_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (v,step_prov PG G copy u,step_taint copy s u tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def,gas_origin_edge_def,gas_path_ptr_edge_def] >>
     conj_tac >> simp[Abbr `v`] >> qexists_tac `0` >>
     simp[Abbr `rev`, gas_events_step_def, gas_count_step_def,
          step_inst_non_invoke, ptr_safe_step_def, is_terminator_def, exit_result_def] >>
     gvs[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (v,step_prov PG G copy u,step_taint copy s u tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)` by
    metis_tac[gas_origin_ptr_path_rules,exit_result_def] >>
  metis_tac[gas_origin_ptr_path_rules,APPEND]
QED

Theorem raw_call_failure_block_origin_ptr:
 !ctx func PG lo explicit sa sz sp sc sb zop rb s G tn t.
 emit_op RETURNDATASIZE [] sa = (zop,sz) /\
 compile_alloc_buffer 0 sz = (rb,sp) /\
 emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sp = ((),sc) /\
 emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
 fn_has_code sa sb func /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 LENGTH s.vs_returndata < dimword (:256) /\
 run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t ==>
 ?Gf tnf.
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx + 3),Gf,tnf)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `z = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `p = STRING #"%" (toString (sa.cs_next_var + 1))` >>
  qabbrev_tac `readsz = mk_inst sa.cs_next_id RETURNDATASIZE [] [z]` >>
  qabbrev_tac `alloc = mk_inst (sa.cs_next_id+1) ALLOCA [Lit 0w] [p]` >>
  qabbrev_tac `copy = mk_inst (sa.cs_next_id+2) RETURNDATACOPY [Var p;Lit 0w;Var z] []` >>
  qabbrev_tac `rev = mk_inst (sa.cs_next_id+3) REVERT [Var p;Var z] []` >>
  `z <> p /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ [readsz;alloc;copy;rev] /\
   emitted_insts sa sb = [readsz;alloc;copy;rev]` by suspend "compile" >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME readsz /\
    get_instruction bb (s.vs_inst_idx+1) = SOME alloc /\
    get_instruction bb (s.vs_inst_idx+2) = SOME copy /\
    get_instruction bb (s.vs_inst_idx+3) = SOME rev` by suspend "placement" >>
  qabbrev_tac `a = update_var z (n2w (LENGTH s.vs_returndata)) s` >>
  `step_inst_base readsz s = OK a` by
    simp[Abbr `readsz`, Abbr `a`, step_inst_base_opcode_eqs, exec_read0_def] >>
  `?b pw. step_inst_base alloc a = OK b /\
    eval_operand (Var p) b = SOME pw /\
    eval_operand (Var z) b = SOME (n2w (LENGTH s.vs_returndata)) /\
    b.vs_returndata = s.vs_returndata` by suspend "allocate" >>
  `step_inst_base copy b = OK (write_memory_with_expansion (w2n pw) s.vs_returndata b) /\
   step_inst_base rev (write_memory_with_expansion (w2n pw) s.vs_returndata b) =
    Abort Revert_abort (revert_state (set_returndata s.vs_returndata
      (write_memory_with_expansion (w2n pw) s.vs_returndata b)))` by
    (simp[Abbr `copy`,Abbr `rev`] >> irule raw_call_revert_copy >> simp[]) >>
  `t = revert_state (set_returndata s.vs_returndata
      (write_memory_with_expansion (w2n pw) s.vs_returndata b))` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]) >>
  qabbrev_tac `a1 = a with vs_inst_idx := s.vs_inst_idx+1` >>
  qabbrev_tac `b2 = b with vs_inst_idx := s.vs_inst_idx+2` >>
  qabbrev_tac `G1 = step_prov PG G readsz a` >>
  qabbrev_tac `tn1 = step_taint readsz s a tn` >>
  qabbrev_tac `G2 = step_prov PG G1 alloc (b with vs_inst_idx := s.vs_inst_idx+1)` >>
  qabbrev_tac `tn2 = step_taint alloc a1 (b with vs_inst_idx := s.vs_inst_idx+1) tn1` >>
  qabbrev_tac `c2 = write_memory_with_expansion (w2n pw) s.vs_returndata b2` >>
  qexistsl_tac [`step_prov PG G2 copy c2`,`step_taint copy b2 c2 tn2`] >>
  gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a1,G1,tn1)` by
    suspend "read_edge" >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (a1,G1,tn1) [] (OK b2,G2,tn2)` by
    suspend "alloc_edge" >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (b2,G2,tn2) []
    (Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx+3),
     step_prov PG G2 copy c2,step_taint copy b2 c2 tn2)` by suspend "pair" >>
  metis_tac[gas_origin_ptr_path_rules,APPEND]
QED

Resume raw_call_failure_block_origin_ptr[compile]:
  qpat_x_assum `emit_op RETURNDATASIZE _ _ = _` mp_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  qpat_x_assum `emit_void RETURNDATACOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_inst REVERT _ _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt disch_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  fs[Abbr `z`,Abbr `p`,Abbr `readsz`,Abbr `alloc`,Abbr `copy`,Abbr `rev`,
       emitted_insts_def,ASCIInumbersTheory.toString_11,DROP_LENGTH_APPEND,
       GSYM APPEND_ASSOC] >>
  qpat_x_assum `_ = sz` (SUBST_ALL_TAC o SYM) >> fs[] >>
  qpat_x_assum `_ = zop` (SUBST_ALL_TAC o SYM) >> fs[] >>
  qpat_x_assum `_ = rb` (SUBST_ALL_TAC o SYM) >> fs[] >>
  qpat_x_assum `_ = sp` (SUBST_ALL_TAC o SYM) >> fs[] >>
  qpat_x_assum `_ = sc` (SUBST_ALL_TAC o SYM) >> fs[] >>
  qpat_x_assum `_ = sb` (SUBST_ALL_TAC o SYM) >>
  simp[GSYM APPEND_ASSOC,DROP_LENGTH_APPEND]
QED

Resume raw_call_failure_block_origin_ptr[placement]:
  drule_all fn_has_code_same_block >>
  simp[] >> strip_tac >> qexists_tac `bb` >> simp[] >>
  rpt conj_tac
  >- (qpat_x_assum `!i. i < 4 ==> _` (qspec_then `0` mp_tac) >> simp[]) 
  >- (qpat_x_assum `!i. i < 4 ==> _` (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD_COMM])
  >- (qpat_x_assum `!i. i < 4 ==> _` (qspec_then `2` mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `!i. i < 4 ==> _` (qspec_then `3` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Resume raw_call_failure_block_origin_ptr[allocate]:
  simp[Abbr `alloc`, step_inst_base_opcode_eqs, eval_operand_def,exec_alloca_def,
       instruction_accessors] >>
  Cases_on `FLOOKUP a.vs_allocas (sa.cs_next_id+1)` >>
  fs[Abbr `a`, update_var_def] >>
  simp[AllCaseEqs(), eval_operand_def,lookup_var_def,FLOOKUP_UPDATE] >>
  TRY (rename1 `FLOOKUP _ _ = SOME pairv` >> PairCases_on `pairv`) >>
  simp[mk_inst_def,FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume raw_call_failure_block_origin_ptr[read_edge]:
  qunabbrev_tac `a1` >> qunabbrev_tac `G1` >> qunabbrev_tac `tn1` >>
  qunabbrev_tac `readsz` >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD1] >>
  irule (SRULE [instruction_accessors,is_terminator_def]
    (Q.INST [`i` |-> `mk_inst sa.cs_next_id RETURNDATASIZE [] [z]`]
       straight_line_origin_ptr_edge)) >>
  fs[] >>
  simp[inst_mem_below_frontier_def,source_memory_read_ranges_def,
       source_memory_write_ranges_def,inst_dload_in_section_def,mk_inst_def,
       ptr_inst_ok_def,access_ok_def,taint_ok_def,op_taint_def,
       step_inst_non_invoke,step_inst_base_opcode_eqs,exec_read0_def,
       Abbr `a`,update_var_def,allocas_from_def] >>
  gvs[mk_inst_def]
QED
Resume raw_call_failure_block_origin_ptr[alloc_edge]:
  `step_inst_base alloc a1 = OK (b with vs_inst_idx := s.vs_inst_idx+1)` by
    (simp[Abbr `a1`,step_inst_inst_idx_indep,Abbr `alloc`,is_terminator_def,
          exec_result_map_def]) >>
  `~a1.vs_halted /\ allocas_from lo a1 /\ lo <= a1.vs_alloca_next /\
    a1.vs_current_bb = s.vs_current_bb` by
    (fs[Abbr `a1`,Abbr `a`,update_var_def,allocas_from_def] >> metis_tac[]) >>
  qunabbrev_tac `b2` >> qunabbrev_tac `G2` >> qunabbrev_tac `tn2` >>
  qunabbrev_tac `alloc` >> qunabbrev_tac `a1` >>
  pure_rewrite_tac[step_prov_inst_idx,step_taint_inst_idx] >>
  irule (SRULE [arithmeticTheory.ADD1,GSYM arithmeticTheory.ADD_ASSOC]
    (Q.INST [`s` |-> `a with vs_inst_idx := s.vs_inst_idx+1`,
             `u` |-> `b with vs_inst_idx := s.vs_inst_idx+1`]
       (SPEC_ALL ifexp_alloca_origin_ptr_edge))) >>
  gvs[]
QED
Resume raw_call_failure_block_origin_ptr[pair]:
  `step_inst 0 ctx alloc a = OK b` by
    simp[Abbr `alloc`,step_inst_non_invoke] >>
  `~a.vs_halted /\ allocas_from lo a /\ lo <= a.vs_alloca_next /\
    a.vs_current_bb = s.vs_current_bb` by
    (fs[Abbr `a`,update_var_def,allocas_from_def] >> metis_tac[]) >>
  `allocas_from lo b /\ ~b.vs_halted /\ b.vs_current_bb = s.vs_current_bb` by
    (drule_all step_inst_allocas_from >>
     drule step_preserves_halted >> drule step_preserves_control_flow >>
     simp[Abbr `alloc`,is_terminator_def]) >>
  `op_taint tn2 (Var p) = {} /\ op_taint tn2 (Var z) = {}` by
    (simp[Abbr `tn2`,Abbr `tn1`,Abbr `alloc`,Abbr `readsz`,
       step_taint_def,op_taint_def,set_var_taint_def,out_taint_def,
       eval_operand_def,FLOOKUP_UPDATE]) >>
  `step_inst_base copy b2 = OK c2` by
    simp[Abbr `b2`,Abbr `c2`,Abbr `copy`,is_terminator_def,
         step_inst_inst_idx_indep,exec_result_map_def] >>
  `step_inst_base rev (c2 with vs_inst_idx := SUC b2.vs_inst_idx) =
    Abort Revert_abort (t with vs_inst_idx := s.vs_inst_idx+3)` by
    (qspec_then `b with vs_inst_idx := s.vs_inst_idx+3` mp_tac
       raw_call_revert_copy >>
     disch_then (qspecl_then [`Var p`,`Var z`,`pw`,`s.vs_returndata`,
       `sa.cs_next_id+2`,`sa.cs_next_id+3`] mp_tac) >>
     fs[eval_operand_def,lookup_var_def] >>
     simp[Abbr `rev`,Abbr `c2`,Abbr `b2`,GSYM arithmeticTheory.ADD_ASSOC,
          arithmeticTheory.ADD1,revert_state_def,set_returndata_def] >>
     metis_tac[]) >>
  qunabbrev_tac `copy` >> qunabbrev_tac `rev` >>
  irule raw_call_forward_pair_origin_ptr >>
  gvs[Abbr `b2`,allocas_from_def,arithmeticTheory.ADD1,
       GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[]
QED

Finalise raw_call_failure_block_origin_ptr

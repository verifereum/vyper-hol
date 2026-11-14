Theory bodyFullRawCallForward
Ancestors
  rawCallBufferPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  ptrSafetyTransport ptrSafeRun ptrDiscipline contextCodegenRel
  gasEvents gasCount fragExec venomMemProps venomInstProps
  venomExecProps venomExecSemantics venomInst venomState list arithmetic
  bodyFullAllocaFresh rawCallDataHeaderPtr exprLoweringProps emitHelperProps
  compileEnv context builtinSystem allocaHistory fragGasSeqPtr instMemFrontier
  codegenRel memSafeRun finite_map loweringShapeRules loweringStateRelDefs
  emitHelper unitTransformDefs
Libs monadsyntax pairLib

Theorem raw_call_forward_pair_origin_ptr:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  copy.inst_operands = [dst; Lit 0w; len] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [dst; len] /\
  op_taint tn dst = {} /\ op_taint tn len = {} /\
  step_inst_base copy s = OK u /\
  step_inst_base rev (u with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort Revert_abort z ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort z,
      step_prov PG G copy u, step_taint copy s u tn)
Proof
  strip_tac >>
  `step_inst 0 ctx copy s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator copy.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_halted >>
     drule_all step_preserves_control_flow >> simp[]) >>
  `u.vs_allocas = s.vs_allocas` by
    (irule step_inst_non_alloca_preserves_allocas >>
     goal_assum (drule_at Any) >> simp[is_alloca_op_def]) >>
  `in_revert_forward func s` by
    (irule forwarding_pair_active >> metis_tac[]) >>
  `about_to_revert func copy s` by
    (simp[about_to_revert_def, active_inst_def] >>
     qexists_tac `rev` >> simp[] >> qexists_tac `bb` >>
     drule lookup_block_MEM >> drule lookup_block_label >>
     fs[get_instruction_def, AllCaseEqs()]) >>
  `ptr_inst_ok D lo 0 ctx func G tn copy s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[] >> irule ptr_inst_ok_forward_copy >> fs[op_taint_def]) >>
  `revert_forward_pair bb s.vs_inst_idx (SUC s.vs_inst_idx)` by
    (irule revert_forward_pair_consecutive >> metis_tac[]) >>
  `revert_forward_at bb s.vs_inst_idx /\
   revert_forward_at bb (SUC s.vs_inst_idx)` by
    (simp[revert_forward_at_def] >> metis_tac[]) >>
  qabbrev_tac `s_rev = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `allocas_from lo s_rev /\ ~s_rev.vs_halted /\
   s_rev.vs_current_bb = s.vs_current_bb /\
   s_rev.vs_inst_idx = SUC s.vs_inst_idx` by
    (simp[Abbr `s_rev`, allocas_from_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `in_revert_forward func s_rev` by
    (irule forwarding_pair_active >> simp[] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx func (step_prov PG G copy u)
     (step_taint copy s u tn) rev s_rev` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >> qexists_tac `0` >>
     simp[] >> irule ptr_inst_ok_forward_revert >>
     simp[forwarding_copy_operand_taint]) >>
  suspend "edges"
QED

Resume raw_call_forward_pair_origin_ptr[edges]:
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK s_rev,step_prov PG G copy u,step_taint copy s u tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
     >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
         qexistsl_tac [`0`, `bb`, `copy`, `OK u`] >>
         simp[step_inst_non_invoke, gas_events_step_def, Abbr `s_rev`]) >>
     rewrite_tac[gas_path_ptr_edge_def] >> conj_tac >- simp[] >>
     qexistsl_tac [`0`, `bb`, `copy`, `OK u`] >>
     simp[step_inst_non_invoke, gas_events_step_def, gas_count_step_def,
       ptr_safe_step_def, ghost_step_non_invoke, Abbr `s_rev`]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (s_rev,step_prov PG G copy u,step_taint copy s u tn) []
    (Abort Revert_abort z,step_prov PG G copy u,step_taint copy s u tn)` by
    (rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
     >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
         qexistsl_tac [`0`, `bb`, `rev`, `Abort Revert_abort z`] >>
         simp[step_inst_non_invoke, gas_events_step_def, exit_result_def]) >>
     rewrite_tac[gas_path_ptr_edge_def] >> conj_tac >- simp[] >>
     qexistsl_tac [`0`, `bb`, `rev`, `Abort Revert_abort z`] >>
     simp[step_inst_non_invoke, gas_events_step_def, gas_count_step_def,
       ptr_safe_step_def, exit_result_def, Abbr `s_rev`]) >>
  metis_tac[gas_origin_ptr_path_rules, exit_result_def, APPEND]
QED

Finalise raw_call_forward_pair_origin_ptr

Theorem raw_call_failure_tail_origin_ptr:
  (do rds <- emit_op RETURNDATASIZE [];
      buf <- compile_alloc_buffer 0;
      emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds];
      emit_inst REVERT [buf.buf_operand;rds] [] od) sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?z J un. z.vs_returndata = s.vs_returndata /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort z,J,un)
Proof
  strip_tac >>
  `?rds s1 buf s2 s3.
    emit_op RETURNDATASIZE [] sa = (rds,s1) /\
    compile_alloc_buffer 0 s1 = (buf,s2) /\
    emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] s2 = ((),s3) /\
    emit_inst REVERT [buf.buf_operand;rds] [] s3 = ((),sb)` by
    (qpat_x_assum `(do _ <- _; _ od) _ = _` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sb` by
    metis_tac[ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, ci_mono_emit_inst, pairTheory.SND] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  qpat_assum `emit_op RETURNDATASIZE [] sa = (rds,s1)`
    (mp_then (Pat `emit_op _ _ _ = _`) mp_tac emit_op_facts) >>
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id RETURNDATASIZE [] [out])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `rds_inst = mk_inst sa.cs_next_id RETURNDATASIZE [] [out]` >>
  qabbrev_tac `u = update_var out (n2w (LENGTH s.vs_returndata)) s` >>
  qabbrev_tac `t_rds = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G_rds = step_prov PG G rds_inst u` >>
  qabbrev_tac `tn_rds = step_taint rds_inst s u tn` >>
  `step_inst_base rds_inst s = OK u` by
    simp[Abbr `rds_inst`,Abbr `u`,raw_call_returndatasize_step_base] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn rds_inst s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `rds_inst`,ptr_inst_ok_returndatasize]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t_rds,G_rds,tn_rds)` by
    (gen_tac >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t_rds,G_rds,tn_rds)` by
       (mp_tac (Q.INST [`i` |-> `rds_inst`,`s` |-> `s`,`u` |-> `u`,
          `bb` |-> `bb`,`D` |-> `D`,`lo` |-> `lo`,`ctx` |-> `ctx`,
          `func` |-> `func`,`PG` |-> `PG`,`G` |-> `G`,`tn` |-> `tn`,
          `explicit` |-> `explicit`] straight_line_origin_ptr_edge) >>
        impl_tac
        >- simp[Abbr `rds_inst`,mk_inst_def,is_terminator_def,
          inst_mem_below_frontier_def,inst_dload_in_section_def,
          source_memory_write_ranges_def,source_memory_read_ranges_def] >>
        simp[Abbr `rds_inst`,Abbr `t_rds`,Abbr `G_rds`,Abbr `tn_rds`,
          mk_inst_def,is_terminator_def,inst_mem_below_frontier_def,
          inst_dload_in_section_def,source_memory_write_ranges_def,
          source_memory_read_ranges_def]) >>
     qpat_assum `gas_origin_ptr_edge _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
          (cj 2 gas_origin_ptr_path_rules))) >>
     simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >>
     simp[Abbr `t_rds`,Abbr `u`,update_var_def]) >>
  `stmt_state_rel H ctx func cenv cx es t_rds` by
    (mp_tac (Q.INST [`out` |-> `out`,
       `w` |-> `n2w (LENGTH s.vs_returndata)`,
       `k` |-> `SUC s.vs_inst_idx`] raw_call_fresh_update_state_frame) >>
     impl_tac >- simp[] >> simp[Abbr `t_rds`,Abbr `u`]) >>
  `alloca_inv s` by fs[stmt_state_rel_def,state_rel_def] >>
  `alloca_history func t_rds` by
    (qspecl_then [`func`,`s`,`bb`,`rds_inst`,`u`] mp_tac alloca_history_base_step >>
     impl_tac >- simp[] >>
     simp[Abbr `rds_inst`,Abbr `t_rds`,is_terminator_def,mk_inst_def]) >>
  `allocas_from lo t_rds` by
    (simp[Abbr `t_rds`,Abbr `u`,allocas_from_def,update_var_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `lo <= t_rds.vs_alloca_next /\
   ~t_rds.vs_halted /\ t_rds.vs_current_bb = s1.cs_current_bb /\
   t_rds.vs_inst_idx = LENGTH s1.cs_current_insts` by
    simp[Abbr `t_rds`,Abbr `u`,update_var_def] >>
  `local_ptrs_reserved cenv s1` by
    (qpat_assum `ci_mono sa s1`
       (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  suspend "allocate"
QED

Resume raw_call_failure_tail_origin_ptr[allocate]:
  mp_tac (Q.INST [`n` |-> `0`,`sa` |-> `s1`,`sb` |-> `s2`,`buf` |-> `buf`,
    `s` |-> `t_rds`,`G` |-> `G_rds`,`tn` |-> `tn_rds`,
    `explicit` |-> `explicit`,`PG` |-> `PG`,`lo` |-> `lo`,
    `func` |-> `func`,`ctx` |-> `ctx`,`cenv` |-> `cenv`,`cx` |-> `cx`,
    `es` |-> `es`,`H` |-> `H`]
    alloc_buffer_origin_ptr_path) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`q_alloc`,`w_alloc`,`t_alloc`,`G_alloc`,`tn_alloc`]
    strip_assume_tac) >>
  `t_alloc.vs_returndata = s.vs_returndata` by
    (qpat_assum `t_alloc with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = t_rds`
       (mp_tac o Q.AP_TERM `\st. st.vs_returndata`) >>
     simp[Abbr `t_rds`,Abbr `u`,update_var_def]) >>
  `eval_operand buf.buf_operand t_alloc = SOME w_alloc /\
   eval_operand rds t_alloc = SOME (n2w (LENGTH s.vs_returndata)) /\
   op_taint tn_alloc buf.buf_operand = {} /\ op_taint tn_alloc rds = {}` by
    (qpat_assum `ptr_covers G_alloc tn_alloc q_alloc t_alloc 0`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
     simp[eval_operand_def] >>
     qpat_assum `!x. not_fresh_at s1 x ==> _`
       (qspec_then `out` mp_tac) >>
     simp[Abbr `t_rds`,Abbr `u`,Abbr `tn_rds`,Abbr `rds_inst`,
       raw_call_returndatasize_step_taint,op_taint_def,lookup_var_def,
       update_var_def,FLOOKUP_UPDATE]) >>
  suspend "forward"
QED

Resume raw_call_failure_tail_origin_ptr[forward]:
  `s3.cs_current_bb = s2.cs_current_bb /\
   sb.cs_current_bb = s2.cs_current_bb /\
   sb.cs_current_insts = s2.cs_current_insts ++
     [mk_inst s2.cs_next_id RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] [];
      mk_inst s3.cs_next_id REVERT [buf.buf_operand;rds] []]` by
    (qpat_x_assum `emit_void _ _ s2 = _` mp_tac >>
     qpat_x_assum `emit_inst REVERT _ _ s3 = _` mp_tac >>
     simp[emit_void_def,emit_inst_def,comp_bind_def,comp_ignore_bind_def,
       fresh_id_def,emit_def,comp_return_def] >> rpt strip_tac >> gvs[]) >>
  qabbrev_tac `copy_inst = mk_inst s2.cs_next_id RETURNDATACOPY
    [buf.buf_operand;Lit 0w;rds] []` >>
  qabbrev_tac `rev_inst = mk_inst s3.cs_next_id REVERT [buf.buf_operand;rds] []` >>
  `?bb_pair. lookup_block s2.cs_current_bb func.fn_blocks = SOME bb_pair /\
    !i. i < LENGTH [copy_inst;rev_inst] ==>
      get_instruction bb_pair (LENGTH s2.cs_current_insts+i) =
        SOME (EL i [copy_inst;rev_inst])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  `get_instruction bb_pair t_alloc.vs_inst_idx = SOME copy_inst /\
   get_instruction bb_pair (SUC t_alloc.vs_inst_idx) = SOME rev_inst` by
    (qpat_assum `!i. i < LENGTH [copy_inst;rev_inst] ==> _`
       (fn th => map_every (fn n => qspec_then n assume_tac th) [`0`,`1`]) >>
     fs[arithmeticTheory.ADD1]) >>
  qabbrev_tac `u_copy = write_memory_with_expansion
    (w2n w_alloc) t_alloc.vs_returndata t_alloc` >>
  qabbrev_tac `s_rev = u_copy with vs_inst_idx := SUC t_alloc.vs_inst_idx` >>
  qabbrev_tac `z_revert = revert_state
    (set_returndata t_alloc.vs_returndata s_rev)` >>
  `lookup_var out t_alloc = SOME (n2w (LENGTH s.vs_returndata))` by
    (qpat_assum `rds = Var out` (fn eq =>
       qpat_assum `eval_operand rds t_alloc = _`
         (ACCEPT_TAC o REWRITE_RULE [eq,eval_operand_def]))) >>
  `step_inst_base copy_inst t_alloc = OK u_copy` by
    simp[Abbr `copy_inst`,Abbr `u_copy`,step_inst_base_opcode_eqs,mk_inst_def,
      eval_operand_def,wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
  `eval_operand buf.buf_operand s_rev = SOME w_alloc /\
   eval_operand rds s_rev = SOME (n2w (LENGTH t_alloc.vs_returndata))` by
    (Cases_on `buf.buf_operand` >> Cases_on `rds` >>
     gvs[Abbr `s_rev`,Abbr `u_copy`,eval_operand_def,lookup_var_def,
       write_memory_with_expansion_def,write_memory_def]) >>
  `mem_bytes_at (w2n w_alloc) (LENGTH t_alloc.vs_returndata)
      u_copy.vs_memory = t_alloc.vs_returndata` by
    simp[Abbr `u_copy`,exprSimHashTheory.hash_write_memory_read_self] >>
  `read_memory (w2n w_alloc) (LENGTH t_alloc.vs_returndata) s_rev =
      t_alloc.vs_returndata` by
    (simp_tac (srw_ss()) [read_memory_def,Abbr `s_rev`] >>
     qpat_assum `mem_bytes_at _ _ u_copy.vs_memory = _`
       (ACCEPT_TAC o REWRITE_RULE [valueEncodingDefsTheory.mem_bytes_at_def])) >>
  `step_inst_base rev_inst s_rev = Abort Revert_abort z_revert` by
    (qpat_assum `read_memory _ _ _ = _` mp_tac >>
     qpat_assum `eval_operand rds s_rev = _` mp_tac >>
     qpat_assum `eval_operand buf.buf_operand s_rev = _` mp_tac >>
     qpat_assum `t_alloc.vs_returndata = s.vs_returndata` mp_tac >>
     qpat_assum `LENGTH s.vs_returndata < dimword (:256)` mp_tac >>
     qpat_assum `Abbrev (rev_inst = _)` mp_tac >>
     qpat_assum `Abbrev (z_revert = _)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     simp[Abbr `rev_inst`,Abbr `z_revert`,step_inst_base_opcode_eqs,
       mk_inst_def,wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD,
       GSYM read_memory_def] >>
     qpat_assum `t_alloc.vs_returndata = s.vs_returndata` (fn rd_eq =>
       qpat_assum `read_memory _ _ _ = _`
         (fn copied => REWRITE_TAC [REWRITE_RULE [rd_eq] copied]))) >>
  qabbrev_tac `G_out = step_prov PG G_alloc copy_inst u_copy` >>
  qabbrev_tac `tn_out = step_taint copy_inst t_alloc u_copy tn_alloc` >>
  `~t_alloc.vs_halted` by
    (qpat_assum `t_alloc with <|vs_vars := _;vs_allocas := _;
       vs_alloca_next := _;vs_inst_idx := _|> = t_rds`
       (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >>
     simp[Abbr `t_rds`,Abbr `u`,update_var_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t_alloc,G_alloc,tn_alloc) [] (Abort Revert_abort z_revert,G_out,tn_out)` by
    (gen_tac >>
     mp_tac (Q.INST [`s` |-> `t_alloc`,`G` |-> `G_alloc`,`tn` |-> `tn_alloc`,
       `copy` |-> `copy_inst`,`rev` |-> `rev_inst`,`bb` |-> `bb_pair`,
       `dst` |-> `buf.buf_operand`,`len` |-> `rds`,`u` |-> `u_copy`,
       `z` |-> `z_revert`,`D` |-> `D`,`lo` |-> `lo`,`explicit` |-> `explicit`,
       `ctx` |-> `ctx`,`func` |-> `func`,`PG` |-> `PG`]
       raw_call_forward_pair_origin_ptr) >>
     impl_tac
     >- (qpat_x_assum `step_inst_base copy_inst t_alloc = OK u_copy` mp_tac >>
         qpat_x_assum `step_inst_base rev_inst s_rev = Abort Revert_abort z_revert` mp_tac >>
         simp[Abbr `copy_inst`,Abbr `rev_inst`,Abbr `s_rev`,mk_inst_def]) >>
     simp[Abbr `G_out`,Abbr `tn_out`]) >>
  suspend "append"
QED

Resume raw_call_failure_tail_origin_ptr[append]:
  qexistsl_tac [`z_revert`,`G_out`,`tn_out`] >>
  conj_tac
  >- simp[Abbr `z_revert`,revert_state_def,set_returndata_def] >>
  gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t_rds,G_rds,tn_rds) [] (Abort Revert_abort z_revert,G_out,tn_out)` by
    (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (t_rds,G_rds,tn_rds) [] (OK t_alloc,G_alloc,tn_alloc)`
       (qspec_then `D` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`t_alloc`,`G_alloc`,`tn_alloc`,`[]`,
       `Abort Revert_abort z_revert`,`G_out`,`tn_out`] mp_tac) >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t_rds,G_rds,tn_rds)`
    (qspec_then `D` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`t_rds`,`G_rds`,`tn_rds`,`[]`,
    `Abort Revert_abort z_revert`,`G_out`,`tn_out`] mp_tac) >> simp[]
QED

Finalise raw_call_failure_tail_origin_ptr

(* Checked failure forwarding after an unsuccessful external call. *)
Theory bodyFullExtCallFailurePath
Ancestors
  ctorDeployMemoryRunPtrPrefixSteps instIdxIndep ghostPcTransportPtr
  exprSimHash valueEncodingDefs rawCallBufferPtr fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  fragGasEmitCtrl exprSimAccounts exprLoweringProps emitHelperProps emitHelper
  exprLowering compileEnv fragExec ptrSafeRun ptrDiscipline memSafeRun
  instMemFrontier unitTransformDefs codegenRel contextCodegenRel contextCodegenRelProps
  venomExecProps venomInstProps venomExecSemantics venomInst venomState
  gasEvents gasCount finite_map pred_set list context

Theorem extcall_forward_copy_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  in_revert_forward func s /\ about_to_revert func copy s /\
  EVERY (\op. op_taint tn op = {}) copy.inst_operands /\
  step_inst_base copy s = OK u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G copy u, step_taint copy s u tn)
Proof
  strip_tac >> gen_tac >>
  `access_ok lo G func copy s /\ taint_ok func tn copy s` by
    (irule revert_forward_access_taint >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn copy s` by
    (qpat_x_assum `step_inst_base copy s = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, write_memory_with_expansion_def,
       write_memory_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
     simp[ptr_inst_ok_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, write_memory_with_expansion_def,
       write_memory_def, AllCaseEqs()]) >>
  `copy.inst_opcode <> INVOKE /\ ~is_terminator copy.inst_opcode` by
    simp[is_terminator_def] >>
  `step_inst 0 ctx copy s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> simp[] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def] >>
      gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  drule_all straight_line_ptr_edge >> simp[]
QED

Theorem extcall_forward_revert_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME rev /\
  rev.inst_opcode = REVERT /\ in_revert_forward func s /\
  EVERY (\op. op_taint tn op = {}) rev.inst_operands /\
  step_inst_base rev s = Abort Revert_abort u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort u,G,tn)
Proof
  strip_tac >> gen_tac >>
  `access_ok lo G func rev s /\ taint_ok func tn rev s` by
    (irule revert_forward_access_taint >> simp[about_to_revert_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn rev s` by
    simp[ptr_inst_ok_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
         AllCaseEqs()] >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> simp[] >>
      qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_events_step_def,
           mem_safe_step_non_invoke, exit_result_def] >>
      gvs[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, ptr_safe_step_def,
       exit_result_def]
QED

Theorem extcall_forward_pair_path:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME copy /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME rev /\
  copy.inst_opcode = RETURNDATACOPY /\ copy.inst_outputs = [] /\
  copy.inst_operands = [p; Lit 0w; rds] /\
  rev.inst_opcode = REVERT /\ rev.inst_operands = [p; rds] /\
  op_taint tn p = {} /\ op_taint tn rds = {} /\
  step_inst_base copy s = OK u /\
  step_inst_base rev (u with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort Revert_abort t ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)
Proof
  strip_tac >> gen_tac >>
  `step_inst 0 ctx copy s = OK u` by simp[step_inst_non_invoke] >>
  `~is_terminator copy.inst_opcode` by simp[is_terminator_def] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `allocas_from lo u` by
    (irule frameActivationSeparationTheory.allocas_from_step >>
     goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[]) >>
  `in_revert_forward func s` by
    (irule forwarding_pair_active >> metis_tac[]) >>
  `about_to_revert func copy s` by
    (simp[about_to_revert_def, active_inst_def] >>
     qexists_tac `rev` >> simp[] >> qexists_tac `bb` >>
     drule lookup_block_MEM >> drule lookup_block_label >>
     fs[get_instruction_def, AllCaseEqs()]) >>
  `in_revert_forward func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule forwarding_pair_active >> simp[] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G copy u,step_taint copy s u tn)` by
    (irule extcall_forward_copy_edge >> simp[] >>
     simp[op_taint_def] >> gvs[op_taint_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (u with vs_inst_idx := SUC s.vs_inst_idx,
     step_prov PG G copy u,step_taint copy s u tn) []
    (Abort Revert_abort t,step_prov PG G copy u,step_taint copy s u tn)` by
    (irule extcall_forward_revert_edge >>
     simp[forwarding_copy_operand_taint] >> fs[allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ (Abort _ _,_,_)`
    (mp_then Any mp_tac (cj 3 gas_origin_ptr_path_rules)) >>
  simp[exit_result_def] >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >> simp[]
QED

Theorem extcall_failure_layout:
  emit_inst JNZ [cond;Label ok;Label fl] [] sa = (a,sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = (b,sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = (c,se) /\
  new_block ok se = (y,sk) /\ fn_has_code sa sk func ==>
  ?v p entry fail.
    z = Var v /\ rb.buf_operand = Var p /\ v <> p /\
    sf.cs_current_bb = fl /\ sf.cs_current_insts = [] /\
    sz.cs_next_id = sa.cs_next_id + 2 /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME entry /\
    get_instruction entry (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id JNZ [cond;Label ok;Label fl] []) /\
    lookup_block fl func.fn_blocks = SOME fail /\
    get_instruction fail 0 =
      SOME (mk_inst (sa.cs_next_id + 1) RETURNDATASIZE [] [v]) /\
    get_instruction fail 1 =
      SOME (mk_inst (sa.cs_next_id + 2) ALLOCA [Lit 0w] [p]) /\
    get_instruction fail 2 =
      SOME (mk_inst (sa.cs_next_id + 3) RETURNDATACOPY
        [Var p;Lit 0w;Var v] []) /\
    get_instruction fail 3 =
      SOME (mk_inst (sa.cs_next_id + 4) REVERT [Var p;Var v] [])
Proof
  simp[emit_inst_def, emit_op_def, emit_void_def, compile_alloc_buffer_def,
    new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[get_instruction_def, EL_APPEND_EQN]
QED

Theorem extcall_failure_prefix_edge[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst = mk_inst id RETURNDATASIZE [] [out] \/
   inst = mk_inst id ALLOCA [Lit 0w] [out]) /\
  step_inst_base inst s = OK u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G inst u,step_taint inst s u tn)
Proof
  strip_tac >> gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (Cases_on `inst.inst_opcode = ALLOCA`
     >- (gvs[mk_inst_def] >> simp[GSYM mk_inst_def, prefix_alloca_inst_ok]) >>
     gvs[mk_inst_def] >>
     gvs[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read0_def, bind_outputs_def, update_var_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
   inst.inst_opcode <> GAS` by
    (gvs[] >> simp[mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  drule_all straight_line_origin_ptr_edge >> simp[]
QED

Theorem extcall_zero_alloca_result[local]:
  !s id p. ?u b.
    step_inst_base (mk_inst id ALLOCA [Lit 0w] [p]) s = OK u /\
    eval_operand (Var p) u = SOME (n2w b) /\
    u.vs_returndata = s.vs_returndata /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted /\
    u.vs_inst_idx = s.vs_inst_idx /\
    (!z. z <> p ==> eval_operand (Var z) u = eval_operand (Var z) s) /\
    (!lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
          allocas_from lo u /\ lo <= u.vs_alloca_next)
Proof
  rpt gen_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (qexistsl_tac
       [`update_var p (n2w s.vs_alloca_next)
          (s with vs_allocas := s.vs_allocas |+ (id,(s.vs_alloca_next,0)))`,
        `s.vs_alloca_next`] >>
      simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
        eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
        allocas_from_def] >> rpt strip_tac >>
      Cases_on `id = aid` >> gvs[] >> metis_tac[]) >>
  PairCases_on `x` >>
  qexistsl_tac [`update_var p (n2w x0) s`, `x0`] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    allocas_from_def] >> metis_tac[]
QED

Theorem extcall_failure_prefix_compose[local]:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME r /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME i /\
  r = mk_inst rid RETURNDATASIZE [] [z] /\
  i = mk_inst aid ALLOCA [Lit 0w] [p] /\
  step_inst_base r s = OK a /\ step_inst_base i a = OK u ==>
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx + 2),
     step_prov PG (step_prov PG G r a) i u,
     step_taint i a u (step_taint r s a tn))
Proof
  strip_tac >> gen_tac >>
  `~a.vs_halted /\ a.vs_current_bb = s.vs_current_bb /\ allocas_from lo a` by
    (gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read0_def,
      bind_outputs_def, update_var_def, allocas_from_def] >> metis_tac[]) >>
  `step_inst_base i (a with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[step_inst_inst_idx_indep, is_terminator_def, mk_inst_def,
      exec_result_map_def] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (a with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G r a,step_taint r s a tn)` by
    (irule extcall_failure_prefix_edge >> simp[] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (a with vs_inst_idx := SUC s.vs_inst_idx,
      step_prov PG G r a,step_taint r s a tn) []
    (OK (u with vs_inst_idx := s.vs_inst_idx + 2),
      step_prov PG (step_prov PG G r a) i u,
      step_taint i a u (step_taint r s a tn))` by
    (drule_at (Pat `step_inst_base _ _ = _`)
       extcall_failure_prefix_edge >>
     simp[allocas_from_def, arithmeticTheory.ADD1] >> disch_then irule >>
     fs[allocas_from_def, GSYM arithmeticTheory.ADD1] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_edge _ (s,G,tn) _ _`
    (mp_then Any mp_tac (cj 2 gas_origin_ptr_path_rules)) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def,
      update_var_def, AllCaseEqs()]
QED

Theorem extcall_failure_prefix_path:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ z <> p /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst rid RETURNDATASIZE [] [z]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst aid ALLOCA [Lit 0w] [p]) ==>
  ?t G' tn' b.
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 2 /\
    t.vs_returndata = s.vs_returndata /\
    eval_operand (Var z) t = SOME (n2w (LENGTH s.vs_returndata)) /\
    eval_operand (Var p) t = SOME (n2w b) /\
    op_taint tn' (Var z) = {} /\ op_taint tn' (Var p) = {} /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  qabbrev_tac `r = mk_inst rid RETURNDATASIZE [] [z]` >>
  qabbrev_tac `i = mk_inst aid ALLOCA [Lit 0w] [p]` >>
  qabbrev_tac `a = update_var z (n2w (LENGTH s.vs_returndata)) s` >>
  `step_inst_base r s = OK a` by
    simp[Abbr `r`, Abbr `a`, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read0_def, bind_outputs_def] >>
  `?u b. step_inst_base i a = OK u /\
    eval_operand (Var p) u = SOME (n2w b) /\
    u.vs_returndata = a.vs_returndata /\
    u.vs_current_bb = a.vs_current_bb /\ u.vs_halted = a.vs_halted /\
    u.vs_inst_idx = a.vs_inst_idx /\
    eval_operand (Var z) u = eval_operand (Var z) a /\
    allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qspecl_then [`a`,`aid`,`p`]
       (qx_choose_then `u` (qx_choose_then `b` strip_assume_tac))
       extcall_zero_alloca_result >>
     qexistsl_tac [`u`,`b`] >>
     fs[Abbr `i`, Abbr `a`, update_var_def, allocas_from_def] >>
     metis_tac[]) >>
  qexistsl_tac [`u with vs_inst_idx := s.vs_inst_idx + 2`,
    `step_prov PG (step_prov PG G r a) i u`,
    `step_taint i a u (step_taint r s a tn)`, `b`] >>
  fs[Abbr `a`, update_var_def, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE, allocas_from_def] >>
  conj_tac
  >- simp[Abbr `i`, Abbr `r`, op_taint_def, step_taint_def,
       set_var_taint_def, out_taint_def, mk_inst_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `i`, prefix_alloca_output_taint] >>
  conj_tac >- metis_tac[] >>
  irule extcall_failure_prefix_compose >>
  simp[Abbr `r`, Abbr `i`, allocas_from_def] >> metis_tac[]
QED

Theorem extcall_failure_forward_exact[local]:
  !s ctx lo func bb cid p rds rid tn pw G explicit PG.
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst cid RETURNDATACOPY [p;Lit 0w;rds] []) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst rid REVERT [p;rds] []) /\
  op_taint tn p = {} /\ op_taint tn rds = {} /\
  eval_operand p s = SOME pw /\
  eval_operand rds s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t G' tn'. t.vs_returndata = s.vs_returndata /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort t,G',tn')
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst cid RETURNDATACOPY [p;Lit 0w;rds] []) s =
      OK (write_memory_with_expansion (w2n pw) s.vs_returndata s) /\
   step_inst_base (mk_inst rid REVERT [p;rds] [])
      (write_memory_with_expansion (w2n pw) s.vs_returndata s) =
      Abort Revert_abort
        (revert_state (set_returndata s.vs_returndata
          (write_memory_with_expansion (w2n pw) s.vs_returndata s)))` by
    (conj_tac
     >- simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
          wordsTheory.w2n_n2w] >>
     `eval_operand p (write_memory_with_expansion (w2n pw) s.vs_returndata s) =
        SOME pw /\
      eval_operand rds (write_memory_with_expansion (w2n pw) s.vs_returndata s) =
        SOME (n2w (LENGTH s.vs_returndata))` by
       (Cases_on `p` >> Cases_on `rds` >>
        gvs[write_memory_with_expansion_def, eval_operand_def, lookup_var_def]) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, wordsTheory.w2n_n2w,
       GSYM mem_bytes_at_def, hash_write_memory_read_self]) >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK u` >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ u = Abort Revert_abort t` >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G (mk_inst cid RETURNDATACOPY [p;Lit 0w;rds] []) u`,
    `step_taint (mk_inst cid RETURNDATACOPY [p;Lit 0w;rds] []) s u tn`] >>
  conj_tac
  >- simp[Abbr `t`, revert_state_def, set_returndata_def] >>
  irule extcall_forward_pair_path >> simp[mk_inst_def] >>
  qpat_x_assum `step_inst_base _ u = Abort _ t` mp_tac >>
  Cases_on `p` >> Cases_on `rds` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
    lookup_var_def, revert_state_def, set_returndata_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem extcall_failure_suffix_path:
  emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
  new_block fl sx = (x,sf) /\
  emit_op RETURNDATASIZE [] sf = (z,sz) /\
  compile_alloc_buffer 0 sz = (rb,sp) /\
  emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = (b,sc) /\
  emit_inst REVERT [rb.buf_operand;z] [] sc = (c,se) /\
  new_block ok se = (y,sk) /\ fn_has_code sa sk func /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand cond s = SOME 0w /\ op_taint tn cond = {} /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u G' tn'. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort u,G',tn')) /\
    u.vs_returndata = s.vs_returndata
Proof
  strip_tac >>
  drule_all extcall_failure_layout >> strip_tac >>
  `fn_has_code sa sx func` by
    (fs[emit_inst_def, emit_op_def, emit_void_def, compile_alloc_buffer_def,
      new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >> gvs[] >>
     fs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
     metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to fl s),G,tn)` by
    (gen_tac >> irule (SRULE [] (INST [``b:bool`` |-> ``F``] emit_jnz_origin_ptr)) >>
     simp[] >> metis_tac[]) >>
  `?t G1 tn1 b0.
    ~t.vs_halted /\ t.vs_current_bb = fl /\ t.vs_inst_idx = 2 /\
    t.vs_returndata = s.vs_returndata /\
    eval_operand (Var v) t = SOME (n2w (LENGTH s.vs_returndata)) /\
    eval_operand (Var p) t = SOME (n2w b0) /\
    op_taint tn1 (Var v) = {} /\ op_taint tn1 (Var p) = {} /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (jump_to fl s,G,tn) [] (OK t,G1,tn1)` by
    (pure_rewrite_tac[jump_to_def] >>
     irule (SRULE [jump_to_def]
       (Q.INST [`s` |-> `jump_to fl s`] extcall_failure_prefix_path)) >>
     simp[allocas_from_def] >> fs[allocas_from_def] >> metis_tac[]) >>
  `?u G2 tn2. u.vs_returndata = t.vs_returndata /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G1,tn1) [] (Abort Revert_abort u,G2,tn2)` by
    (irule extcall_failure_forward_exact >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`u`,`G2`,`tn2`] >> simp[] >> gen_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `D` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  simp[] >> disch_then irule >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (jump_to fl s,G,tn) _ _`
    (qspec_then `D` (mp_then Any mp_tac gas_origin_ptr_path_append)) >>
  simp[] >> disch_then irule >> simp[]
QED

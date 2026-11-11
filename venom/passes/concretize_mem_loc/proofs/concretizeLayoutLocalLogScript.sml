Theory concretizeLayoutLocalLog
Ancestors concretizeLayoutLocalSha3 frameRelocationCleanOperands
  frameRelocationLocal frameRelocationGuardedValues concretizeLayoutAccessGeometry
  frameRelocationReachableSupport frameRelocationBinding frameJointDemand
  frameJointTrace frameJointTransition frameOriginReachable frameOriginHistory
  frameResolvedTrace frameActivationLookup frameActivationLifetime
  frameRelocationDemand frameRelocationMemory venomState concretizeLayoutLocalTerminals
  frameRelocationEnvironment concretizeLayoutReaderContext frameRelocationTaintOrder
  frameRelocationCopyTaint
  frameOriginUpdates frameRelocationValues frameRelocationOpaque
  ptrDiscipline unitMemInv o1PassContract contextCodegenRel
  pointerConfinedDefs venomExecSemantics memLocDefs finite_map list pred_set words

Theorem log_execution_envelope[local]:
  inst.inst_opcode = LOG /\ step_inst_base inst s = OK post ==>
  ?tc rest off sz topics.
    inst.inst_operands = Lit tc :: rest /\
    LENGTH rest = w2n tc + 2 /\
    eval_operand (EL 0 (REVERSE rest)) s = SOME off /\
    eval_operand (EL 1 (REVERSE rest)) s = SOME sz /\
    eval_operands (DROP 2 (REVERSE rest)) s = SOME topics /\
    ~(s.vs_call_ctx.cc_static /\ IS_SOME (eval_operands inst.inst_operands s)) /\
    post = s with vs_logs := s.vs_logs ++
      [<| logger := w2w s.vs_call_ctx.cc_address; topics := topics;
          data := TAKE (w2n sz)
            (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) |>]
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem log_read_descriptor[local]:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (opd::opn::tops) ==>
  mem_read_ops inst =
    SOME <| iao_ofst := opd; iao_size := SOME opn;
            iao_max_size := SOME opn |> /\
  mem_write_ops inst = NONE
Proof
  strip_tac >> Cases_on `tops` >>
  simp[mem_read_ops_def, mem_write_ops_def, REVERSE_APPEND]
QED

Theorem log_reversed_tail[local]:
  LENGTH rest = w2n tc + 2 ==>
  ?opd opn tops. rest = REVERSE (opd::opn::tops) /\ LENGTH tops = w2n tc
Proof
  strip_tac >>
  Cases_on `REVERSE rest` >> gvs[] >>
  rename1 `REVERSE rest = opd::tail` >>
  Cases_on `tail` >> gvs[] >>
  qexistsl_tac [`opd`, `h`, `t`] >> conj_tac
  >- (qpat_x_assum `REVERSE rest = _` (mp_tac o AP_TERM ``REVERSE``) >>
      pure_rewrite_tac[REVERSE_REVERSE, REVERSE_DEF, APPEND] >>
      strip_tac >> simp[APPEND_ASSOC]) >>
  qpat_x_assum `REVERSE rest = _` (mp_tac o AP_TERM ``LENGTH``) >> simp[]
QED

Theorem log_scalar_agreement[local]:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (opd::opn::tops) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op (opn::tops) ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> rpt strip_tac >>
  `!v. op = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `v IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     drule_all log_read_descriptor >> strip_tac >>
     fs[ptr_use_ok_def, is_pointer_preserving_op_def] >>
     qpat_x_assum `!u. MEM (Var u) _ /\ _ ==> _`
       (qspec_then `v` mp_tac) >>
     simp[MEM_REVERSE, is_pointer_preserving_op_def] >>
     strip_tac >> gvs[] >>
     strip_tac >> gvs[FILTER_REVERSE, FILTER_APPEND_DISTRIB] >>
     `MEM (Var v) (FILTER ($= (Var v)) tops)` by simp[MEM_FILTER] >>
     Cases_on `FILTER ($= (Var v)) tops` >> gvs[] >>
     Cases_on `Var v = opn` >> gvs[] >>
     qpat_x_assum `_ = [Var v]` (mp_tac o AP_TERM ``LENGTH``) >> simp[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `inst` >> simp[MEM_REVERSE] >> fs[] >> metis_tac[]
QED

Theorem log_read_clean[local]:
  taint_ok fn tn inst s /\ inst.inst_opcode = LOG /\
  inst.inst_operands = Lit tc :: REVERSE (opd::opn::tops) /\
  LENGTH tops = w2n tc /\ eval_operands tops s = SOME topics /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz ==>
  !i. i < w2n sz ==> w2n off+i NOTIN tn.t_mem
Proof
  strip_tac >> drule_all log_read_descriptor >> strip_tac >>
  fs[taint_ok_def, about_to_revert_def,
     source_memory_read_ranges_def, memory_range_of_operands_def,
     REVERSE_APPEND] >>
  rpt strip_tac >> first_x_assum (qspec_then `w2n off+i` mp_tac) >> simp[]
QED

Theorem concretize_log_demand_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\ s.vs_call_ctx = t.vs_call_ctx /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) Obs s t /\
  inst.inst_opcode = LOG ==>
  ?entry. post = s with vs_logs := s.vs_logs ++ [entry] /\
    step_inst_base inst t = OK (t with vs_logs := t.vs_logs ++ [entry])
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def]) >>
  drule_all log_execution_envelope >> strip_tac >>
  drule_all log_reversed_tail >> strip_tac >> gvs[REVERSE_APPEND] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!op. MEM op (opn::tops) ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     drule_at (Pat `local_rel _ _ _ _ _ _ _`) log_scalar_agreement >>
     disch_then irule >> simp[REVERSE_APPEND] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     qexistsl_tac [`opd`, `opn`, `tc`, `tops`] >> simp[] >> fs[] >> metis_tac[]) >>
  `eval_operand opn t = SOME sz` by metis_tac[listTheory.MEM] >>
  `eval_operands tops t = SOME topics` by
    (qsuff_tac `eval_operands tops s = eval_operands tops t` >- metis_tac[] >>
     qpat_x_assum `!op. MEM op _ ==> _` mp_tac >>
     qid_spec_tac `tops` >> Induct >> simp[eval_operands_def] >>
     rpt strip_tac >> fs[] >> metis_tac[]) >>
  `?offT. eval_operand opd t = SOME offT /\
     (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
       joint_relocation_demand lo (concretize_positions C') q0 es qs c
         (w2n off+i) (w2n offT+i))` by
    (irule concretize_read_demand_geometry >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, REVERSE_APPEND] >>
     Cases_on `tops` >> gvs[] >> metis_tac[]) >>
  `TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n offT) t.vs_memory ++ REPLICATE (w2n sz) 0w)` by
    (irule listTheory.LIST_EQ >>
     simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
     qx_gen_tac `j` >> strip_tac >>
     `w2n off+j NOTIN tn.t_mem` by
       (irule log_read_clean >> simp[REVERSE_APPEND] >> metis_tac[]) >>
     `codegenRel$read_byte (w2n off+j) s.vs_memory =
      codegenRel$read_byte (w2n offT+j) t.vs_memory` by
       (drule local_rel_demand >> simp[demand_agree_def] >>
        metis_tac[arithmeticTheory.ADD_COMM]) >>
     fs[codegenRelTheory.read_byte_def] >> simp[EL_TAKE] >>
     Cases_on `w2n off+j < LENGTH s.vs_memory` >>
     Cases_on `w2n offT+j < LENGTH t.vs_memory` >>
     gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
         LENGTH_DROP, rich_listTheory.EL_DROP, rich_listTheory.EL_REPLICATE]) >>
  qexists_tac `<| logger := w2w s.vs_call_ctx.cc_address; topics := topics;
    data := TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) |>` >>
  conj_tac >- simp[] >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  drule_all eval_operands_domain_agreement >>
  disch_then (qspec_then `inst.inst_operands` assume_tac) >>
  qpat_x_assum `IS_SOME _ <=> IS_SOME _` mp_tac >>
  simp[REVERSE_APPEND] >> strip_tac >>
  simp[step_inst_base_def, REVERSE_APPEND]
QED

Theorem log_ghosts[local]:
  inst.inst_opcode = LOG /\ inst.inst_outputs = [] ==>
  step_prov PG G inst post = G /\
  step_taint inst s (s with vs_logs := logs) tn = tn /\
  step_writes inst s post = []
Proof
  strip_tac >>
  `new_site_bytes s (s with vs_logs := logs) = {}` by
    (irule new_site_bytes_unchanged >> simp[]) >>
  simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, set_var_taint_def, taint_component_equality,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  rpt conj_tac >> rpt gen_tac >> rpt CASE_TAC >> simp[]
QED

Theorem log_local_update[local]:
  local_rel P V B R (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  (!a b. R' a b ==> R a b) ==>
  local_rel P V B R' (\s t. dead_result_rel D (Halt s) (Halt t))
    (s with vs_logs := s.vs_logs ++ [entry])
    (t with vs_logs := t.vs_logs ++ [entry])
Proof
  simp[local_rel_def, local_values_def, variable_domains_def,
       variables_agree_on_def, lookup_var_def, dead_result_rel_def,
       demand_agree_def] >> metis_tac[]
QED

Theorem concretize_log_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  inst.inst_opcode = LOG ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    step_prov PG G inst post = SND o_f rv /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels /\ s.vs_call_ctx = t.vs_call_ctx` by
    fs[relocation_env_def] >>
  drule_all concretize_log_demand_execution >> strip_tac >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >>
     metis_tac[resolved_frame_erasure]) >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, venomWfTheory.fn_inst_wf_def,
        venomInstTheory.fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     simp[venomWfTheory.inst_wf_def, venomInstTheory.opcode_case_def] >> metis_tac[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, log_ghosts, range_bytes_def] >> metis_tac[]) >>
  qexists_tac `t with vs_logs := t.vs_logs ++ [entry]` >> gvs[] >>
  simp[log_ghosts] >>
  conj_tac >- (irule log_local_update >> metis_tac[]) >>
  conj_tac >- (fs[relocation_taint_le_def, demand_taint_def] >> metis_tac[]) >>
  fs[relocation_env_def, relocation_reader_context_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "LOG export has hypotheses")
  [concretize_log_demand_execution, concretize_log_local_complete];

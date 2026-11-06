Theory concretizeLayoutCallResult
Ancestors concretizeLayoutCallControl frameRelocationCleanOperands
  memLocDefs pointerConfinedDefs ptrDiscipline o1PassContract
  frameRelocationGuardedValues frameRelocationOpaque frameRelocationLocal
  frameRelocationGhostCopy
  venomState venomExecSemantics frameRelocationValues
  concretizeLayoutLocalTerminals concretizeLayoutPhaseOrigin
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameResolvedTrace frameRelocationReachableSupport frameRelocationEnvironment
  frameRelocationBinding frameRelocationDemand frameJointDemand
  codegenRel contextCodegenRel concretizeLayoutSupplement venomInstProofs1
  concretizeLayoutReaderContext
  finite_map list rich_list

(* RET cannot export allocation pointers: the syntactic discipline only permits
   them as addresses, pointer-preserving inputs or selected comparisons. *)
Theorem layout_ret_pointer_absent:
  ptr_use_ok P pv inst /\ inst.inst_opcode = RET /\
  MEM (Var v) inst.inst_operands ==> v NOTIN pv
Proof
  strip_tac >> gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_read_ops_def, mem_write_ops_def] >> metis_tac[]
QED

Theorem layout_ret_front_clean:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  MEM (Var v) (FRONT inst.inst_operands) ==>
  clean_scalar (retpc_var fn) rv tn v
Proof
  strip_tac >>
  `MEM (Var v) inst.inst_operands` by
    (Cases_on `inst.inst_operands = []` >> gvs[] >>
     metis_tac[APPEND_FRONT_LAST, MEM_APPEND]) >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  `v NOTIN fn_pv P fn` by metis_tac[layout_ret_pointer_absent] >>
  simp[clean_scalar_def] >> rpt conj_tac
  >- (strip_tac >> drule_all disciplined_retpc_operand_use >>
      strip_tac >> gvs[FRONT_APPEND])
  >- metis_tac[] >>
  irule taint_ok_operand_exclusion >> qexistsl_tac [`fn`, `inst`, `s`] >> simp[]
QED

Theorem layout_ret_front_operand_agreement:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  MEM op (FRONT inst.inst_operands) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> irule guarded_scalar_operand >> simp[] >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  irule layout_ret_front_clean >> metis_tac[]
QED

Theorem layout_ret_front_evaluation[local]:
  !ops s t. (!op. MEM op ops ==> eval_operand op s = eval_operand op t) ==>
    eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  `eval_operand h s = eval_operand h t` by metis_tac[] >>
  `eval_operands ops s = eval_operands ops t` by
    (first_x_assum irule >> metis_tac[]) >> simp[]
QED

Theorem layout_ret_front_agreement:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operands (FRONT inst.inst_operands) s =
    eval_operands (FRONT inst.inst_operands) t
Proof
  strip_tac >> irule layout_ret_front_evaluation >> rpt strip_tac >>
  irule layout_ret_front_operand_agreement >> metis_tac[]
QED

Theorem layout_eval_front[local]:
  !ops s vals. eval_operands ops s = SOME vals ==>
    eval_operands (FRONT ops) s = SOME (FRONT vals) /\ LENGTH vals = LENGTH ops
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `ops` >> gvs[eval_operands_def] >>
  first_x_assum drule >> simp[FRONT_DEF] >> strip_tac >>
  Cases_on `vs` >> gvs[]
QED

Theorem layout_ret_execution:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = RET /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t /\
  step_inst fuel C inst s = IntRet ret send ==>
  ?ret'. step_inst fuel' C' inst t = IntRet ret' t /\ send = s /\
    ret.iret_values = ret'.iret_values /\
    ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE
Proof
  strip_tac >>
  `eval_operands (FRONT inst.inst_operands) s =
    eval_operands (FRONT inst.inst_operands) t` by
    (irule layout_ret_front_agreement >> metis_tac[]) >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  qpat_x_assum `step_inst fuel C inst s = IntRet ret send` mp_tac >>
  simp[step_inst_def, Once step_inst_base_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_operands inst.inst_operands s = SOME (head::tail)` >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (drule_all eval_operands_domain_agreement >>
     disch_then (qspec_then `inst.inst_operands` mp_tac) >> simp[]) >>
  Cases_on `eval_operands inst.inst_operands t` >> gvs[] >>
  drule layout_eval_front >> strip_tac >>
  `eval_operands (FRONT inst.inst_operands) s = SOME (FRONT (head::tail))` by
    metis_tac[layout_eval_front] >>
  `FRONT x = FRONT (head::tail)` by metis_tac[optionTheory.SOME_11] >>
  Cases_on `x` >> gvs[] >>
  simp[Once step_inst_base_def]
QED

(* The endpoint retains the selected callee snapshot, including its activation
   stack, annotations, demand, supplement and reader environment. *)
Definition layout_ret_endpoint_def:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g s t ret ret' <=>
    ~g.lop_pending /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
    (?stk PG G tn fn inst oms om hs h.
      g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
      inst.inst_opcode = RET) /\
    ret.iret_values = ret'.iret_values /\
    ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE
End

Theorem layout_ret_endpoint_produce:
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RET /\ step_inst fuel C inst s = IntRet ret send ==>
  ?ret'. step_inst fuel' C' inst t = IntRet ret' t /\ send = s /\
    layout_ret_endpoint D lo vs0 C C' q0 es qs q g s t ret ret'
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_trace_def, layout_ordinary_state_def] >> rpt strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `g.lop_cursor <= LENGTH es` by fs[] >>
  `joint_config_reachable vs0 C g.lop_config` by
    (drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (gvs[resolved_config_ok_def] >>
     metis_tac[reachable_resolved_support]) >>
  drule_all layout_ret_execution >>
  disch_then (qspecl_then [`fuel'`, `C'`] strip_assume_tac) >>
  qexists `ret'` >> simp[layout_ret_endpoint_def] >> metis_tac[]
QED

(* Binding the same clean return vector restores the saved caller variables.
   The relation is unrestricted on outputs before binding, since they are dead. *)
Theorem layout_bind_return_values[local]:
  !outs vals s t.
  LENGTH outs = LENGTH vals /\
  (!v x y. v NOTIN set outs /\ lookup_var v s = SOME x /\
       lookup_var v t = SOME y ==> Rel v x y /\ Bytes v x y) /\
  (!v x. MEM v outs ==> Rel v x x /\ Bytes v x x) ==>
  local_values Rel Bytes
    (FOLDL (\st (v,x). update_var v x st) s (ZIP (outs,vals)))
    (FOLDL (\st (v,x). update_var v x st) t (ZIP (outs,vals)))
Proof
  Induct
  >- (Cases_on `vals` >> simp[local_values_def]) >>
  qx_gen_tac `out` >> Cases_on `vals` >> simp[] >>
  rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> Cases_on `v = out` >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem layout_ret_endpoint_bind_values:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g sc tc ret ret' /\
  variable_domains caller caller' /\
  local_values (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv caller_tn) caller caller' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post ==>
  ?post'. bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' /\
    variable_domains post post' /\
    local_values (guarded_ptr Opaque L (DRESTRICT rv (COMPL (set outs))))
      (guarded_bytes Opaque (DRESTRICT rv (COMPL (set outs)))
        (callee_tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set outs)))) post post'
Proof
  simp[layout_ret_endpoint_def, bind_outputs_def, adopt_return_fmp_def] >>
  rpt strip_tac >> gvs[]
  >- (irule variable_domains_bind_fold >>
      gvs[variable_domains_def, lookup_var_def, merge_callee_state_def]) >>
  irule layout_bind_return_values >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      gvs[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
        FLOOKUP_DRESTRICT, op_taint_def, lookup_var_def, merge_callee_state_def,
        local_values_def] >> metis_tac[]) >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def, copy_bytes_def,
    FLOOKUP_DRESTRICT, op_taint_def, word_agree_except_def]
QED

Theorem layout_ret_endpoint_demand:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g s t ret ret' /\
  vs0.vs_allocas = FEMPTY /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginResume fuel fn inst s ret s post) /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  inst.inst_opcode = RET ==>
  demand_agree
    (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
    (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory)
Proof
  simp[layout_ret_endpoint_def] >> rpt strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  gvs[layout_ordinary_trace_def, layout_ordinary_state_def] >>
  drule local_rel_demand >>
  simp[demand_agree_def] >> strip_tac >> rpt strip_tac >>
  first_x_assum irule >> irule joint_relocation_demand_retained >>
  goal_assum (drule_at Any) >>
  simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
    range_bytes_def] >> metis_tac[]
QED

Theorem layout_return_bind_fields[local]:
  ret.iret_adopt_fmp = NONE /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME post ==>
  post = (merge_callee_state caller callee) with vs_vars := post.vs_vars
Proof
  strip_tac >> gvs[adopt_return_fmp_def] >>
  `post with vs_vars := FEMPTY =
    (merge_callee_state caller callee) with vs_vars := FEMPTY` by
    (irule bind_outputs_preserves >> simp[update_var_def] >>
     goal_assum (drule_at Any) >> simp[adopt_return_fmp_def]) >>
  gvs[venom_state_component_equality]
QED

Theorem layout_ret_endpoint_restore:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g sc tc ret ret' /\
  vs0.vs_allocas = FEMPTY /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginResume fuel fn inst sc ret sc post) /\
  g.lop_config = JointConfig stk PG G tn fn inst sc oms om hs h /\
  inst.inst_opcode = RET /\
  variable_domains caller caller' /\
  local_values (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv caller_tn) caller caller' /\
  concretize_local_obs caller caller' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post ==>
  ?post'. bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' /\
    local_rel (\v. F)
      (guarded_ptr Opaque L (DRESTRICT rv (COMPL (set outs))))
      (guarded_bytes Opaque (DRESTRICT rv (COMPL (set outs)))
        (tn with t_var := DRESTRICT caller_tn.t_var (COMPL (set outs))))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC g.lop_cursor))
      concretize_local_obs post post'
Proof
  strip_tac >> drule_all layout_ret_endpoint_bind_values >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  `ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE` by
    fs[layout_ret_endpoint_def] >>
  `post = (merge_callee_state caller sc) with vs_vars := post.vs_vars` by
    metis_tac[layout_return_bind_fields] >>
  `post' = (merge_callee_state caller' tc) with vs_vars := post'.vs_vars` by
    metis_tac[layout_return_bind_fields] >>
  drule_all layout_ret_endpoint_demand >> strip_tac >>
  `concretize_local_obs sc tc` by
    (gvs[layout_ret_endpoint_def, layout_ordinary_entry_def,
       layout_ordinary_state_def] >> metis_tac[local_rel_observation]) >>
  qexists `post'` >> simp[local_rel_def, variables_agree_on_def] >>
  conj_tac
  >- (qpat_assum `post = _` (once_rewrite_tac o single) >>
      qpat_assum `post' = _` (once_rewrite_tac o single) >>
      gvs[demand_agree_def, merge_callee_state_def]) >>
  qpat_assum `post = _` (once_rewrite_tac o single) >>
  qpat_assum `post' = _` (once_rewrite_tac o single) >>
  gvs[concretize_local_obs_def, dead_result_rel_def, merge_callee_state_def]
QED

Theorem layout_ret_endpoint_restore_supplement:
  layout_ret_endpoint D lo vs0 C C' q0 es qs q g sc tc ret ret' /\
  g.lop_config = JointConfig stk PG G tn fn inst sc oms om hs h /\
  caller.vs_call_ctx.cc_address = sc.vs_call_ctx.cc_address /\
  relocation_env caller caller' /\ relocation_reader_context caller caller' /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs outs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  concretize_supplement D
    (tn with t_var := DRESTRICT caller_tv (COMPL (set outs))) post post' /\
  relocation_env post post' /\ relocation_reader_context post post'
Proof
  strip_tac >>
  `concretize_supplement D tn sc tc /\ relocation_env sc tc` by
    gvs[layout_ret_endpoint_def, layout_ordinary_entry_def, layout_ordinary_state_def] >>
  `ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE` by
    fs[layout_ret_endpoint_def] >>
  `post = (merge_callee_state caller sc) with vs_vars := post.vs_vars` by
    metis_tac[layout_return_bind_fields] >>
  `post' = (merge_callee_state caller' tc) with vs_vars := post'.vs_vars` by
    metis_tac[layout_return_bind_fields] >>
  qpat_assum `post = _` (once_rewrite_tac o single) >>
  qpat_assum `post' = _` (once_rewrite_tac o single) >>
  gvs[concretize_supplement_def, relocation_env_def,
    relocation_reader_context_def, merge_callee_state_def]
QED

val _ = export_theory();

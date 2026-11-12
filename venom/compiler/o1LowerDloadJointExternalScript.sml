(* External family integration: masked oracle and concrete EVM boundaries. *)
Theory o1LowerDloadJointExternal
Ancestors
  o1LowerDloadJointExternalUpdate o1LowerDloadConcreteExternal
  o1LowerDloadExternalEffects o1LowerDloadExternalOracle o1LowerDloadPrecompileEffects
  o1LowerDloadJointRangeRead o1LowerDloadJointRangeCopy
  o1LowerDloadJointRelation o1LowerDloadShared o1PassContract venomCallOracleProps
  o1LowerDloadOccurrence o1LowerDloadJointScalar o1LowerDloadOpaque
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel pointerConfinedDefs finite_map memLocDefs
  ptrDiscipline venomExecSemantics venomCallOracleDefs extCallOracle
  venomState list pred_set venomInst unitShapeDefs contextCodegenRel codegenRel

Theorem ld_venom_call_request_masked:
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n off') (w2n sz) t ==>
  request_agree_except D
    (venom_call_request s addr value off sz static)
    (venom_call_request t addr value off' sz static)
Proof
  simp[request_agree_except_def, venom_call_request_def,
       call_request_component_equality]
QED

Theorem ld_joint_call_shared_observation:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_src_inv D C vs /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK s1 /\
  LENGTH s.vs_requests < LENGTH s1.vs_requests ==>
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient
Proof
  (* P4a in progress *) cheat
QED

(* Pointer operands have exactly one occurrence, at an address position.
   A scalar alias at another position therefore cannot carry provenance. *)
Theorem ld_joint_external_scalar_clean:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov H op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `op_prov H op = NONE` by
    (drule ld_joint_nonaddress_no_provenance >> disch_then irule >>
     gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  simp[]
QED

Theorem ld_joint_external_scalar_operand:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\
  (!ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
    ops.iao_ofst <> op) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `op_prov H op = NONE /\ op_taint tn op = {}` by
    (irule ld_joint_external_scalar_clean >> metis_tac[]) >>
  irule ld_joint_operand_clean >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]
QED

Theorem ld_joint_external_input_slice:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    read_memory (w2n x) len s = read_memory (w2n y) len t
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_concrete_shared_inputs:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [DELEGATECALL;CREATE;CREATE2] ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_delegatecall_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [gop;adop;offop;szop;rop;rsop] /\
  eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  ?off' ro'. eval_operand gop t = SOME gas /\
    eval_operand adop t = SOME addr /\ eval_operand offop t = SOME off' /\
    eval_operand szop t = SOME sz /\ eval_operand rop t = SOME ro' /\
    eval_operand rsop t = SOME rs /\
    read_memory (w2n off) (w2n sz) s =
      read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ (w2n ro+w2n rs<=lo \/
       dyn_floor C vs<=w2n ro /\ w2n ro+w2n rs<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_delegatecall_execute:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DELEGATECALL /\ step_inst fuel C inst s = OK s1 ==>
  ?out w r rq ro ro' rs.
    inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    ~computed_precompile rq /\
    r = s with <|
      vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_outcomes := r.vs_outcomes;
      vs_requests := record_request rq s.vs_requests;
      vs_memory := (write_memory_with_expansion ro
        (TAKE rs r.vs_returndata) s).vs_memory |> /\
    step_inst fuel C' inst t = OK (update_var out w (t with <|
      vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_outcomes := r.vs_outcomes;
      vs_requests := record_request rq t.vs_requests;
      vs_memory := (write_memory_with_expansion ro'
        (TAKE rs r.vs_returndata) t).vs_memory |>)) /\
    request_agree_except D rq rq /\
    source_memory_write_ranges inst s = [(ro,rs)] /\
    (rs=0 \/ (ro=ro' /\ (ro+rs<=lo \/
       dyn_floor C vs<=ro /\ ro+rs<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+rs<=z /\
                    ro=b+j /\ ro'=c+j))
Proof
  (* P4a in progress *) cheat
QED

(* External effects change shared fields as well as the output variable. *)
Theorem ld_env_external_clean_update:
  ld_env_agree sites fn H tn s t /\ inst.inst_outputs = [out] /\
  s1.vs_vars = s.vs_vars |+ (out,x) /\
  t1.vs_vars = t.vs_vars |+ (out,x) /\
  occurrence_out a HP H inst s1 = NONE /\ out_taint tn inst s = {} ==>
  ld_env_agree sites fn (occurrence_step a HP H inst s1)
    (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >>
  simp[ld_env_agree_def, FLOOKUP_UPDATE,
       occurrence_step_def, set_prov_def, FLOOKUP_DRESTRICT,
       step_taint_def, set_var_taint_def, op_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `v = out` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `v = out` >>
  gvs[ld_env_agree_def, op_taint_def, ld_value_agree_scalar,
      word_agree_except_def] >> rpt strip_tac >> gvs[]
QED

Theorem ld_joint_delegatecall_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ~in_revert_forward fn s /\ inst.inst_opcode = DELEGATECALL /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_create_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\ rest = []) \/
   (inst.inst_opcode = CREATE2 /\ ?salt sw.
      inst.inst_operands = [vop;offop;szop;salt] /\ rest = [salt] /\
      eval_operand salt s = SOME sw)) /\
  eval_operand vop s = SOME value /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz ==>
  (!op. MEM op (vop::szop::rest) ==> eval_operand op s = eval_operand op t) /\
  ?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t
Proof
  strip_tac >> (
  `!op. MEM op (vop::szop::rest) ==>
     op_prov H op = NONE /\ op_taint tn op = {}` by
    (gen_tac >> disch_tac >>
     drule ld_joint_external_scalar_clean >> disch_then irule >>
     gvs[Excl "FILTER", MEM, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[FILTER, SF boolSimps.COND_elim_ss]) >>
  conj_tac
  >- (rpt strip_tac >> irule ld_joint_operand_clean >>
      `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
      metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  drule ld_joint_external_input_slice >> disch_then irule >>
  gvs[mem_read_ops_def, source_memory_read_ranges_def,
      memory_range_of_operands_def])
QED

Theorem ld_exec_create_transport[local]:
  s.vs_outcomes = t.vs_outcomes /\ s.vs_accounts = t.vs_accounts /\
  s.vs_transient = t.vs_transient /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  venom_create_request s value off sz salt = rq /\
  venom_create_request t value off' sz salt = rq /\
  exec_create inst s value off sz salt = OK s1 ==>
  ?out w r. inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|> /\
    exec_create inst t value off' sz salt = OK (update_var out w (t with <|
      vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq t.vs_requests|>))
Proof
  strip_tac >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  strip_tac >> Cases_on `consume_create_outcome rq s` >>
  gvs[Excl "consume_create_outcome_eq"] >>
  drule_all ld_consume_create_outcome_transport >>
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qexistsl_tac [`q`,`r`] >>
  simp[Excl "consume_create_outcome_eq", venom_state_fupdcanon] >>
  qpat_x_assum `r = _` mp_tac >> simp[venom_state_fupdcanon]
QED

Theorem ld_joint_create_execute:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\ step_inst fuel C inst s = OK s1 ==>
  ?out w r rq. inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    ~computed_precompile rq /\
    r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|> /\
    step_inst fuel C' inst t = OK (update_var out w (t with <|
      vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq t.vs_requests|>)) /\
    request_agree_except D rq rq
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_create_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_call_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop]) \/
   (inst.inst_opcode = STATICCALL /\ prefix = [gop;adop])) /\
  inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
  (!op. MEM op prefix ==> ?w. eval_operand op s = SOME w) /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  (!op. MEM op (prefix ++ [szop;rsop]) ==> eval_operand op s = eval_operand op t) /\
  ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ (w2n ro+w2n rs<=lo \/
       dyn_floor C vs<=w2n ro /\ w2n ro+w2n rs<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_call_outcome_effects[local]:
  ld_shared_agree D A tn s t /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
     rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
   request_agree_except D rq1 rq2) /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  w1 = w2 /\ s1.vs_returndata = t1.vs_returndata /\
  ld_shared_agree D A
    (tn with <|t_stor := if s1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
               t_trans := if s1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
    s1 t1 /\
  ld_shared_agree D A
    (tn with <|t_stor := if ~rq1.cr_static /\ s1.vs_requests <> s.vs_requests /\
                  s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                then {} else tn.t_stor;
               t_trans := if ~rq1.cr_static /\ s1.vs_requests <> s.vs_requests /\
                  s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                then {} else tn.t_trans|>) s1 t1
Proof
  strip_tac
  >- (`s1.vs_requests = s.vs_requests` by
        (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
         simp[consume_call_outcome_eq, record_request_def] >> strip_tac >>
         gvs[Excl "consume_call_outcome_eq"]) >>
      drule_all ld_consume_precompile_shared >> strip_tac >>
      simp[Excl "consume_call_outcome_eq"]) >>
  `s.vs_outcomes = t.vs_outcomes /\
   LIST_REL (request_agree_except D) s.vs_requests t.vs_requests` by
    fs[ld_shared_agree_def] >>
  drule_all ld_consume_call_outcome_masked_observation >> strip_tac >> simp[] >>
  drule_all ld_consume_call_outcome_shared_effects >> simp[]
QED

Theorem ld_joint_call_execute_effects[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_src_inv D C vs /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out w r1 r2 rq1 rq2 (ro:bytes32) (rs:bytes32) (ro':bytes32).
    inst.inst_outputs = [out] /\ s1 = update_var out w r1 /\
    step_inst fuel C' inst t = OK (update_var out w r2) /\
    consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w,r1) /\
    consume_call_outcome rq2 (w2n ro') (w2n rs) t = (w,r2) /\
    r1.vs_returndata = r2.vs_returndata /\
    ld_shared_agree D s.vs_call_ctx.cc_address
      (tn with <|t_stor := if r1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
                 t_trans := if r1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
      r1 r2 /\
    source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ (w2n ro+w2n rs<=lo \/
       dyn_floor C vs<=w2n ro /\ w2n ro+w2n rs<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j)) /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
      s1 (update_var out w r2)
Proof
  (* P4a in progress *) cheat
QED


Theorem ld_joint_call_execute:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_src_inv D C vs /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
  step_inst fuel C inst s = OK s1 ==>
  ?out w r1 r2 rq1 rq2 (ro:bytes32) (rs:bytes32) (ro':bytes32).
    inst.inst_outputs = [out] /\ s1 = update_var out w r1 /\
    step_inst fuel C' inst t = OK (update_var out w r2) /\
    consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w,r1) /\
    consume_call_outcome rq2 (w2n ro') (w2n rs) t = (w,r2) /\
    r1.vs_returndata = r2.vs_returndata /\
    ld_shared_agree D s.vs_call_ctx.cc_address
      (tn with <|t_stor := if r1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
                 t_trans := if r1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
      r1 r2 /\
    source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ (w2n ro+w2n rs<=lo \/
       dyn_floor C vs<=w2n ro /\ w2n ro+w2n rs<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_consume_call_shape[local]:
  consume_call_outcome rq ro rs s = (w,r) ==>
  r = s with <|vs_memory := (write_memory_with_expansion ro
      (TAKE rs r.vs_returndata) s).vs_memory;
    vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
    vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
    vs_requests := r.vs_requests; vs_pending_deletions := r.vs_pending_deletions;
    vs_returndata := r.vs_returndata|>
Proof
  simp[consume_call_outcome_eq] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem ld_joint_call_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_src_inv D C vs /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

(* Contract creation at the FMP boundary. *)
Theory fmpStageOpSimMemCreates
Ancestors
  fmpStageOpSimMemCalls fmpStageOpSimMemReads fmpStageOpSimMemSupport
  fmpStageOpBase fmpStageRel o1LowerDloadExternalEffects o1LowerDloadShared
  o1LowerDloadConcreteExternal o1LowerDloadRelocationKernel
  memLocDefs ptrDiscipline contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomCallOracleDefs
  extCallOracle venomState venomInst words finite_map pred_set list

Theorem fmp_mem_create_operands[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\ rest = []) \/
   (inst.inst_opcode = CREATE2 /\ ?salt sw.
      inst.inst_operands = [vop;offop;szop;salt] /\ rest = [salt] /\
      eval_operand salt s = SOME sw)) /\
  eval_operand vop s = SOME value /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz ==>
  (!op x. MEM op (vop::szop::rest) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
  ?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t
Proof
  strip_tac >> (
  conj_tac
  >- (rpt strip_tac >> irule fmp_mem_external_scalar >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
      gvs[Excl "FILTER", mem_read_ops_def, mem_write_ops_def] >>
      rpt strip_tac >> gvs[Excl "FILTER"] >>
      qpat_x_assum `FILTER _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [FILTER] >> rpt IF_CASES_TAC >> simp[]) >>
  irule fmp_mem_external_input >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  gvs[mem_read_ops_def, source_memory_read_ranges_def, memory_range_of_operands_def])
QED

Theorem fmp_mem_create_world[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CREATE;CREATE2] ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by (fs[taint_ok_def, MEM] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  metis_tac[ld_shared_clean_accounts, ld_shared_clean_transient]
QED

Theorem fmp_mem_create_inputs[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst k C inst s = OK s1 ==>
  ?vop offop szop value off off' sz salt rest.
    eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
    eval_operand szop s = SOME sz /\
    eval_operand vop t = SOME value /\ eval_operand offop t = SOME off' /\
    eval_operand szop t = SOME sz /\
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\
      rest = [] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw.
      inst.inst_operands = [vop;offop;szop;sop] /\ rest = [sop] /\
      eval_operand sop s = SOME sw /\ eval_operand sop t = SOME sw /\ salt = SOME sw)) /\
    ~s.vs_call_ctx.cc_static /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    exec_create inst s value off sz salt = OK s1
Proof
  strip_tac >>
  `?vop offop szop value off sz salt rest.
    eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
    eval_operand szop s = SOME sz /\
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\
      rest = [] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw.
      inst.inst_operands = [vop;offop;szop;sop] /\ rest = [sop] /\
      eval_operand sop s = SOME sw /\ salt = SOME sw)) /\
    ~s.vs_call_ctx.cc_static /\ exec_create inst s value off sz salt = OK s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operands_def] >> metis_tac[]) >>
  `(!op x. MEM op (vop::szop::rest) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
   ?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (irule fmp_mem_create_operands >> simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`vop`,`offop`,`szop`,`value`,`off`,`off'`,`sz`,`salt`,`rest`] >>
  gvs[] >> metis_tac[]
QED

Theorem fmp_mem_create_execute[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  step_inst k C inst s = OK s1 ==>
  ?out w r rq. inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    ~computed_precompile rq /\
    r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|> /\
    step_inst k C' inst t = OK (update_var out w (t with <|
      vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq t.vs_requests|>))
Proof
  strip_tac >> drule_all fmp_mem_create_inputs >> strip_tac >> (
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    metis_tac[fmp_mem_create_world] >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[fmp_stage_rel_def, ld_shared_agree_def] >>
  `venom_create_request t value off' sz salt =
   venom_create_request s value off sz salt` by simp[venom_create_request_def] >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  strip_tac >> Cases_on `consume_create_outcome (venom_create_request s value off sz salt) s` >>
  gvs[Excl "consume_create_outcome_eq"] >>
  drule_all ld_consume_create_outcome_transport >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_create_outcome rq s` >>
  qexistsl_tac [`q`,`r`,`rq`] >>
  simp[Excl "consume_create_outcome_eq", venom_state_fupdcanon] >>
  conj_tac >- simp[Abbr `rq`, venom_create_request_def, computed_precompile_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  gvs[Abbr `rq`, Excl "consume_create_outcome_eq"] >> metis_tac[])
QED

Theorem fmp_mem_creates_ok[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    (!v. ~MEM v inst.inst_outputs ==>
      FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
      FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
    (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
      ?y. FLOOKUP t1.vs_vars v = SOME y /\
        (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
          (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
    ld_memory_agree (fmp_ld_sites sm) eom
      (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
    s1.vs_returndata = t1.vs_returndata /\
    ~s1.vs_halted /\ ~t1.vs_halted /\
    s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
    s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
    s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
    s1.vs_block_ctx = s.vs_block_ctx /\ s1.vs_data_section = s.vs_data_section /\
    s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
    s1.vs_prev_hashes = s.vs_prev_hashes /\
    s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
    t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
    t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
    t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
    t1.vs_block_ctx = t.vs_block_ctx /\ t1.vs_data_section = t.vs_data_section /\
    t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
    t1.vs_prev_hashes = t.vs_prev_hashes /\
    t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
Proof
  strip_tac >> drule_all fmp_mem_create_execute >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst k C' inst t = OK target` >>
  `ld_memory_agree (fmp_ld_sites sm) eom (step_taint inst s s1 tn).t_mem
      s1.vs_memory target.vs_memory` by suspend "memory" >>
  `ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
      s1 target` by suspend "shared" >>
  `out_taint tn inst s = {}` by
    (drule_all fmp_mem_create_inputs >> strip_tac >> gvs[out_taint_def]) >>
  qexists_tac `target` >> simp[] >>
  `s.vs_halted = t.vs_halted` by fs[fmp_stage_rel_def] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  simp[Abbr `target`, update_var_def, FLOOKUP_UPDATE] >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       op_taint_def, set_var_taint_def, fmp_value_rel_def, ld_value_agree_def,
       FLOOKUP_DRESTRICT, MEM] >>
  gvs[MEM] >> simp[word_agree_except_def, FLOOKUP_DRESTRICT]
QED

Resume fmp_mem_creates_ok[memory]:
  drule_all fmp_mem_create_inputs >> strip_tac >> (
  `source_memory_write_ranges inst s = []` by
    gvs[MEM, source_memory_write_ranges_def] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       range_bytes_def, update_var_def, Abbr `target`] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  `new_site_bytes s (s with <|vs_vars := s.vs_vars |+ (out,w);
      vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request rq s.vs_requests|>) = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[MEM, written_taint_def, fmp_stage_rel_def])
QED

Resume fmp_mem_creates_ok[shared]:
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  simp[ld_shared_agree_def, step_taint_def, imm_taint_def,
       update_var_def, Abbr `target`, word_agree_except_def] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  fs[ld_shared_agree_def, word_agree_except_def] >>
  simp[record_request_def, LIST_REL_APPEND, request_agree_except_def,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, word_agree_except_def]
QED

Finalise fmp_mem_creates_ok

Theorem fmp_mem_create_size_abort[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CREATE;CREATE2] /\
  ~s.vs_call_ctx.cc_static /\ step_inst k C inst s = r /\
  terminates r /\ ~(?s1. r = OK s1) ==>
  step_inst k C' inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)) /\
  r = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >>
  `?vop offop szop value off sz rest.
    eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
    eval_operand szop s = SOME sz /\ w2n sz > 2 * max_code_size /\
    (?out. inst.inst_outputs = [out]) /\
    ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\ rest = []) \/
     (inst.inst_opcode = CREATE2 /\ ?sop sw.
      inst.inst_operands = [vop;offop;szop;sop] /\ rest = [sop] /\
      eval_operand sop s = SOME sw)) /\
    r = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_create_def,
          AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
     rpt strip_tac >> gvs[passSimulationDefsTheory.terminates_def, AllCaseEqs(),
                          consume_create_outcome_eq] >> metis_tac[]) >>
  `(!op x. MEM op (vop::szop::rest) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
   ?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (irule fmp_mem_create_operands >> simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `eval_operand vop t = SOME value /\ eval_operand szop t = SOME sz /\
   (!op x. MEM op rest /\ eval_operand op s = SOME x ==> eval_operand op t = SOME x)` by
    metis_tac[MEM] >>
  qpat_x_assum `!op x. MEM op (vop::szop::rest) /\ _ ==> _` kall_tac >>
  gvs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
                exec_create_def, Excl "consume_create_outcome_eq"] >>
  metis_tac[MEM]
QED

Theorem fmp_mem_create_static_abort[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\ s.vs_call_ctx.cc_static /\
  step_inst k C inst s = r /\ terminates r ==>
  step_inst k C' inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)) /\
  r = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) /\
   r = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operands_def, passSimulationDefsTheory.terminates_def]) >>
  `IS_SOME (eval_operands inst.inst_operands t)` by
    (fs[eval_operands_IS_SOME_EVERY, EVERY_MEM] >> rpt strip_tac >>
     rename1 `MEM op inst.inst_operands` >>
     `?x. eval_operand op s = SOME x` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
     `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
     `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
     drule_all fmp_stage_operand >> strip_tac >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  fs[] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

(* Creation part of the frozen call simulation. *)
Theorem fmp_mem_creates_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >> Cases_on `?s1. r = OK s1`
  >- (qpat_x_assum `?s1. r = OK s1` (qx_choose_then `s1` SUBST_ALL_TAC) >>
      drule_all fmp_mem_creates_ok >> strip_tac >>
      qexistsl_tac [`k`,`OK t1`] >> simp[]) >>
  `step_inst k C' inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)) /\
   r = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (Cases_on `s.vs_call_ctx.cc_static`
     >- (drule_all fmp_mem_create_static_abort >> simp[]) >>
     drule_all fmp_mem_create_size_abort >> simp[]) >>
  qexistsl_tac [`k`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`] >>
  gvs[dead_result_rel_def]
QED

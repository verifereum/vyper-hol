(* Effects of the actual external steps at the bounded FMP cursor. *)
Theory gasFocusFmpCutExternalEffect
Ancestors
  gasFocusFmpCutCallExecute gasFocusFmpCutCreateExecute
  concretizeLayoutCutSafe o1LowerDloadPrecompileEffects
  lowerDloadOracleSelection venomCallOracleProps
  lowerDloadExternalEffects lowerDloadExternalMemory lowerDloadPtrResidualInterfaces
  lowerDloadPtrCreateInterfaces
  concretizeLayoutExternalRequests o1RequestContract arithmetic
  o1LowerDloadExternalOracle o1LowerDloadExternalEffects o1LowerDloadShared
  fmpStageRel ptrDiscipline venomExecSemantics venomCallOracleDefs extCallOracle
  o1LowerDloadRelocationKernel passSimulationDefs ptrDisciplineEmptyTaint
  venomState opcodeClass finite_map pred_set list words

Theorem cut_call_request_containment[local]:
  taint_within_upto D n C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK (update_var out w r) /\
  consume_call_outcome rq ro rs s = (w,r) ==>
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  `r.vs_requests = record_request rq s.vs_requests` by
    (mp_tac (Q.INST [`rq` |-> `rq`,`ro` |-> `ro`,`rs` |-> `rs`,`s` |-> `s`] consume_call_outcome_observation) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `LENGTH s.vs_requests < LENGTH (update_var out w r).vs_requests` by
    simp[record_request_def, update_var_def] >>
  `step_inst 0 C inst s = OK (update_var out w r)` by
    simp[step_inst_non_invoke] >>
  drule_all taint_within_upto_request >> simp[]
QED

Theorem cut_call_shared[local]:
  taint_within_upto D n C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  active_inst fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst_base inst s = OK (update_var out w1 r1) /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  rq1 = (venom_call_request s addr value off sz static with
           <|cr_kind := kind; cr_gas := SOME (w2n gas)|>) /\
  rq2 = (venom_call_request t addr value off' sz static with
           <|cr_kind := kind; cr_gas := SOME (w2n gas)|>) /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  consume_call_outcome rq1 ro1 rs s = (w1,r1) /\
  consume_call_outcome rq2 ro2 rs t = (w2,r2) ==>
  w1 = w2 /\ r1.vs_returndata = r2.vs_returndata /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (tn with <|t_stor := if adopt_guard rq1.cr_static s r1 (HD s.vs_outcomes).co_success
                       then {} else tn.t_stor;
               t_trans := if adopt_guard rq1.cr_static s r1 (HD s.vs_outcomes).co_success
                        then {} else tn.t_trans|>) r1 r2
Proof
  strip_tac >>
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
   rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data /\
   rq1.cr_kind = rq2.cr_kind /\ rq1.cr_value = rq2.cr_value` by
    simp[venom_call_request_def] >>
  drule_all cut_call_request_containment >> strip_tac >>
  `accounts_agree_except D s.vs_accounts t.vs_accounts` by
    (irule ld_shared_accounts_observe >> goal_assum drule >> simp[]) >>
  `transient_agree_except D s.vs_transient t.vs_transient` by
    (irule ld_shared_transient_observe >> goal_assum drule >> simp[]) >>
  `request_agree_except D rq1 rq2` by
    simp[request_agree_except_def, venom_call_request_def] >>
  `s.vs_outcomes = t.vs_outcomes /\ LIST_REL (request_agree_except D) s.vs_requests t.vs_requests` by
    fs[ld_shared_agree_def] >>
  drule_all ld_consume_call_outcome_masked_observation >> strip_tac >>
  drule_all ld_consume_call_outcome_shared_effects >> simp[]
QED

val call_ops = ``[CALL;STATICCALL;DELEGATECALL]``;
val create_ops = ``[CREATE;CREATE2]``;

Theorem cut_call_return_memory[local]:
  MEM inst.inst_opcode ^call_ops /\
  source_memory_write_ranges inst s = [(p,n)] /\
  consume_call_outcome rq1 p n s = (w1,r1) /\
  consume_call_outcome rq2 q n t = (w2,r2) /\
  r1.vs_returndata = r2.vs_returndata /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  ld_joint_geometry sites FEMPTY eom owners /\
  (n=0 \/ (p=q /\ p+n<=eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+n<=z /\ p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites eom (step_taint inst s (update_var out w1 r1) tn).t_mem
    (update_var out w1 r1).vs_memory (update_var out w2 r2).vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  every_drule_then strip_assume_tac ld_consume_call_frame_fields >>
  `(step_taint inst s (update_var out w1 r1) tn).t_mem =
   tn.t_mem DIFF {a | p <= a /\ a < p + LENGTH (TAKE n (update_var out w1 r1).vs_returndata)}` by
    (irule ld_external_return_mem_taint >> simp[update_var_def]) >>
  `LENGTH (TAKE n r2.vs_returndata) = MIN n (LENGTH r2.vs_returndata)` by
    simp[LENGTH_TAKE_EQ, MIN_DEF] >>
  `r1.vs_memory = (write_memory_with_expansion p (TAKE n r1.vs_returndata) s).vs_memory /\
   r2.vs_memory = (write_memory_with_expansion q (TAKE n r1.vs_returndata) t).vs_memory` by
    metis_tac[dload_consume_call_memory] >>
  simp[update_var_def] >> irule ld_memory_agree_return_buffer >>
  simp[] >> qexistsl_tac [`FEMPTY`,`0`,`owners`] >> simp[] >>
  `MIN n (LENGTH r2.vs_returndata) <= n` by simp[MIN_LE] >>
  qpat_x_assum `n=0 \/ _` strip_assume_tac
  >- simp[]
  >- (disj2_tac >> disj1_tac >> simp[] >> decide_tac) >>
  disj2_tac >> disj2_tac >> disj1_tac >>
  goal_assum drule >> simp[] >> decide_tac
QED

Theorem cut_call_shared_after_update[local]:
  MEM inst.inst_opcode ^call_ops /\
  (MEM inst.inst_opcode [CALL;DELEGATECALL] ==>
    rq.cr_static = s.vs_call_ctx.cc_static) /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (tn with <|t_stor := if adopt_guard rq.cr_static s r1 (HD s.vs_outcomes).co_success
                       then {} else tn.t_stor;
               t_trans := if adopt_guard rq.cr_static s r1 (HD s.vs_outcomes).co_success
                        then {} else tn.t_trans|>) r1 r2 ==>
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s (update_var out w1 r1) tn)
    (update_var out w1 r1) (update_var out w2 r2)
Proof
  strip_tac >>
  `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by
    fs[MEM] >>
  drule (cj 1 ld_external_taint_projections) >> strip_tac >>
  drule (cj 2 ld_external_taint_projections) >> strip_tac >>
  drule (cj 3 ld_external_taint_projections) >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL;DELEGATECALL]`
  >- gvs[MEM, ld_shared_agree_def, adopt_reset_def, update_var_def] >>
  `inst.inst_opcode = STATICCALL` by fs[MEM] >>
  Cases_on `adopt_guard rq.cr_static s r1 (HD s.vs_outcomes).co_success` >>
  gvs[ld_shared_agree_def, adopt_reset_def, update_var_def, word_agree_except_def]
QED

val external_ops = ``^call_ops ++ ^create_ops``;
val local_fields = ``\u v. u.vs_halted = v.vs_halted /\
  u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb /\
  u.vs_inst_idx = v.vs_inst_idx /\ u.vs_params = v.vs_params /\
  u.vs_call_ctx = v.vs_call_ctx /\ u.vs_tx_ctx = v.vs_tx_ctx /\
  u.vs_block_ctx = v.vs_block_ctx /\ u.vs_data_section = v.vs_data_section /\
  u.vs_labels = v.vs_labels /\ u.vs_code = v.vs_code /\
  u.vs_prev_hashes = v.vs_prev_hashes /\
  u.vs_initial_fmp = v.vs_initial_fmp /\ u.vs_fmp = v.vs_fmp /\
  u.vs_allocas = v.vs_allocas /\ u.vs_alloca_next = v.vs_alloca_next /\
  u.vs_call_entry_fmp = v.vs_call_entry_fmp /\
  u.vs_return_pc_token = v.vs_return_pc_token``;

val output_data = ``
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
    ?y. FLOOKUP t1.vs_vars v = SOME y /\
      (~retpc_var fn v ==>
       fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
         (op_taint (step_taint inst s s1 tn) (Var v)) x y))``;

Theorem cut_external_output[local]:
  MEM inst.inst_opcode ^external_ops /\ inst.inst_outputs = [out] /\
  a.vs_vars = s.vs_vars /\ b.vs_vars = t.vs_vars /\
  s1 = update_var out w a /\ t1 = update_var out w b ==>
  ^output_data
Proof
  strip_tac >>
  `out_prov PG G inst s1 = NONE` by fs[MEM, out_prov_def] >>
  gvs[update_var_def, FLOOKUP_UPDATE, step_prov_def, set_prov_def,
      FLOOKUP_DRESTRICT, fmp_value_rel_def, ld_value_agree_scalar,
      word_agree_except_def]
QED

Theorem cut_call_fields[local]:
  consume_call_outcome rq p n s = (w,r) ==>
  (^local_fields) (update_var out w r) s
Proof
  simp[consume_call_outcome_eq] >> strip_tac >>
  gvs[update_var_def]
QED

val external_point = ``
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  gas_cut ncut vs s /\ taint_within_upto D ncut C vs /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  ptr_use_static_ok P (fn_pv P fn) inst /\ FDOM G SUBSET fn_pv P fn /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  eom <= fmp0 /\ fmp0 <= raw0``;

val ok_data = ``^output_data /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\ ~s1.vs_halted /\ ~t1.vs_halted /\
  (^local_fields) s1 s /\ (^local_fields) t1 t``;

Theorem cut_call_ok[local]:
  ^external_point /\ MEM inst.inst_opcode ^call_ops /\
  step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\ ^ok_data
Proof
  strip_tac >> drule_all focus_fmp_cut_call_execute >>
  disch_then (qx_choosel_then
    [`gop`,`adop`,`vop`,`offop`,`szop`,`rop`,`rsop`,`gas`,`addr`,`value`,
     `off`,`off'`,`sz`,`ro`,`ro'`,`rs`,`prefix`,`out`,`kind`,`static`,
     `rq1`,`rq2`,`w1`,`r1`,`w2`,`r2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
   ~t.vs_halted /\ s.vs_call_ctx = t.vs_call_ctx` by
    fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  drule_all cut_call_shared >> strip_tac >>
  drule_all cut_call_return_memory >> strip_tac >>
  `(MEM inst.inst_opcode [CALL;DELEGATECALL] ==>
    rq1.cr_static = s.vs_call_ctx.cc_static)` by
    fs[MEM, venom_call_request_def] >>
  drule_all cut_call_shared_after_update >> strip_tac >>
  every_drule_then assume_tac ld_consume_call_vars >>
  every_drule_then (strip_assume_tac o BETA_RULE) cut_call_fields >>
  `(update_var out w1 r1).vs_returndata = (update_var out w2 r2).vs_returndata` by
    simp[update_var_def] >>
  qpat_x_assum `w1 = w2` SUBST_ALL_TAC >>
  qexists_tac `update_var out w2 r2` >>
  conj_tac >- simp[Excl "consume_call_outcome_eq"] >>
  conj_tac
  >- (match_mp_tac (GEN_ALL cut_external_output) >>
      simp[MEM_APPEND] >> qexistsl_tac [`w2`,`r2`,`r1`] >> simp[]) >>
  simp[Excl "consume_call_outcome_eq"]
QED

val create_update = ``\s r rq. s with
  <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
    vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
    vs_pending_deletions := r.vs_pending_deletions; vs_returndata := r.vs_returndata;
    vs_requests := record_request rq s.vs_requests|>``;

Theorem cut_create_shared[local]:
  MEM inst.inst_opcode ^create_ops /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
  request_agree_except D rq rq' /\
  r = (^create_update) s r rq /\ rt = (^create_update) t r rq' ==>
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s (update_var out w r) tn)
    (update_var out w r) (update_var out w rt)
Proof
  disch_then (MAP_EVERY (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2]` by
    fs[MEM] >>
  drule (cj 1 ld_external_taint_projections) >> strip_tac >>
  drule (cj 2 ld_external_taint_projections) >> strip_tac >>
  drule (cj 3 ld_external_taint_projections) >> strip_tac >>
  `inst.inst_opcode <> CALL` by
    ((qpat_assum `MEM inst.inst_opcode ^create_ops` mp_tac >> simp[] >> (gvs[]))) >>
  simp[ld_shared_agree_def, adopt_reset_def, update_var_def] >>
  qpat_assum `rt = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  fs[ld_shared_agree_def, word_agree_except_def] >>
  irule request_agree_record_request >> simp[]
QED

Theorem cut_create_memory[local]:
  MEM inst.inst_opcode ^create_ops /\ r = (^create_update) s r rq ==>
  (step_taint inst s (update_var out w r) tn).t_mem = tn.t_mem
Proof
  disch_then (MAP_EVERY (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `new_site_bytes s (update_var out w r) = {}` by
    (irule ptrDisciplineEmptyTaintTheory.new_site_bytes_unchanged >>
     qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[update_var_def]) >>
  gvs[MEM, step_taint_def, mem_taint_def, step_writes_def, range_bytes_def,
      codegenRelTheory.source_memory_write_ranges_def, written_taint_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem cut_create_ok[local]:
  ^external_point /\ MEM inst.inst_opcode ^create_ops /\
  step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\ ^ok_data
Proof
  strip_tac >> drule_all focus_fmp_cut_create_execute >>
  disch_then (qx_choosel_then
    [`vop`,`offop`,`szop`,`value`,`off`,`off'`,`sz`,`salt`,`out`,`rq`,`rq'`,`w`,`r`,`rt`]
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
   ~t.vs_halted` by fs[fmp_stage_rel_def] >>
  `request_agree_except D rq rq'` by
    (`inst.inst_opcode <> INVOKE` by fs[MEM] >>
     `step_inst 0 C inst s = OK s1` by simp[step_inst_non_invoke] >>
     `LENGTH s.vs_requests < LENGTH s1.vs_requests` by
       (drule_all ld_create_step_request_growth >> simp[]) >>
     drule_all taint_within_upto_request >> strip_tac >>
     qpat_assum `rq = venom_create_request _ _ _ _ _` (fn th => REWRITE_TAC[th]) >>
     qpat_assum `rq' = venom_create_request _ _ _ _ _` (fn th => REWRITE_TAC[th]) >>
     irule ld_venom_create_request_masked >> simp[] >>
     metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe]) >>
  drule_all (BETA_RULE cut_create_shared) >> strip_tac >>
  drule_all (BETA_RULE cut_create_memory) >> strip_tac >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qexists_tac `update_var out w rt` >>
  conj_tac >- simp[Excl "consume_create_outcome_eq"] >>
  conj_tac
  >- (match_mp_tac (GEN_ALL cut_external_output) >>
      simp[MEM_APPEND] >> qexistsl_tac [`w`,`rt`,`r`] >>
      qpat_assum `rt = _` (fn th => once_rewrite_tac[th]) >>
      qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  simp[Excl "consume_create_outcome_eq"] >>
  qpat_assum `rt = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  simp[update_var_def, Excl "consume_create_outcome_eq"]
QED

(* The exceptional dispatch inspects only definedness and scalar operands. *)
Theorem cut_external_operands[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode ^external_ops /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      fmp_value_rel sm (op_prov G op) (op_taint tn op) x y
Proof
  strip_tac >>
  `MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI` by
    (conj_tac >- metis_tac[lowerDloadOracleCallAssemblyTheory.ld_active_inst_member] >>
     gvs[MEM_APPEND, MEM]) >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >> irule frameViewFactsTheory.ordinary_operand_not_retpc >>
     simp[] >> qexists_tac `inst` >> gvs[MEM_APPEND, MEM]) >>
  drule_all fmpStageOpBaseTheory.fmp_stage_operand_point >> simp[]
QED

Theorem cut_external_scalar_clean[local]:
  MEM inst.inst_opcode ^external_ops /\ MEM op inst.inst_operands /\
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\ taint_ok fn tn inst s /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      rename1 `MEM (Var v) inst.inst_operands` >>
      `v NOTIN pv` by
        (strip_tac >> qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
         pure_rewrite_tac[ptrStaticDisciplineTheory.ptr_use_static_ok_def] >>
         disch_then (qspec_then `v` mp_tac o CONJUNCT2) >>
         gvs[MEM_APPEND, MEM, pointerConfinedDefsTheory.is_pointer_preserving_op_def,
             Excl "FILTER"] >> metis_tac[]) >>
      fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[MEM_APPEND, MEM, taint_ok_def] >> metis_tac[]
QED

Theorem cut_call_exception[local]:
  MEM inst.inst_opcode ^call_ops /\ step_inst_base inst s = r /\
  passSimulationDefs$terminates r /\ ~(?s1. r = OK s1) ==>
  r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
  IS_SOME (eval_operands inst.inst_operands s) /\
  LENGTH inst.inst_operands = (if inst.inst_opcode = CALL then 7 else 6) /\
  ((s.vs_outcomes = [] /\ ?out. inst.inst_outputs = [out]) \/
   (inst.inst_opcode = CALL /\ s.vs_call_ctx.cc_static /\
    ?g a v off sz ro rs value.
      inst.inst_operands = [g;a;v;off;sz;ro;rs] /\
      eval_operand v s = SOME value /\ value <> 0w))
Proof
  strip_tac >> Cases_on `r` >> fs[passSimulationDefsTheory.terminates_def] >>
  TRY (drule step_inst_base_halt_opcodes >> gvs[MEM] >> NO_TAC) >>
  TRY (drule step_inst_base_intret_opcodes >> gvs[MEM] >> NO_TAC) >>
  fs[MEM] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, exec_ext_call_abort_iff,
       exec_delegatecall_abort_iff, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operands_def] >> metis_tac[]
QED

Theorem cut_external_defined[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ opaque_use_ok fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode ^external_ops /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  IS_SOME (eval_operands inst.inst_operands s) ==>
  IS_SOME (eval_operands inst.inst_operands t)
Proof
  strip_tac >> qpat_x_assum `IS_SOME (eval_operands _ _)` mp_tac >>
  pure_rewrite_tac[eval_operands_IS_SOME_EVERY, EVERY_MEM, optionTheory.IS_SOME_EXISTS] >>
  rpt strip_tac >>
  rename1 `MEM op inst.inst_operands` >>
  `?x. eval_operand op s = SOME x` by metis_tac[] >>
  drule_all cut_external_operands >> metis_tac[]
QED

Theorem cut_call_abort[local]:
  ^external_point /\ MEM inst.inst_opcode ^call_ops /\ step_inst_base inst s = r /\
  passSimulationDefs$terminates r /\ ~(?s1. r = OK s1) ==>
  r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
  step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >> drule_all cut_call_exception >>
  disch_then (map_every assume_tac o CONJUNCTS) >> simp[] >>
  `MEM inst.inst_opcode ^external_ops` by simp[MEM_APPEND] >>
  drule_all cut_external_defined >> strip_tac >>
  qpat_x_assum `(_ /\ (?out. inst.inst_outputs = [out])) \/ _` strip_assume_tac
  >- (`t.vs_outcomes = []` by
        (fs[fmp_stage_rel_def, ld_shared_agree_def] >>
         qpat_assum `s.vs_outcomes = t.vs_outcomes` (rewrite_tac o single o SYM) >>
         first_assum ACCEPT_TAC) >>
      gvs[MEM, LENGTH_EQ_NUM_compute, eval_operands_IS_SOME_EVERY,
          optionTheory.IS_SOME_EXISTS] >>
      simp[step_inst_base_opcode_eqs, exec_ext_call_def, exec_delegatecall_def,
           Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `MEM v inst.inst_operands` by simp[] >>
  `FILTER ($= v) inst.inst_operands = [v] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> v` by
    (simp[memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
          Excl "FILTER"] >>
     rpt strip_tac >> gvs[Excl "FILTER"] >>
     qpat_x_assum `FILTER _ _ = _` mp_tac >>
     simp[FILTER] >> rpt IF_CASES_TAC >> simp[]) >>
  drule_all cut_external_scalar_clean >> strip_tac >>
  `eval_operand v t = SOME value` by
    (drule_all cut_external_operands >> metis_tac[fmpStagePointRangesTheory.fmp_mem_value_clean]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `t.vs_call_ctx.cc_static` by metis_tac[] >>
  qpat_x_assum `IS_SOME (eval_operands _ t)` mp_tac >>
  simp[eval_operands_IS_SOME_EVERY, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >> simp[step_inst_base_opcode_eqs]
QED

Theorem cut_create_static_abort[local]:
  ^external_point /\ MEM inst.inst_opcode ^create_ops /\ s.vs_call_ctx.cc_static /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
  step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) /\
   r = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >> fs[MEM] >>
     simp[step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[eval_operands_def, passSimulationDefsTheory.terminates_def]) >>
  `MEM inst.inst_opcode ^external_ops` by simp[MEM_APPEND] >>
  drule_all cut_external_defined >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `t.vs_call_ctx.cc_static` by metis_tac[] >>
  gvs[MEM, step_inst_base_opcode_eqs]
QED

Theorem cut_create_nonstatic_exception[local]:
  MEM inst.inst_opcode ^create_ops /\ ~s.vs_call_ctx.cc_static /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r /\
  ~(?s1. r = OK s1) ==>
  r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
  IS_SOME (eval_operands inst.inst_operands s) /\
  ?v off sz rest size.
    eval_operand sz s = SOME size /\
    (w2n size > 2 * vfmConstants$max_code_size \/ s.vs_outcomes = []) /\
    (?out. inst.inst_outputs = [out]) /\
    inst.inst_operands = v::off::sz::rest /\
    ((inst.inst_opcode = CREATE /\ rest = []) \/
     (inst.inst_opcode = CREATE2 /\ ?salt. rest = [salt]))
Proof
  simp[MEM] >> strip_tac >>
  Cases_on `r` >> fs[passSimulationDefsTheory.terminates_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs(), exec_create_not_Halt,
       exec_create_not_IntRet, exec_create_abort_iff] >>
  rpt strip_tac >> gvs[eval_operands_def] >> metis_tac[]
QED

Theorem cut_create_nonstatic_abort[local]:
  ^external_point /\ MEM inst.inst_opcode ^create_ops /\ ~s.vs_call_ctx.cc_static /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r /\
  ~(?s1. r = OK s1) ==>
  r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
  step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >> drule_all cut_create_nonstatic_exception >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  rename1 `eval_operand sz s = SOME szval` >> simp[] >>
  `MEM inst.inst_opcode ^external_ops` by simp[MEM_APPEND] >>
  drule_all cut_external_defined >> strip_tac >>
  `MEM sz inst.inst_operands` by simp[] >>
  `FILTER ($= sz) inst.inst_operands = [sz] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> sz` by
    (qpat_x_assum `(inst.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >>
     simp[memLocDefsTheory.mem_read_ops_def, memLocDefsTheory.mem_write_ops_def,
          Excl "FILTER"] >>
     rpt strip_tac >> gvs[Excl "FILTER"] >>
     qpat_x_assum `FILTER _ _ = _` mp_tac >>
     simp[FILTER] >> rpt IF_CASES_TAC >> simp[]) >>
  drule_all cut_external_scalar_clean >> strip_tac >>
  `eval_operand sz t = SOME szval` by
    (drule_all cut_external_operands >> metis_tac[fmpStagePointRangesTheory.fmp_mem_value_clean]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[fmp_stage_rel_def, ld_shared_agree_def] >>
  `~t.vs_call_ctx.cc_static` by metis_tac[] >>
  qpat_x_assum `?out. inst.inst_outputs = [out]` strip_assume_tac >>
  qpat_x_assum `(inst.inst_opcode = CREATE /\ _) \/ _` strip_assume_tac >>
  qpat_x_assum `IS_SOME (eval_operands _ t)` mp_tac >>
  simp[eval_operands_IS_SOME_EVERY, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_create_def] >> metis_tac[]
QED

Theorem focus_fmp_cut_external_effect:
  ^external_point /\ MEM inst.inst_opcode ^external_ops /\
  step_inst_base inst s = r /\ passSimulationDefs$terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\ ^ok_data
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode ^external_ops` mp_tac >>
  pure_rewrite_tac[MEM_APPEND] >> disch_then DISJ_CASES_TAC >>
  Cases_on `?s1. r = OK s1`
  >- (qpat_x_assum `?s1. r = OK s1` (qx_choose_then `s1` SUBST_ALL_TAC) >>
      drule_all cut_call_ok >> strip_tac >> qexists_tac `OK t1` >> gvs[])
  >- (drule_all cut_call_abort >> strip_tac >>
      qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] t))` >>
      simp[dead_result_rel_def])
  >- (qpat_x_assum `?s1. r = OK s1` (qx_choose_then `s1` SUBST_ALL_TAC) >>
      drule_all cut_create_ok >> strip_tac >> qexists_tac `OK t1` >> gvs[]) >>
  `r = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
   step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (Cases_on `s.vs_call_ctx.cc_static`
     >- (drule_all cut_create_static_abort >> simp[]) >>
     drule_all cut_create_nonstatic_abort >> simp[]) >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] t))` >>
  simp[dead_result_rel_def]
QED

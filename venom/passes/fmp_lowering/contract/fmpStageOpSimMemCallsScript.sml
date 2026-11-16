(* External calls at the FMP boundary. *)
Theory fmpStageOpSimMemCalls
Ancestors
  fmpStageOpSimMemSupport fmpStageOpSimMemReads fmpStageOpBase fmpStageRel
  o1LowerDloadExternalOracle o1LowerDloadExternalEffects o1LowerDloadPrecompileEffects o1LowerDloadShared
  o1LowerDloadRangeTransport o1LowerDloadRelocationKernel o1PassContract
  ptrDiscipline ptrStaticDiscipline contextCodegenRel codegenRel unitShapeDefs passSimulationDefs
  venomExecSemantics venomCallOracleDefs extCallOracle venomState venomInst
  memLocDefs pointerConfinedDefs words finite_map pred_set list

Theorem fmp_mem_external_scalar_clean:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   (?P. EVERY (fn_static_ptr_ok P) C.ctx_functions) /\ taint_ok fn tn inst s` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
     `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def] >> metis_tac[]) >>
  simp[] >> fs[taint_ok_def] >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_external_scalar:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x /\
  (FILTER ($= op) inst.inst_operands = [op] ==>
    !ops. mem_read_ops inst = SOME ops \/ mem_write_ops inst = SOME ops ==>
      ops.iao_ofst <> op) ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[fmp_mem_external_scalar_clean] >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by
    gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_operand_clean >> simp[]
QED

Theorem fmp_mem_external_input:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    read_memory (w2n x) len s = read_memory (w2n y) len t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `inst.inst_opcode <> PHI /\ (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by metis_tac[fmp_mem_operand_non_retpc] >>
  drule_all fmp_mem_read_operand_range >> strip_tac >>
  qexists_tac `y` >> simp[] >>
  irule LIST_EQ >> simp[ld_read_memory_length] >> rpt strip_tac >>
  `w2n x+x' NOTIN tn.t_mem` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >> strip_tac >>
     qpat_x_assum `!off len i. _` (qspecl_then [`w2n x`,`len`,`w2n x+x'`] mp_tac) >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC] >> simp[]) >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`tn.t_mem`,`fmp_ld_sites sm`] >>
  gvs[fmp_stage_rel_def] >> metis_tac[]
QED

Theorem fmp_mem_external_world:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> INVOKE /\ step_inst k C inst s = OK s1 /\
  LENGTH s.vs_requests < LENGTH s1.vs_requests ==>
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient
Proof
  strip_tac >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[fmp_stage_ctx_def, o1_inv_def, o1_static_inv_def, taint_within_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe]
QED

Theorem fmp_mem_call_operands[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop]) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop])) /\
  inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
  (!op. MEM op prefix ==> ?w. eval_operand op s = SOME w) /\
  eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
  eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs ==>
  (!op x. MEM op (prefix ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
     eval_operand op t = SOME x) /\
  ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  strip_tac >> (
  conj_tac
  >- (rpt strip_tac >> irule fmp_mem_external_scalar >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >> simp[Excl "FILTER"] >>
      reverse conj_tac >- (gvs[] >> metis_tac[]) >>
      gvs[Excl "FILTER", mem_read_ops_def, mem_write_ops_def] >>
      rpt strip_tac >> gvs[Excl "FILTER"] >>
      qpat_x_assum `FILTER _ _ = _` mp_tac >>
      simp_tac (srw_ss()) [FILTER] >> rpt IF_CASES_TAC >> simp[]) >>
  `(?w. eval_operand gop s = SOME w) /\ (?w. eval_operand adop s = SOME w) /\
   (inst.inst_opcode = CALL ==> ?w. eval_operand vop s = SOME w)` by
    (gvs[] >> metis_tac[]) >>
  `?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (irule fmp_mem_external_input >> conj_tac >- simp[] >> goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     gvs[mem_read_ops_def, source_memory_read_ranges_def, memory_range_of_operands_def] >>
     `?w. eval_operand vop s = SOME w` by metis_tac[] >> simp[]) >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn rop = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `!v. rop = Var v ==> ~retpc_var fn v` by
    (`!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
     `MEM rop inst.inst_operands` by simp[] >> metis_tac[fmp_mem_operand_non_retpc]) >>
  `?ro'. eval_operand rop t = SOME ro' /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (irule fmp_mem_write_operand_range >> goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     gvs[mem_write_ops_def, source_memory_write_ranges_def,
         fixed_source_write_range_def] >>
     `?w. eval_operand vop s = SOME w` by metis_tac[] >> simp[]) >>
  gvs[] >> metis_tac[])
QED

Theorem fmp_mem_call_decode[local]:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst k C inst s = OK s1 ==>
  ?gop adop vop offop szop rop rsop gas addr value off sz ro rs static prefix.
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
    eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
    ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
      eval_operand vop s = SOME value /\ static = s.vs_call_ctx.cc_static /\
      ~(s.vs_call_ctx.cc_static /\ value <> 0w)) \/
     (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\
      value = 0w /\ static = (inst.inst_opcode = STATICCALL))) /\
    inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
    (if inst.inst_opcode = DELEGATECALL then
      exec_delegatecall inst s gas addr off sz ro rs
     else exec_ext_call inst s gas addr value off sz ro rs static) = OK s1
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_call_scalar_values[local]:
  (!op x. MEM op (prefix ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x) /\
  ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
     eval_operand vop s = SOME value) \/
   (MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\ prefix = [gop;adop] /\ value = 0w)) /\
  eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
  eval_operand szop s = SOME sz /\ eval_operand rsop s = SOME rs ==>
  eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
  eval_operand szop t = SOME sz /\ eval_operand rsop t = SOME rs /\
  (inst.inst_opcode = CALL ==> eval_operand vop t = SOME value)
Proof
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_call_observe[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> INVOKE /\ step_inst k C inst s = OK (update_var out w1 r1) /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  rq1 = (venom_call_request s addr value off sz static with cr_kind := kind) /\
  rq2 = (venom_call_request t addr value off' sz static with cr_kind := kind) /\
  consume_call_outcome rq1 ro rs s = (w1,r1) /\
  consume_call_outcome rq2 ro' rs t = (w2,r2) ==>
  w1 = w2 /\ r1.vs_returndata = r2.vs_returndata /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (tn with <|t_stor := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_stor;
               t_trans := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_trans|>) r1 r2
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
   rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data /\
   computed_precompile rq1 = computed_precompile rq2` by
    simp[venom_call_request_def, computed_precompile_def] >>
  Cases_on `computed_precompile rq1`
  >- (`computed_precompile rq2` by metis_tac[] >> `r1.vs_requests = s.vs_requests` by
        (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
         simp[consume_call_outcome_eq, record_request_def] >> strip_tac >>
         gvs[Excl "consume_call_outcome_eq"]) >>
      drule_all ld_consume_precompile_shared >> strip_tac >>
      gvs[Excl "consume_call_outcome_eq"]) >>
  `LENGTH s.vs_requests < LENGTH (update_var out w1 r1).vs_requests` by
    (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
     simp[consume_call_outcome_eq, record_request_def, update_var_def] >>
     strip_tac >> gvs[]) >>
  `accounts_agree_except D s.vs_accounts t.vs_accounts /\
   transient_agree_except D s.vs_transient t.vs_transient` by
    metis_tac[fmp_mem_external_world] >>
  `request_agree_except D rq1 rq2` by
    simp[request_agree_except_def, venom_call_request_def,
         call_request_component_equality] >>
  `s.vs_outcomes = t.vs_outcomes /\
   LIST_REL (request_agree_except D) s.vs_requests t.vs_requests` by fs[ld_shared_agree_def] >>
  drule_all ld_consume_call_outcome_masked_observation >> strip_tac >> simp[] >>
  drule_all ld_consume_call_outcome_shared_effects >> simp[]
QED

Theorem fmp_mem_call_execute[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst k C inst s = OK s1 ==>
  ?out w1 w2 r1 r2 addr value off off' sz (ro:bytes32) (ro':bytes32) (rs:bytes32) static kind rq1 rq2.
    inst.inst_outputs = [out] /\ s1 = update_var out w1 r1 /\
    step_inst k C' inst t = OK (update_var out w2 r2) /\
    rq1 = (venom_call_request s addr value off sz static with cr_kind := kind) /\
    rq2 = (venom_call_request t addr value off' sz static with cr_kind := kind) /\
    consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w1,r1) /\
    consume_call_outcome rq2 (w2n ro') (w2n rs) t = (w2,r2) /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    source_memory_write_ranges inst s = [(w2n ro,w2n rs)] /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j)) /\
    kind = (if inst.inst_opcode = DELEGATECALL then DelegateMessageCall else MessageCall) /\
    static = (if inst.inst_opcode = CALL then s.vs_call_ctx.cc_static
              else inst.inst_opcode = STATICCALL)
Proof
  strip_tac >> drule_all fmp_mem_call_decode >> strip_tac >> (
  `(!op. MEM op prefix ==> ?w. eval_operand op s = SOME w)` by (gvs[] >> metis_tac[]) >>
  `(!op x. MEM op (prefix ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
     eval_operand op t = SOME x) /\
   ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (irule fmp_mem_call_operands >> simp[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     fs[] >> metis_tac[]) >>
  `eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
   eval_operand szop t = SOME sz /\ eval_operand rsop t = SOME rs /\
   (inst.inst_opcode = CALL ==> eval_operand vop t = SOME value)` by
    (irule fmp_mem_call_scalar_values >> metis_tac[]) >>
  qpat_x_assum `!op x. _` kall_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  qabbrev_tac `kind = if inst.inst_opcode = DELEGATECALL then DelegateMessageCall else MessageCall` >>
  qabbrev_tac `rq1 = venom_call_request s addr value off sz static with cr_kind := kind` >>
  qabbrev_tac `rq2 = venom_call_request t addr value off' sz static with cr_kind := kind` >>
  Cases_on `consume_call_outcome rq1 (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq1 _ _ s = (w1,r1)` >>
  Cases_on `consume_call_outcome rq2 (w2n ro') (w2n rs) t` >>
  rename1 `consume_call_outcome rq2 _ _ t = (w2,r2)` >>
  `?out. inst.inst_outputs = [out] /\ s1 = update_var out w1 r1` by
    (gvs[Abbr `rq1`, Abbr `kind`, exec_ext_call_def, exec_delegatecall_def,
         venom_call_request_def, Excl "consume_call_outcome_eq", AllCaseEqs()] >> metis_tac[]) >>
  qexistsl_tac [`out`,`w1`,`w2`,`r1`,`r2`,`addr`,`value`,`off`,`off'`,`sz`,
                `ro`,`ro'`,`rs`,`static`,`kind`,`rq1`,`rq2`] >>
  simp[Excl "consume_call_outcome_eq", Abbr `rq1`, Abbr `rq2`] >>
  gvs[MEM, Abbr `kind`, Excl "consume_call_outcome_eq"] >>
  gvs[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_ext_call_def,
       exec_delegatecall_def, venom_call_request_def, source_memory_write_ranges_def,
       Excl "consume_call_outcome_eq"] >> metis_tac[])
QED

Theorem fmp_mem_call_return_memory[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  consume_call_outcome rq1 ro rs s = (w1,r1) /\
  consume_call_outcome rq2 ro' rs t = (w2,r2) /\
  r1.vs_returndata = r2.vs_returndata /\
  source_memory_write_ranges inst s = [(ro,rs)] /\ written_taint tn inst s = {} /\
  (rs=0 \/ (ro=ro' /\ ro+rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+rs<=z /\
                    ro=b+j /\ ro'=c+j)) ==>
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s (update_var out w1 r1) tn).t_mem
    (update_var out w1 r1).vs_memory (update_var out w2 r2).vs_memory
Proof
  strip_tac >> (
  `r1.vs_allocas = s.vs_allocas /\ r1.vs_fmp = s.vs_fmp /\
   r1.vs_memory = (write_memory_with_expansion ro (TAKE rs r1.vs_returndata) s).vs_memory` by
    (qpat_x_assum `consume_call_outcome _ _ _ s = _` mp_tac >>
     simp[consume_call_outcome_eq] >> strip_tac >> gvs[]) >>
  `r2.vs_memory = (write_memory_with_expansion ro' (TAKE rs r2.vs_returndata) t).vs_memory` by
    (qpat_x_assum `consume_call_outcome _ _ _ t = _` mp_tac >>
     simp[consume_call_outcome_eq] >> strip_tac >> gvs[]) >>
  `new_site_bytes s (update_var out w1 r1) = {}` by
    (simp[new_site_bytes_def, update_var_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by metis_tac[fmp_mem_geometry] >>
  `ld_memory_agree (fmp_ld_sites sm) eom
    (tn.t_mem DIFF {i | ro<=i /\ i<ro+MIN rs (LENGTH r2.vs_returndata)})
    (write_memory_with_expansion ro (TAKE rs r2.vs_returndata) s).vs_memory
    (write_memory_with_expansion ro' (TAKE rs r2.vs_returndata) t).vs_memory` by
    (drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_return_buffer >>
     disch_then irule >> simp[] >>
     fs[fmp_stage_rel_def, Excl "consume_call_outcome_eq"] >>
     simp[arithmeticTheory.MIN_DEF] >> rpt IF_CASES_TAC >>
     gvs[Excl "consume_call_outcome_eq"] >>
     qexists_tac `0` >> disj2_tac >> disj2_tac >> disj1_tac >>
     qexistsl_tac [`id`,`b`,`c`,`z`,`j`] >> simp[] >> decide_tac) >>
  gvs[step_taint_def, mem_taint_def, step_writes_def, range_bytes_def, update_var_def,
      Excl "consume_call_outcome_eq"])
QED

Theorem fmp_mem_call_shared[local]:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  taint_ok fn tn inst s /\
  static = (if inst.inst_opcode = CALL then s.vs_call_ctx.cc_static
            else inst.inst_opcode = STATICCALL) /\
  rq1 = (venom_call_request s addr value off sz static with cr_kind := kind) /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (tn with <|t_stor := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_stor;
               t_trans := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_trans|>) r1 r2 ==>
  ld_shared_agree D s.vs_call_ctx.cc_address
    (step_taint inst s (update_var out w1 r1) tn)
    (update_var out w1 r1) (update_var out w2 r2)
Proof
  strip_tac >> gvs[MEM] >>
  fs[taint_ok_def, step_taint_def, adopt_reset_def, store_taint_def,
     imm_taint_def, update_var_def, venom_call_request_def,
     ld_shared_agree_def, Excl "consume_call_outcome_eq"] >>
  gvs[Excl "consume_call_outcome_eq"]
QED

Theorem fmp_mem_call_clean_taint[local]:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst k C inst s = OK s1 ==>
  out_taint tn inst s = {} /\ written_taint tn inst s = {}
Proof
  strip_tac >> drule_all fmp_mem_call_decode >> strip_tac >>
  gvs[MEM, out_taint_def, written_taint_def, Excl "consume_call_outcome_eq"]
QED

Theorem fmp_mem_calls_ok[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
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
  strip_tac >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    metis_tac[fmp_mem_call_clean_taint] >>
  drule_all fmp_mem_call_execute >> strip_tac >>
  `w1 = w2 /\ r1.vs_returndata = r2.vs_returndata /\
   ld_shared_agree D s.vs_call_ctx.cc_address
    (tn with <|t_stor := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_stor;
               t_trans := if ~rq1.cr_static /\ r1.vs_requests <> s.vs_requests /\
                    r1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_trans|>) r1 r2` by
    (irule fmp_mem_call_observe >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     gvs[MEM, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
    (step_taint inst s (update_var out w1 r1) tn)
    (update_var out w1 r1) (update_var out w2 r2)` by
    (irule fmp_mem_call_shared >> metis_tac[]) >>
  `ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s (update_var out w1 r1) tn).t_mem
    (update_var out w1 r1).vs_memory (update_var out w2 r2).vs_memory` by
    (irule fmp_mem_call_return_memory >> metis_tac[]) >>
  qexists_tac `update_var out w2 r2` >>
  gvs[Excl "consume_call_outcome_eq"] >>
  `s.vs_halted = t.vs_halted` by fs[fmp_stage_rel_def] >>
  gvs[update_var_def, consume_call_outcome_eq, FLOOKUP_UPDATE] >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       op_taint_def, set_var_taint_def, fmp_value_rel_def, ld_value_agree_def,
       FLOOKUP_DRESTRICT, MEM] >>
  gvs[MEM] >> simp[word_agree_except_def]
QED

Theorem fmp_mem_call_exception[local]:
  MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst k C inst s = r /\ terminates r /\ ~(?s1. r = OK s1) ==>
  inst.inst_opcode = CALL /\
  ?gop adop vop offop szop rop rsop gas addr value off sz ro rs.
    inst.inst_operands = [gop;adop;vop;offop;szop;rop;rsop] /\
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
    eval_operand szop s = SOME sz /\ eval_operand rop s = SOME ro /\
    eval_operand rsop s = SOME rs /\
    s.vs_call_ctx.cc_static /\ value <> 0w /\
    r = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[MEM] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_ext_call_def, exec_delegatecall_def,
       Excl "consume_call_outcome_eq", AllCaseEqs()] >>
  rpt strip_tac >> gvs[terminates_def, consume_call_outcome_eq, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_mem_calls_dead[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  step_inst k C inst s = r /\ terminates r /\ ~(?s1. r = OK s1) ==>
  step_inst k C' inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)) /\
  r = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >> drule_all fmp_mem_call_exception >> strip_tac >>
  `(!op x. MEM op ([gop;adop;vop] ++ [szop;rsop]) /\ eval_operand op s = SOME x ==>
     eval_operand op t = SOME x) /\
   ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (irule fmp_mem_call_operands >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fmp_stage_ctx _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     fs[] >> metis_tac[]) >>
  `eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
   eval_operand vop t = SOME value /\ eval_operand szop t = SOME sz /\
   eval_operand rsop t = SOME rs` by (fs[] >> metis_tac[]) >>
  qpat_x_assum `!op x. _` kall_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
  gvs[Excl "consume_call_outcome_eq"] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

(* The external message-call part of the frozen call simulation. *)
Theorem fmp_mem_calls_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL] /\
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
      drule_all fmp_mem_calls_ok >> strip_tac >>
      qexistsl_tac [`k`,`OK t1`] >> simp[]) >>
  drule_all fmp_mem_calls_dead >> strip_tac >>
  qexistsl_tac [`k`,`Abort ExHalt_abort (halt_state (set_returndata [] t))`] >>
  gvs[dead_result_rel_def]
QED

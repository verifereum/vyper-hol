Theory readonlyInvokeCopyFwdExecutionExternal
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsExternalOracle readonlyInvokeCopyFwdEffects
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistoryPhase
  o1LowerDloadShared o1LowerDloadJointExternal o1LowerDloadConcreteExternal
  o1LowerDloadRelocationKernel
  internalReturnCopyFwdSim ptrDiscipline taintAgree venomCallOracleDefs extCallOracle
  venomExecSemantics venomState venomInst finite_map list pred_set words
  regularCallEmitSim

Theorem ricf_opaque_consume_call[local]:
  consume_call_outcome rq ro rs s = (w,r) ==>
  consume_call_outcome rq ro rs (ricf_opaque_view fn PG G s) =
    (w,ricf_opaque_view fn PG G r)
Proof
  simp[consume_call_outcome_eq, ricf_opaque_view_def,
    write_memory_with_expansion_def, write_memory_def] >>
  strip_tac >> gvs[]
QED



Theorem ricf_consume_call_memory[local]:
  consume_call_outcome rq ro rs s = (w,r) ==>
  r.vs_memory = (write_memory_with_expansion ro (TAKE rs r.vs_returndata) s).vs_memory /\
  r.vs_alloca_next = s.vs_alloca_next
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ricf_support_consume_call[local]:
  ricf_support_agree B E tn s t /\
  consume_call_outcome rq1 ro1 rs s = (w,r) /\
  consume_call_outcome rq2 ro2 rs t = (z,u) /\
  r.vs_returndata = u.vs_returndata /\ (rs = 0 \/ ro1 = ro2) ==>
  ricf_support_agree B E (ricf_call_taint tn rq1 s r ro1 rs) r u
Proof
  strip_tac >>
  `r.vs_memory = (write_memory_with_expansion ro1 (TAKE rs r.vs_returndata) s).vs_memory /\
   u.vs_memory = (write_memory_with_expansion ro2 (TAKE rs r.vs_returndata) t).vs_memory /\
   r.vs_alloca_next = s.vs_alloca_next` by metis_tac[ricf_consume_call_memory] >>
  Cases_on `rs = 0`
  >- (gvs[ricf_support_agree_def, ricf_call_taint_def,
        read_byte_write_memory_with_expansion] >> metis_tac[]) >>
  gvs[ricf_support_agree_def, ricf_call_taint_def,
    read_byte_write_memory_with_expansion] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem ricf_cross_consume_call_offsets[local]:
  ircf_cross tn gam s t /\
  consume_call_outcome rq1 ro1 rs s = (w,r) /\
  consume_call_outcome rq2 ro2 rs t = (z,u) /\
  r.vs_returndata = u.vs_returndata /\ (rs = 0 \/ ro1 = ro2) /\
  (!db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
    ~(ro1 <= db+k /\ db+k < ro1 + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro1 <= sb+k /\ sb+k < ro1 + LENGTH (TAKE rs r.vs_returndata))) ==>
  ircf_cross (ricf_call_taint tn rq1 s r ro1 rs) gam r u
Proof
  strip_tac >> Cases_on `rs = 0`
  >- (`r.vs_memory = (write_memory_with_expansion ro1 [] s).vs_memory /\
       u.vs_memory = (write_memory_with_expansion ro2 [] t).vs_memory` by
        metis_tac[ricf_consume_call_memory, TAKE_0] >>
      gvs[ircf_cross_def, ricf_call_taint_def,
        read_byte_write_memory_with_expansion] >> metis_tac[]) >>
  gvs[Excl "consume_call_outcome_eq"] >>
  irule (Q.INST [`rq2` |-> `rq2`, `t` |-> `t`, `w` |-> `w`, `z` |-> `z`]
    ricf_cross_consume_call) >>
  simp[Excl "consume_call_outcome_eq"] >> metis_tac[]
QED



Theorem ricf_opaque_frame_consume_call:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro rs t = (z,u) /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  w = z /\ ricf_opaque_frame_agree fn D X sites PG G
    (ricf_call_taint tn rq1 s r ro rs) r u
Proof
  strip_tac >>
  `consume_call_outcome rq1 ro rs (ricf_opaque_view fn PG G s) =
    (w,ricf_opaque_view fn PG G r) /\
   consume_call_outcome rq2 ro rs (ricf_opaque_view fn PG G t) =
    (z,ricf_opaque_view fn PG G u)` by metis_tac[ricf_opaque_consume_call] >>
  fs[ricf_opaque_frame_agree_def, Excl "consume_call_outcome_eq"] >>
  drule ricf_frame_consume_call >>
  disch_then (qspecl_then [`z`,`w`,`ricf_opaque_view fn PG G u`,`rs`,
    `rq2`,`rq1`,`ro`,`ricf_opaque_view fn PG G r`] mp_tac) >>
  simp[ricf_opaque_view_def, ricf_call_taint_def,
    Excl "consume_call_outcome_eq"] >> metis_tac[]
QED

Theorem ricf_opaque_call_request_compatible:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n ao') (w2n az) t /\
  (computed_precompile (venom_call_request s addr value ao az static) \/
   (accounts_agree_except D s.vs_accounts t.vs_accounts /\
    transient_agree_except D s.vs_transient t.vs_transient)) ==>
  ((computed_precompile (venom_call_request s addr value ao az static) /\
    computed_precompile (venom_call_request t addr value ao' az static) /\
    (venom_call_request s addr value ao az static).cr_target =
      (venom_call_request t addr value ao' az static).cr_target /\
    (venom_call_request s addr value ao az static).cr_data =
      (venom_call_request t addr value ao' az static).cr_data) \/
   request_agree_except D (venom_call_request s addr value ao az static)
     (venom_call_request t addr value ao' az static))
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def, Excl "consume_call_outcome_eq"] >>
     drule taint_agree_call_ctx >> simp[ricf_opaque_view_def]) >>
  fs[Excl "consume_call_outcome_eq"]
  >- (disj1_tac >> gvs[computed_precompile_def, venom_call_request_def]) >>
  disj2_tac >> irule ld_venom_call_request_masked >> simp[]
QED

Theorem ricf_opaque_live_stack_consume_call[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro rs s = (w,r) /\
  consume_call_outcome rq2 ro rs t = (z,u) /\
  (!j db sb sz k. j < LENGTH stk /\
    (db,sb,sz) IN ricf_site_triples (EL j maps) /\ k < sz ==>
    ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE rs r.vs_returndata)) /\
    ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE rs r.vs_returndata))) ==>
  ricf_opaque_live_stack_agree D ids (ricf_call_taint tn rq1 s r ro rs)
    maps stk targets r u
Proof
  simp[ricf_opaque_live_stack_agree_def, Excl "consume_call_outcome_eq"] >>
  strip_tac >> simp[Excl "consume_call_outcome_eq"] >> rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` (qspec_then `j` mp_tac) >>
  simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
  drule ricf_opaque_frame_consume_call >>
  disch_then (qspecl_then [`z`,`w`,`merge_callee_state (EL j targets) u`,
    `rs`,`rq2`,`rq1`,`ro`,`merge_callee_state (EL j stk).cf_state r`] mp_tac) >>
  simp[ricf_consume_call_merge, merge_callee_state_def,
    ricf_call_taint_def, Excl "consume_call_outcome_eq"] >> metis_tac[]
QED

Theorem ricf_opaque_frame_consume_call_zero:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 0 s = (w,r) /\
  consume_call_outcome rq2 ro2 0 t = (z,u) ==>
  w = z /\ ricf_opaque_frame_agree fn D X sites PG G
    (ricf_call_taint tn rq1 s r ro1 0) r u
Proof
  strip_tac >> Cases_on `consume_call_outcome rq2 ro1 0 t` >>
  `w = q /\ ricf_opaque_frame_agree fn D X sites PG G
    (ricf_call_taint tn rq1 s r ro1 0) r r'` by
    (irule ricf_opaque_frame_consume_call >>
     simp[Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  qpat_x_assum `consume_call_outcome rq2 ro1 0 t = _` mp_tac >>
  qpat_x_assum `consume_call_outcome rq2 ro2 0 t = _` mp_tac >>
  simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[] >>
  fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def, taint_agree_def,
    ld_shared_agree_def, ircf_cross_def, ricf_opaque_view_def,
    ricf_call_taint_def, read_byte_write_memory_with_expansion] >> metis_tac[]
QED

Theorem ricf_opaque_live_stack_consume_call_zero[local]:
  ricf_opaque_live_stack_agree D ids tn maps stk targets s t /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 0 s = (w,r) /\
  consume_call_outcome rq2 ro2 0 t = (z,u) ==>
  ricf_opaque_live_stack_agree D ids (ricf_call_taint tn rq1 s r ro1 0)
    maps stk targets r u
Proof
  simp[ricf_opaque_live_stack_agree_def, Excl "consume_call_outcome_eq"] >>
  strip_tac >> simp[Excl "consume_call_outcome_eq"] >> rpt strip_tac >>
  qpat_x_assum `!j. j < LENGTH stk ==> _` (qspec_then `j` mp_tac) >>
  simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
  drule ricf_opaque_frame_consume_call_zero >>
  disch_then (qspecl_then [`z`,`w`,`merge_callee_state (EL j targets) u`,
    `rq2`,`rq1`,`ro2`,`ro1`,`merge_callee_state (EL j stk).cf_state r`] mp_tac) >>
  simp[ricf_consume_call_merge, merge_callee_state_def,
    ricf_call_taint_def, Excl "consume_call_outcome_eq"] >> metis_tac[]
QED

Theorem ricf_execution_consume_call_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK (update_var out w r) /\
  (!z v. consume_call_outcome rq2 (ro') (rs) t = (z,v) ==>
    step_inst fuel Ct inst t = OK (update_var out z v)) /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  consume_call_outcome rq1 (ro) (rs) s = (w,r) /\
  (rs = 0 \/ ro = ro') /\
  step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
  step_taint inst s (update_var out w r) tn =
    (ricf_call_taint tn rq1 s r (ro) (rs)
      with t_var := set_var_taint tn.t_var [out] {}) /\
  occurrence_sites_step a B inst (update_var out w r) = B /\
  active_inst fn next ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(ro <= db+k /\ db+k < ro + LENGTH (TAKE (rs) r.vs_returndata)) /\
      ~(ro <= sb+k /\ sb+k < ro + LENGTH (TAKE (rs) r.vs_returndata))) ==>
  ?v. step_inst fuel C inst s = OK (update_var out w r) /\
    step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG
      (step_prov PG G inst (update_var out w r))
      (step_taint inst s (update_var out w r) tn) fn next
      ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst (update_var out w r))
      ledger E sites maps targets (step_taint inst s (update_var out w r) tn)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `consume_call_outcome rq2 (ro') (rs) t` >>
  rename1 `consume_call_outcome rq2 (ro') (rs) t =
    (target_result,target_state)` >>
  `w = target_result /\ ricf_opaque_frame_agree fn D
    (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G
    (ricf_call_taint tn rq1 s r (ro) (rs)) r target_state` by
    (Cases_on `rs = 0` >| [
       mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
         `PG` |-> `ricf_complete_params PG s.vs_params`,
        `rq1` |-> `rq1`, `rq2` |-> `rq2`,
        `ro1` |-> `ro`, `ro2` |-> `ro'`, `u` |-> `target_state`, `z` |-> `target_result`]
         ricf_opaque_frame_consume_call_zero) >>
       impl_tac >- (gvs[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
          metis_tac[]) >> simp[Excl "consume_call_outcome_eq"],
       gvs[Excl "consume_call_outcome_eq"] >>
       qpat_x_assum `!gam. _` (qspec_then `ricf_site_triples sites` mp_tac) >>
       simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
       mp_tac (Q.INST [`X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
         `PG` |-> `ricf_complete_params PG s.vs_params`, `ro` |-> `ro`,
         `rs` |-> `rs`, `u` |-> `target_state`, `z` |-> `target_result`,
         `rq1` |-> `rq1`,
         `rq2` |-> `rq2`]
         ricf_opaque_frame_consume_call) >>
       (impl_tac >- (simp[venom_call_request_def, Excl "consume_call_outcome_eq"] >>
         metis_tac[arithmeticTheory.ADD_COMM])) >>
       simp[Excl "consume_call_outcome_eq"]]) >>
  `r.vs_returndata = target_state.vs_returndata` by
    (fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def, Excl "consume_call_outcome_eq"] >>
     drule taint_agree_read_fields >> simp[ricf_opaque_view_def]) >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (ricf_call_taint tn rq1 s r (ro) (rs)) maps stk targets r target_state` by
    (Cases_on `rs = 0`
     >- (mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`,
           `ro1` |-> `ro`, `ro2` |-> `ro'`,
           `u` |-> `target_state`, `z` |-> `target_result`] ricf_opaque_live_stack_consume_call_zero) >>
         impl_tac >- (gvs[venom_call_request_def, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
         simp[Excl "consume_call_outcome_eq"]) >>
     mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`, `ro` |-> `ro`,
       `rs` |-> `rs`, `u` |-> `target_state`, `z` |-> `target_result`]
       ricf_opaque_live_stack_consume_call) >>
     impl_tac >- (gvs[venom_call_request_def, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `r.vs_vars = s.vs_vars /\ r.vs_params = s.vs_params /\
   r.vs_allocas = s.vs_allocas` by metis_tac[ricf_consume_call_footprint] >>
  `step_inst fuel C inst s = OK (update_var out w r) /\
   step_inst fuel Ct inst t = OK (update_var out w target_state)` by
    (gvs[Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
  `ircf_cross (ricf_call_taint tn rq1 s r (ro) (rs))
    (ricf_phase_ranges 0 ledger) r target_state` by
    (mp_tac (Q.INST [`gam` |-> `ricf_phase_ranges 0
         (ledger:(ricf_protection_event # call_frame list) list)`,
       `ro1` |-> `ro`, `ro2` |-> `ro'`, `rs` |-> `rs`,
       `u` |-> `target_state`, `z` |-> `target_result`]
       ricf_cross_consume_call_offsets) >>
     (impl_tac >- (gvs[Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `ricf_cert_crosses (ricf_call_taint tn rq1 s r (ro) (rs))
    (ricf_phase_stack_ranges stk ledger) stk r target_state` by
    (fs[ricf_cert_crosses_def, EVERY_MEM, Excl "consume_call_outcome_eq"] >>
     rpt strip_tac >>
     rename1 `MEM gam (ricf_phase_stack_ranges stk ledger)` >>
     mp_tac (Q.INST [`gam` |-> `gam`,
       `ro1` |-> `ro`, `ro2` |-> `ro'`, `rs` |-> `rs`,
       `u` |-> `target_state`, `z` |-> `target_result`]
       ricf_cross_consume_call_offsets) >>
     (impl_tac >- (gvs[Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `ricf_support_agree B E (ricf_call_taint tn rq1 s r (ro) (rs)) r target_state` by
    (mp_tac (Q.INST [`ro1` |-> `ro`, `ro2` |-> `ro'`,
       `rs` |-> `rs`, `u` |-> `target_state`, `z` |-> `target_result`]
       (INST_TYPE [alpha |-> ``:num # num``] ricf_support_consume_call)) >>
     (impl_tac >- (gvs[Excl "consume_call_outcome_eq"] >> metis_tac[])) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) (set_prov G [out] NONE)
    (ricf_call_taint tn rq1 s r (ro) (rs)
      with t_var := set_var_taint tn.t_var [out] {})
    (update_var out w r) (update_var out w target_state)` by
    (mp_tac (Q.INST [`tn` |-> `ricf_call_taint tn rq1 s r ro rs`,
       `s` |-> `r`, `t` |-> `target_state`,
       `X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`,
       `p` |-> `NONE`, `m` |-> `{}:num set`, `x` |-> `w:256 word`,
       `y` |-> `w:256 word`] ricf_opaque_frame_bind) >>
     (impl_tac >- simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
       ricf_value_agree_def, ld_value_agree_def, word_agree_except_def,
       ricf_call_taint_def]) >>
     simp[ricf_call_taint_def]) >>
  qexists_tac `update_var out w target_state` >> simp[] >>
  (mp_tac (Q.INST [`u` |-> `update_var out w r`,
    `v` |-> `update_var out w target_state`, `rt` |-> `tn`]
    ricf_execution_next) >>
  (impl_tac >- (fs[MEM, Excl "consume_call_outcome_eq"] >> simp[is_terminator_def, Excl "consume_call_outcome_eq"] >>
  (rpt conj_tac
  >- gvs[ircf_dead_def, update_var_def, Excl "consume_call_outcome_eq"]
  >- (mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`,
        `tn` |-> `ricf_call_taint tn rq1 s r ro rs`,
        `s` |-> `r`, `t` |-> `target_state`,
        `tv` |-> `set_var_taint tn.t_var [out] {}`,
        `x` |-> `w:256 word`, `y` |-> `w:256 word`]
        ricf_opaque_live_stack_update_var) >>
      simp[ricf_call_taint_def,
        Excl "consume_call_outcome_eq"])
  >- (fs[ircf_cross_def, update_var_def, Excl "consume_call_outcome_eq"] >> metis_tac[])
  >- (fs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def,
        update_var_def, Excl "consume_call_outcome_eq"] >> metis_tac[])
  >> fs[ricf_support_agree_def, update_var_def, Excl "consume_call_outcome_eq"] >>
     metis_tac[]))) >> simp[])
QED

Theorem ricf_execution_ext_call_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ MEM inst.inst_opcode [CALL;STATICCALL] /\
  inst.inst_outputs = [out] /\
  step_inst fuel C inst s = exec_ext_call inst s gas addr value ao az ro rs static /\
  step_inst fuel Ct inst t = exec_ext_call inst t gas addr value ao' az ro' rs static /\
  rq1 = venom_call_request s addr value ao az static /\
  rq2 = venom_call_request t addr value ao' az static /\
  ((computed_precompile rq1 /\ computed_precompile rq2 /\
    rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
    request_agree_except D rq1 rq2) /\
  consume_call_outcome rq1 (w2n ro) (w2n rs) s = (w,r) /\
  (w2n rs = 0 \/ ro = ro') /\
  step_prov PG G inst (update_var out w r) = set_prov G [out] NONE /\
  step_taint inst s (update_var out w r) tn =
    (ricf_call_taint tn rq1 s r (w2n ro) (w2n rs)
      with t_var := set_var_taint tn.t_var [out] {}) /\
  occurrence_sites_step a B inst (update_var out w r) = B /\
  active_inst fn next ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(w2n ro <= db+k /\ db+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata)) /\
      ~(w2n ro <= sb+k /\ sb+k < w2n ro + LENGTH (TAKE (w2n rs) r.vs_returndata))) ==>
  ?v. step_inst fuel C inst s = OK (update_var out w r) /\
    step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG
      (step_prov PG G inst (update_var out w r))
      (step_taint inst s (update_var out w r) tn) fn next
      ((update_var out w r) with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst (update_var out w r))
      ledger E sites maps targets (step_taint inst s (update_var out w r) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (update_var out w r)` by
    (qpat_assum `step_inst fuel C inst s = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_ext_call_def, LET_THM] >>
     qpat_assum `rq1 = venom_call_request _ _ _ _ _ _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `consume_call_outcome rq1 _ _ s = _` (fn th => pure_rewrite_tac[th]) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `!z v. consume_call_outcome rq2 (w2n ro') (w2n rs) t = (z,v) ==>
     step_inst fuel Ct inst t = OK (update_var out z v)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `step_inst fuel Ct inst t = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[exec_ext_call_def, LET_THM] >>
     qpat_assum `rq2 = venom_call_request _ _ _ _ _ _`
       (fn th => pure_rewrite_tac[GSYM th]) >>
     qpat_assum `consume_call_outcome rq2 _ _ t = _` (fn th => pure_rewrite_tac[th]) >>
     simp[Excl "consume_call_outcome_eq"]) >>
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient` by
    (qpat_assum `rq1 = venom_call_request _ _ _ _ _ _` (fn th => rewrite_tac[th]) >>
     qpat_assum `rq2 = venom_call_request _ _ _ _ _ _` (fn th => rewrite_tac[th]) >>
     simp[venom_call_request_def]) >>
  qabbrev_tac `source_off = w2n ro` >>
  qabbrev_tac `target_off = w2n ro'` >>
  qabbrev_tac `output_size = w2n rs` >>
  mp_tac (Q.INST [`ro` |-> `source_off`, `ro'` |-> `target_off`,
    `rs` |-> `output_size`] ricf_execution_consume_call_next) >>
  (impl_tac >- (gvs[Abbr `source_off`, Abbr `target_off`, Abbr `output_size`,
    MEM, is_terminator_def, Excl "consume_call_outcome_eq"] >> metis_tac[])) >> simp[]
QED

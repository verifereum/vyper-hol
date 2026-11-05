(* External family integration: masked oracle and concrete EVM boundaries. *)
Theory o1LowerDloadJointExternal
Ancestors
  o1LowerDloadJointExternalUpdate o1LowerDloadConcreteExternal
  o1LowerDloadExternalEffects o1LowerDloadExternalOracle o1LowerDloadPrecompileEffects
  o1LowerDloadJointRangeRead o1LowerDloadJointRangeCopy
  o1LowerDloadJointRelation o1LowerDloadShared o1PassContract
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
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (fs[o1_src_inv_def, taint_within_def] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def] >>
  metis_tac[ld_shared_accounts_observe, ld_shared_transient_observe]
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
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (qpat_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
  `?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))` by
    (drule ld_joint_read_operand_range >> disch_then irule >> metis_tac[]) >>
  `!k. k<len ==> w2n x+k NOTIN tn.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x+k /\ w2n x+k < w2n x+len` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >>
     rpt disch_tac >> disj2_tac >> qexistsl_tac [`w2n x`,`len`,`w2n x+k`] >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `y` >> simp[] >> irule ld_memory_agree_clean_slice >>
  qexistsl_tac [`lo`,`tn.t_mem`,`sites`] >> simp[] >>
  gvs[ld_joint_boundary_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_joint_concrete_shared_inputs:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [DELEGATECALL;CREATE;CREATE2] ==>
  tn.t_stor = {} /\ tn.t_trans = {} /\
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by
    (fs[taint_ok_def, MEM] >> metis_tac[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def] >>
  metis_tac[ld_shared_clean_accounts, ld_shared_clean_transient]
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
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  strip_tac >>
  `!op. MEM op [gop;adop;szop;rsop] ==>
     op_prov H op = NONE /\ op_taint tn op = {}` by
    (gen_tac >> disch_tac >>
     drule ld_joint_external_scalar_clean >> disch_then irule >>
     simp[Excl "FILTER"] >> reverse conj_tac >- metis_tac[MEM] >>
     gvs[Excl "FILTER", MEM, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[FILTER, SF boolSimps.COND_elim_ss]) >>
  `!op. MEM op [gop;adop;szop;rsop] ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_joint_operand_clean >>
     `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  `?off'. eval_operand offop t = SOME off' /\
     read_memory (w2n off) (w2n sz) s =
       read_memory (w2n off') (w2n sz) t` by
    (drule ld_joint_external_input_slice >> disch_then irule >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn rop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> metis_tac[MEM]) >>
  `?ro'. eval_operand rop t = SOME ro' /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (drule ld_joint_write_operand_range >> disch_then irule >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, retpc_use_ok_def]) >>
  qexistsl_tac [`off'`,`ro'`] >> gvs[] >> metis_tac[MEM]
QED

Theorem ld_joint_delegatecall_execute:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DELEGATECALL /\ step_inst fuel C inst s = OK s1 ==>
  ?out w r ro ro' rs.
    inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    r = s with <|
      vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_memory := (write_memory_with_expansion ro
        (TAKE rs r.vs_returndata) s).vs_memory |> /\
    step_inst fuel C' inst t = OK (update_var out w (t with <|
      vs_returndata := r.vs_returndata;
      vs_accounts := r.vs_accounts; vs_logs := r.vs_logs;
      vs_transient := r.vs_transient;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_memory := (write_memory_with_expansion ro'
        (TAKE rs r.vs_returndata) t).vs_memory |>)) /\
    source_memory_write_ranges inst s = [(ro,rs)] /\
    (rs=0 \/ (ro=ro' /\ ro+rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+rs<=z /\
                    ro=b+j /\ ro'=c+j))
Proof
  rpt gen_tac >> disch_then strip_assume_tac >>
  `?dg da di dz dr dn dgval daval dival dzval drval dnval.
     inst.inst_operands = [dg;da;di;dz;dr;dn] /\
     eval_operand dg s = SOME dgval /\ eval_operand da s = SOME daval /\
     eval_operand di s = SOME dival /\ eval_operand dz s = SOME dzval /\
     eval_operand dr s = SOME drval /\ eval_operand dn s = SOME dnval /\
     exec_delegatecall inst s dgval daval dival dzval drval dnval = OK s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  drule_all ld_joint_delegatecall_operands >>
  disch_then (qx_choose_then `di_target` (qx_choose_then `dr_target` assume_tac)) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    (drule ld_joint_concrete_shared_inputs >> simp[]) >>
  `ld_joint_local_fields s t` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  `s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[ld_joint_boundary_def, ld_shared_agree_def] >>
  drule_all (INST_TYPE [``:'h`` |-> ``:256``] ld_exec_delegatecall_transport) >>
  disch_then (qspec_then `dr_target:bytes32` mp_tac) >>
  disch_then (qx_choose_then `dc_out`
    (qx_choose_then `dc_word` (qx_choose_then `dc_state` assume_tac))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_then assume_tac ld_extract_concrete_shape >>
  qexistsl_tac [`dc_out`,`dc_word`,`dc_state`,`w2n drval`,`w2n dr_target`,`w2n dnval`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `dc_state = _` kall_tac >> conj_tac
  >- (simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs]) >>
  conj_tac
  >- simp[source_memory_write_ranges_def, fixed_source_write_range_def] >>
  first_assum ACCEPT_TAC
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
  strip_tac >> drule_all ld_joint_delegatecall_execute >>
  disch_then (qx_choose_then `out` (qx_choose_then `w`
    (qx_choose_then `r` (qx_choose_then `ro` (qx_choose_then `rq`
      (qx_choose_then `rs` assume_tac)))))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qmatch_asmsub_abbrev_tac `step_inst fuel C' inst t = OK target` >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    fs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def]) >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     gvs[out_taint_def, written_taint_def]) >>
  `ld_env_agree sites fn (occurrence_step a HP H inst s1)
     (step_taint inst s s1 tn) s1 target` by
    suspend "environment" >>
  `new_site_bytes s s1 = {}` by
    (simp[new_site_bytes_def, update_var_def] >>
     qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
     simp[FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  `ld_joint_geometry sites X lo (a::MAP (\x. x.of_owner) U)` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  `ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
      s1.vs_memory target.vs_memory` by
    suspend "memory" >>
  `ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
     s1 target` by
    suspend "shared" >>
  qexists_tac `target` >> simp[] >>
  irule ld_joint_external_update_next >>
  qpat_assum `s1 = _` (fn th => rewrite_tac[GSYM th]) >> simp[] >>
  conj_tac >- simp[Abbr `target`, update_var_def] >>
  conj_tac
  >- (qexistsl_tac [`r.vs_accounts`,`s.vs_vars |+ (out,w)`,`r.vs_logs`,
         `r.vs_memory`,`s.vs_outcomes`,`r.vs_pending_deletions`,
         `r.vs_returndata`,`s.vs_requests`,`r.vs_transient`] >>
      simp[update_var_def] >>
      qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
      simp[venom_state_fupdcanon, venom_state_component_equality]) >>
  conj_tac
  >- (simp[Abbr `target`, update_var_def, venom_state_component_equality]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[]
QED

Resume ld_joint_delegatecall_next[environment]:
  irule ld_env_external_clean_update >> simp[] >>
  conj_tac >- simp[occurrence_out_def, out_prov_def] >>
  qexistsl_tac [`t`,`w`] >> simp[Abbr `target`, update_var_def] >>
  conj_tac
  >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  metis_tac[ld_joint_environment]
QED

Resume ld_joint_delegatecall_next[memory]:
  simp[step_taint_def, mem_taint_def, step_writes_def,
       range_bytes_def, update_var_def, Abbr `target`] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_return_buffer >>
  disch_then irule >> simp[] >> conj_tac
  >- (qpat_x_assum `rs = 0 \/ _` strip_assume_tac
      >- simp[]
      >- (disj2_tac >> disj1_tac >> simp[] >>
          simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`id`,`b`,`c`,`z`,`j`] >> simp[] >>
      simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  fs[ld_joint_boundary_def, ld_joint_frame_def] >> metis_tac[]
QED

Resume ld_joint_delegatecall_next[shared]:
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def] >>
  simp[ld_shared_agree_def, step_taint_def, imm_taint_def,
       update_var_def, Abbr `target`, word_agree_except_def] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  fs[ld_shared_agree_def, word_agree_except_def]
QED

Finalise ld_joint_delegatecall_next

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
  strip_tac >>
  `?vop offop szop value off sz salt rest.
     eval_operand vop s = SOME value /\ eval_operand offop s = SOME off /\
     eval_operand szop s = SOME sz /\
     ((inst.inst_opcode = CREATE /\ inst.inst_operands = [vop;offop;szop] /\
       rest = [] /\ salt = NONE) \/
      (inst.inst_opcode = CREATE2 /\ ?sop sw.
       inst.inst_operands = [vop;offop;szop;sop] /\ rest = [sop] /\
       eval_operand sop s = SOME sw /\ salt = SOME sw)) /\
     exec_create inst s value off sz salt = OK s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `~s.vs_call_ctx.cc_static` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[eval_operands_def] >>
     Cases_on `s.vs_call_ctx.cc_static` >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `~t.vs_call_ctx.cc_static` by metis_tac[] >>
  `(!op. MEM op (vop::szop::rest) ==> eval_operand op s = eval_operand op t) /\
   ?off'. eval_operand offop t = SOME off' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (drule ld_joint_create_operands >> disch_then irule >> metis_tac[]) >>
  `s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient` by
    (drule ld_joint_concrete_shared_inputs >> simp[]) >>
  `s.vs_outcomes = t.vs_outcomes /\ s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[ld_joint_boundary_def, ld_shared_agree_def] >>
  `venom_create_request t value off' sz salt =
   venom_create_request s value off sz salt` by simp[venom_create_request_def] >>
  drule_at (Pat `exec_create _ _ _ _ _ _ = _`) ld_exec_create_transport >>
  disch_then (qspecl_then [`t`,`venom_create_request s value off sz salt`,`off'`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `co` (qx_choose_then `cw`
    (qx_choose_then `cr` assume_tac))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qexistsl_tac [`co`,`cw`,`cr`,`venom_create_request s value off sz salt`] >>
  (simp[] >> conj_tac
   >- simp[venom_create_request_def, computed_precompile_def] >>
   conj_tac
   >- (simp[step_inst_non_invoke] >>
       asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
       `eval_operand vop t = SOME value /\ eval_operand szop t = SOME sz` by
         metis_tac[MEM] >>
       gvs[] >> metis_tac[MEM]) >>
   simp[request_agree_except_def, accounts_agree_except_def,
        transient_agree_except_def, storage_agree_except_def, word_agree_except_def])
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
  strip_tac >> drule_all ld_joint_create_execute >>
  disch_then (qx_choose_then `out` (qx_choose_then `w`
    (qx_choose_then `r` (qx_choose_then `rq` assume_tac)))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qmatch_asmsub_abbrev_tac `step_inst fuel C' inst t = OK target` >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    fs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[MEM, is_terminator_def] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >>
     gvs[MEM, occurrence_sites_step_def]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     gvs[MEM, occurrence_sites_step_def]) >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     gvs[out_taint_def, written_taint_def]) >>
  `ld_env_agree sites fn (occurrence_step a HP H inst s1)
     (step_taint inst s s1 tn) s1 target` by suspend "environment" >>
  `new_site_bytes s s1 = {}` by
    (simp[new_site_bytes_def, update_var_def] >>
     qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
     simp[FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  `ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
      s1.vs_memory target.vs_memory` by suspend "memory" >>
  `ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
     s1 target` by suspend "shared" >>
  qexists_tac `target` >> simp[] >>
  irule ld_joint_external_update_next >>
  qpat_assum `s1 = _` (fn th => rewrite_tac[GSYM th]) >> simp[] >>
  conj_tac >- gvs[MEM] >>
  conj_tac >- simp[Abbr `target`, update_var_def] >>
  conj_tac
  >- (qexistsl_tac [`r.vs_accounts`,`s.vs_vars |+ (out,w)`,`r.vs_logs`,
         `s.vs_memory`,`r.vs_outcomes`,`r.vs_pending_deletions`,
         `r.vs_returndata`,`record_request rq s.vs_requests`,`r.vs_transient`] >>
      simp[update_var_def] >>
      qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
      simp[venom_state_fupdcanon, venom_state_component_equality]) >>
  conj_tac
  >- simp[Abbr `target`, update_var_def, venom_state_component_equality] >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[]
QED

Resume ld_joint_create_next[environment]:
  irule ld_env_external_clean_update >> simp[] >>
  conj_tac >- gvs[MEM, occurrence_out_def, out_prov_def] >>
  qexistsl_tac [`t`,`w`] >> simp[Abbr `target`, update_var_def] >>
  conj_tac
  >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  metis_tac[ld_joint_environment]
QED

Resume ld_joint_create_next[memory]:
  `source_memory_write_ranges inst s = []` by
    gvs[MEM, source_memory_write_ranges_def] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       range_bytes_def, update_var_def, Abbr `target`] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  fs[ld_joint_boundary_def, ld_joint_frame_def]
QED

Resume ld_joint_create_next[shared]:
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
    fs[ld_joint_boundary_def] >>
  simp[ld_shared_agree_def, step_taint_def, imm_taint_def,
       update_var_def, Abbr `target`, word_agree_except_def] >>
  qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
  fs[ld_shared_agree_def, word_agree_except_def] >>
  simp[record_request_def, LIST_REL_APPEND]
QED

Finalise ld_joint_create_next

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
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  strip_tac >> (
  `!op. MEM op (prefix ++ [szop;rsop]) ==>
     op_prov H op = NONE /\ op_taint tn op = {}` by
    (gen_tac >> disch_tac >>
     drule ld_joint_external_scalar_clean >> disch_then irule >>
     gvs[Excl "FILTER", MEM, mem_read_ops_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[Excl "FILTER"] >>
     qpat_x_assum `FILTER _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [FILTER] >>
     rpt IF_CASES_TAC >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ld_joint_operand_clean >>
      `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
      metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM, MEM_APPEND]) >>
  `?off'. eval_operand offop t = SOME off' /\
     read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t` by
    (drule ld_joint_external_input_slice >> disch_then irule >>
     gvs[mem_read_ops_def, source_memory_read_ranges_def,
         memory_range_of_operands_def] >>
     `(?w. eval_operand gop s = SOME w) /\
      (?w. eval_operand adop s = SOME w)` by metis_tac[] >>
     simp[] >>
     qpat_x_assum `!op. _ ==> ?w. eval_operand op s = SOME w`
       (qspec_then `vop` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn rop = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `?ro'. eval_operand rop t = SOME ro' /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (drule ld_joint_write_operand_range >> disch_then irule >>
     gvs[mem_write_ops_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, retpc_use_ok_def] >>
     `(?w. eval_operand gop s = SOME w) /\
      (?w. eval_operand adop s = SOME w)` by metis_tac[] >>
     simp[] >>
     qpat_x_assum `!op. _ ==> ?w. eval_operand op s = SOME w`
       (qspec_then `vop` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
  qexistsl_tac [`off'`,`ro'`] >> gvs[] >> metis_tac[])
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
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j)) /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
      s1 (update_var out w r2)
Proof
  strip_tac >>
  `?gop adop vop offop szop rop rsop gas addr value off sz ro rs static prefix.
    eval_operand gop s = SOME gas /\ eval_operand adop s = SOME addr /\
    eval_operand offop s = SOME off /\ eval_operand szop s = SOME sz /\
    eval_operand rop s = SOME ro /\ eval_operand rsop s = SOME rs /\
    ((inst.inst_opcode = CALL /\ prefix = [gop;adop;vop] /\
      eval_operand vop s = SOME value /\ static = s.vs_call_ctx.cc_static) \/
     (inst.inst_opcode = STATICCALL /\ prefix = [gop;adop] /\ value = 0w /\ static = T)) /\
    inst.inst_operands = prefix ++ [offop;szop;rop;rsop] /\
    exec_ext_call inst s gas addr value off sz ro rs static = OK s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  `inst.inst_opcode = CALL ==> ~(s.vs_call_ctx.cc_static /\ value <> 0w)` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[eval_operands_def] >>
     Cases_on `s.vs_call_ctx.cc_static /\ value <> 0w` >> gvs[]) >>
  `(!op. MEM op (prefix ++ [szop;rsop]) ==> eval_operand op s = eval_operand op t) /\
   ?off' ro'. eval_operand offop t = SOME off' /\ eval_operand rop t = SOME ro' /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))` by
    (drule ld_joint_call_operands >> disch_then irule >> gvs[MEM] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  qabbrev_tac `rq1 = venom_call_request s addr value off sz static` >>
  qabbrev_tac `rq2 = venom_call_request t addr value off' sz static` >>
  `rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
   rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
   rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data /\
   computed_precompile rq1 = computed_precompile rq2` by
    simp[Abbr `rq1`, Abbr `rq2`, venom_call_request_def, computed_precompile_def] >>
  Cases_on `consume_call_outcome rq1 (w2n ro) (w2n rs) s` >>
  rename1 `consume_call_outcome rq1 _ _ s = (w1,r1)` >>
  `?out. inst.inst_outputs = [out] /\ s1 = update_var out w1 r1` by
    (fs[Abbr `rq1`, exec_ext_call_def,
        Excl "consume_call_outcome_eq", AllCaseEqs()] >> metis_tac[]) >>
  (Cases_on `consume_call_outcome rq2 (w2n ro') (w2n rs) t` >>
   rename1 `consume_call_outcome rq2 _ _ t = (w2,r2)` >>
   `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by
     fs[ld_joint_boundary_def] >>
   SUBGOAL_THEN
     ``((computed_precompile rq1 /\ computed_precompile rq2 /\
      rq1.cr_target = rq2.cr_target /\ rq1.cr_data = rq2.cr_data) \/
     request_agree_except D rq1 rq2)`` assume_tac
   >- (Cases_on `computed_precompile rq1` >- metis_tac[] >>
      disj2_tac >>
      `LENGTH s.vs_requests < LENGTH s1.vs_requests` by
        (qpat_x_assum `consume_call_outcome rq1 _ _ s = _` mp_tac >>
         simp[consume_call_outcome_eq] >> strip_tac >>
         gvs[update_var_def, record_request_def]) >>
      `accounts_agree_except D s.vs_accounts t.vs_accounts /\
       transient_agree_except D s.vs_transient t.vs_transient` by
        (drule ld_joint_call_shared_observation >> disch_then irule >>
         gvs[Excl "consume_call_outcome_eq", MEM] >>
         qexistsl_tac [`fuel`,`update_var out w1 r1`] >>
         simp[Excl "consume_call_outcome_eq", update_var_def]) >>
      simp[Abbr `rq1`, Abbr `rq2`] >>
      irule ld_venom_call_request_masked >> simp[]) >>
   drule_all ld_call_outcome_effects >> strip_tac >>
   qexistsl_tac [`out`,`w1`,`r1`,`r2`,`rq1`,`rq2`,`ro`,`rs`,`ro'`] >>
   simp[Excl "consume_call_outcome_eq"] >>
   conj_tac
   >- (`eval_operand gop t = SOME gas /\ eval_operand adop t = SOME addr /\
        eval_operand szop t = SOME sz /\ eval_operand rsop t = SOME rs` by
         (gvs[MEM, Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
       gvs[MEM, Excl "consume_call_outcome_eq"] >>
       simp[step_inst_non_invoke, Excl "consume_call_outcome_eq"] >>
       asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, Excl "consume_call_outcome_eq"] >>
       simp[exec_ext_call_def, Abbr `rq2`, Excl "consume_call_outcome_eq"]) >>
   conj_tac
   >- (gvs[Excl "consume_call_outcome_eq", source_memory_write_ranges_def] >> metis_tac[]) >>
   conj_tac >- (gvs[Excl "consume_call_outcome_eq"] >> metis_tac[]) >>
   gvs[Excl "consume_call_outcome_eq", ld_shared_agree_def,
       step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       update_var_def, Abbr `rq1`] >>
   gvs[venom_call_request_def, Excl "consume_call_outcome_eq"])
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
    (w2n rs=0 \/ (w2n ro=w2n ro' /\ w2n ro+w2n rs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n rs<=z /\
                    w2n ro=b+j /\ w2n ro'=c+j))
Proof
  strip_tac >> drule_all ld_joint_call_execute_effects >>
  metis_tac[]
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
  strip_tac >> drule_all ld_joint_call_execute_effects >>
  disch_then (qx_choose_then `out` (qx_choose_then `w`
    (qx_choose_then `r1` (qx_choose_then `r2` (qx_choose_then `rq1`
      (qx_choose_then `rq2` (qx_choose_then `ro` (qx_choose_then `rs`
        (qx_choose_then `ro'` assume_tac))))))))) >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  qpat_assum `consume_call_outcome _ _ _ s = _`
    (mp_tac o MATCH_MP ld_consume_call_shape) >>
  disch_then assume_tac >>
  qpat_assum `consume_call_outcome _ _ _ t = _`
    (mp_tac o MATCH_MP ld_consume_call_shape) >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `step_inst fuel C' inst t = OK target` >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    fs[ld_joint_boundary_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[MEM, is_terminator_def, Excl "consume_call_outcome_eq"] >>
  `occ_frame_reachable vs C stk PG (step_prov PG G inst s1)
     (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP
     (occurrence_step a HP H inst s1)` by
    (drule_all occ_frame_reachable_next >>
     gvs[MEM, occurrence_sites_step_def, Excl "consume_call_outcome_eq"]) >>
  `occurrence_annotation_ok n a U B HP (occurrence_step a HP H inst s1)
     stk PG (step_prov PG G inst s1) (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     gvs[MEM, occurrence_sites_step_def, Excl "consume_call_outcome_eq"]) >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     gvs[MEM, Excl "consume_call_outcome_eq"] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     simp[out_taint_def, written_taint_def, Excl "consume_call_outcome_eq"]) >>
  `ld_env_agree sites fn (occurrence_step a HP H inst s1)
     (step_taint inst s s1 tn) s1 target` by suspend "environment" >>
  `ld_joint_geometry sites X lo (a::MAP (\x. x.of_owner) U)` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  `ld_memory_agree sites lo (step_taint inst s s1 tn).t_mem
      s1.vs_memory target.vs_memory` by suspend "memory" >>
  `ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn)
     s1 target` by suspend "shared" >>
  qexists_tac `target` >> simp[Excl "consume_call_outcome_eq"] >>
  irule ld_joint_external_update_next >>
  qpat_assum `s1 = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[Excl "consume_call_outcome_eq"] >>
  conj_tac >- gvs[MEM, Excl "consume_call_outcome_eq"] >>
  conj_tac >- simp[Abbr `target`, update_var_def, Excl "consume_call_outcome_eq"] >>
  conj_tac
  >- (qexistsl_tac [`r1.vs_accounts`,`s.vs_vars |+ (out,w)`,`r1.vs_logs`,
         `r1.vs_memory`,`r1.vs_outcomes`,`r1.vs_pending_deletions`,
         `r1.vs_returndata`,`r1.vs_requests`,`r1.vs_transient`] >>
      simp[update_var_def, Excl "consume_call_outcome_eq"] >>
      qpat_x_assum `r1 = _` (fn th => once_rewrite_tac[th]) >>
      simp[venom_state_fupdcanon, venom_state_component_equality]) >>
  conj_tac
  >- (simp[Abbr `target`, update_var_def, Excl "consume_call_outcome_eq"] >>
      qpat_x_assum `r2 = _` (fn th => once_rewrite_tac[th]) >>
      simp[venom_state_fupdcanon, venom_state_component_equality]) >>
  qexistsl_tac [`G`,`H`,`tn`] >> simp[Excl "consume_call_outcome_eq"]
QED

Resume ld_joint_call_next[environment]:
  irule ld_env_external_clean_update >> simp[Excl "consume_call_outcome_eq"] >>
  conj_tac >- gvs[MEM, occurrence_out_def, out_prov_def, Excl "consume_call_outcome_eq"] >>
  qexistsl_tac [`t`,`w`] >> simp[Abbr `target`, update_var_def, Excl "consume_call_outcome_eq"] >>
  conj_tac
  >- (qpat_x_assum `r2 = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
      qpat_x_assum `r1 = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `r2 = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  metis_tac[ld_joint_environment]
QED

Resume ld_joint_call_next[memory]:
  SUBGOAL_THEN ``inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = DELEGATECALL`` assume_tac
  >- gvs[MEM, Excl "consume_call_outcome_eq"] >>
  `new_site_bytes s s1 = {}` by
    (simp[new_site_bytes_def, update_var_def, Excl "consume_call_outcome_eq"] >>
     qpat_x_assum `r1 = _` (fn th => once_rewrite_tac[th]) >>
     simp[FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       range_bytes_def, update_var_def, Abbr `target`,
       Excl "consume_call_outcome_eq"] >>
  qpat_x_assum `r1 = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `r2 = _` (fn th => once_rewrite_tac[th]) >>
  simp[] >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_return_buffer >>
  disch_then irule >> simp[] >> conj_tac
  >- (qpat_x_assum `w2n rs = 0 \/ _` strip_assume_tac
      >- gvs[Excl "consume_call_outcome_eq"]
      >- (disj2_tac >> disj1_tac >>
          gvs[Excl "consume_call_outcome_eq"] >>
          simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`id`,`b`,`c`,`z`,`j`] >> simp[] >>
      simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  fs[ld_joint_boundary_def, ld_joint_frame_def, Excl "consume_call_outcome_eq"] >>
  metis_tac[]
QED

Resume ld_joint_call_next[shared]:
  simp[Abbr `target`, Excl "consume_call_outcome_eq"]
QED

Finalise ld_joint_call_next

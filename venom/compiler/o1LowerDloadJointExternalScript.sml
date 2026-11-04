(* External family integration: masked oracle and concrete EVM boundaries. *)
Theory o1LowerDloadJointExternal
Ancestors
  o1LowerDloadJointExternalUpdate o1LowerDloadConcreteExternal
  o1LowerDloadExternalEffects o1LowerDloadExternalOracle
  o1LowerDloadJointRangeRead o1LowerDloadJointRangeCopy
  o1LowerDloadJointRelation o1LowerDloadShared o1PassContract
  o1LowerDloadOccurrence o1LowerDloadJointScalar o1LowerDloadOpaque
  o1LowerDloadEnvironment pointerConfinedDefs finite_map memLocDefs
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
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_def] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[o1LowerDloadGhostTheory.frame_reachable_prov_support] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def,
           o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
     metis_tac[]) >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def] >> metis_tac[]) >>
  `op_prov H op = NONE` by
    (`occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
       fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
     drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     Cases_on `op_prov H op` >> simp[occurrence_param_ok_def]) >>
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

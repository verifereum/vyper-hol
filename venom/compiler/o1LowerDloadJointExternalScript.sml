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
  venomState list pred_set venomInst unitShapeDefs contextCodegenRel

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

(* Scalar arguments cannot occupy either memory-address position. *)
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

(* Request observations survive discarded revert-forward intervals. *)
Theory o1LowerDloadRequestForward
Ancestors
  o1LowerDloadForwardAbort o1LowerDloadForwardInversion
  o1LowerDloadRunnerEndpoints o1LowerDloadShared o1LowerDloadJointRelation
  venomExecSemantics venomExecProps venomState venomInst contextCodegenRel
  ptrDiscipline list o1LowerDloadOccurrence unitShapeDefs venomWf lowerDloadDefs
  lowerDloadSupplyProofs o1ContractLowerDload o1PassContract

Theorem assign_suffix_abort_requests:
  !n s j bb fuel ctx reason t.
    j = s.vs_inst_idx + n /\
    (?inst. get_instruction bb j = SOME inst /\
            inst.inst_opcode = REVERT) /\
    (!k inst. s.vs_inst_idx <= k /\ k < j /\
              get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) /\
    exec_block fuel ctx bb s = Abort reason t ==>
    t.vs_requests = s.vs_requests
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def, step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by
    (first_x_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  qpat_x_assum `update_var _ _ _ = _` (SUBST_ALL_TAC o SYM) >>
  first_x_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  simp[update_var_def, arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >>
  gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >>
  qpat_x_assum `!k inst. _` (qspec_then `k` mp_tac) >>
  simp[] >> disch_then irule >> decide_tac
QED

Theorem copy_assign_suffix_abort_requests:
  s.vs_inst_idx < j /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dst;src;sz] /\
  (?ri. get_instruction bb j = SOME ri /\ ri.inst_opcode = REVERT) /\
  (!k ii. s.vs_inst_idx < k /\ k < j /\
          get_instruction bb k = SOME ii ==> ii.inst_opcode = ASSIGN) /\
  exec_block fuel ctx bb s = Abort reason t ==>
  t.vs_requests = s.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  gvs[] >>
  drule_at (Pat `exec_block _ _ _ _ = _`) assign_suffix_abort_requests >>
  disch_then (qspecl_then [`j - SUC s.vs_inst_idx`,`j`] mp_tac) >>
  simp[write_memory_with_expansion_def, write_memory_def] >>
  disch_then irule >> rpt strip_tac >>
  first_x_assum irule >> qexists_tac `k` >> simp[] >> decide_tac
QED

Theorem ld_forward_fetch_abort_requests:
  revert_forward_pair bb s.vs_inst_idx j /\
  (!k. k <= j - s.vs_inst_idx ==>
    get_instruction bb (s.vs_inst_idx+k) =
    get_instruction bb' (t.vs_inst_idx+k)) /\
  exec_block fuel ctx bb' t = Abort reason t1 ==>
  t1.vs_requests = t.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair _ _ _` mp_tac >>
  pure_rewrite_tac[revert_forward_pair_def] >> strip_tac >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME copy` >>
  rename1 `get_instruction bb j = SOME rev` >>
  `get_instruction bb' t.vs_inst_idx = SOME copy` by
    (qpat_assum `!k. k <= _ ==> get_instruction _ _ = get_instruction _ _` (qspec_then `0` assume_tac) >> gvs[]) >>
  `get_instruction bb' (t.vs_inst_idx + (j - s.vs_inst_idx)) = SOME rev` by
    (qpat_assum `!k. k <= _ ==> get_instruction _ _ = get_instruction _ _`
      (qspec_then `j - s.vs_inst_idx` assume_tac) >> gvs[]) >>
  drule_at (Pat `exec_block _ _ _ _ = _`) copy_assign_suffix_abort_requests >>
  disch_then irule >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `t.vs_inst_idx + (j - s.vs_inst_idx)` >>
  simp[] >> rpt strip_tac >>
  `k - t.vs_inst_idx <= j - s.vs_inst_idx` by decide_tac >>
  qpat_x_assum `!k. k <= _ ==> get_instruction _ _ = get_instruction _ _`
    (qspec_then `k - t.vs_inst_idx` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum irule >>
  qexists_tac `s.vs_inst_idx + (k - t.vs_inst_idx)` >> simp[] >> decide_tac
QED

Theorem ld_joint_forward_abort_requests:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?fn' bb' t1. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = Abort reason t1 /\
    LIST_REL (request_agree_except D) s1.vs_requests t1.vs_requests
Proof
  strip_tac >> drule_all ld_joint_forward_abort >> strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> strip_tac >>
     drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_assum `active_inst _ _ _` mp_tac >>
     simp[NoAsms, active_inst_def] >> strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> simp[]) >> gvs[get_instruction_def]) >>
  `?j. revert_forward_pair bb s.vs_inst_idx j` by
    (qpat_x_assum `in_revert_forward _ _`
       (strip_assume_tac o REWRITE_RULE [in_revert_forward_def, revert_forward_at_def]) >>
     gvs[] >- metis_tac[] >>
     qpat_x_assum `revert_forward_pair _ _ _`
       (strip_assume_tac o REWRITE_RULE [revert_forward_pair_def]) >> gvs[]) >>
  `s1.vs_requests = s.vs_requests` by
    (irule ld_forward_fetch_abort_requests >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn''.fn_blocks)` by
    (qhdtm_assum `ld_joint_control`
      (strip_assume_tac o REWRITE_RULE [ld_joint_control_def]) >>
     drule lower_dload_function_supply_labels >> simp[fn_labels_def]) >>
  `fn'' = fn'` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  drule_all ld_joint_control_forward_fetch >> strip_tac >>
  `bb'' = bb'` by metis_tac[optionTheory.SOME_11] >> gvs[] >>
  `t1.vs_requests = t.vs_requests` by
    (irule ld_forward_fetch_abort_requests >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  fs[ld_shared_agree_def]
QED

Theorem ld_runner_forward_endpoint_requests:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  exec_block fuel C bb s = r /\ terminates r ==>
  ?fn' bb' reason s1 t1. r = Abort reason s1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    exec_block fuel C' bb' t = Abort reason t1 /\
    LIST_REL (request_agree_except D) s1.vs_requests t1.vs_requests
Proof
  strip_tac >>
  `revert_forward_at bb s.vs_inst_idx` by fs[in_revert_forward_def] >>
  drule_all revert_forward_at_terminates_abort >> strip_tac >> gvs[] >>
  drule_all ld_joint_forward_abort_requests >> metis_tac[]
QED

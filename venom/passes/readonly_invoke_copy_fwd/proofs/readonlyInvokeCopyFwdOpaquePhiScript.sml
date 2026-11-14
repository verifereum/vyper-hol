Theory readonlyInvokeCopyFwdOpaquePhi
Ancestors
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdValues
  unitShapeDefs venomWf venomWfProps execEquivParamBase
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdRel
  contextCodegenRel venomExecProofs internalReturnCopyFwdSim taintAgree
  frameRel ptrDiscipline o1LowerDloadShared venomExecSemantics venomState venomInst finite_map list

Theorem ricf_retpc_phi_source[local]:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  MEM (Var x) inst.inst_operands ==>
  (retpc_var fn out <=> retpc_var fn x)
Proof
  strip_tac >> eq_tac
  >- (strip_tac >> fs[retpc_shape_ok_def] >>
      qpat_x_assum `!i v. MEM i (fn_insts fn) /\ MEM v i.inst_outputs /\
        retpc_var fn v ==> _` (qspecl_then [`inst`,`out`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[retpc_var_def] >> strip_tac >>
  irule copy_phi_var_phi >> metis_tac[MEM]
QED

Theorem ricf_retpc_view_one_phi[local]:
  retpc_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = PHI /\ phi_well_formed inst.inst_operands ==>
  eval_one_phi (ricf_retpc_view fn s) inst =
    OPTION_MAP (\(out,v). (out,if retpc_var fn out then 0w else v))
      (eval_one_phi s inst)
Proof
  strip_tac >> Cases_on `inst.inst_outputs` >>
  simp[eval_one_phi_def] >> Cases_on `t` >> simp[] >>
  Cases_on `s.vs_prev_bb` >>
  simp[ricf_retpc_view_def, frame_view_def] >>
  rename1 `s.vs_prev_bb = SOME prev` >>
  Cases_on `resolve_phi prev inst.inst_operands` >> simp[] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME val_op` >>
  `?x. val_op = Var x` by metis_tac[resolve_phi_well_formed] >> gvs[] >>
  `retpc_var fn h <=> retpc_var fn x` by
    (irule ricf_retpc_phi_source >> metis_tac[resolve_phi_MEM]) >>
  simp[eval_operand_def, lookup_var_def, FLOOKUP_FMAP_MAP2] >>
  Cases_on `FLOOKUP s.vs_vars x` >> simp[]
QED

Theorem ricf_retpc_view_phis:
  !ins s s1.
    retpc_shape_ok fn /\
    EVERY (\inst. MEM inst (fn_insts fn) /\
      (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands)) ins ==>
    (eval_phis (ricf_retpc_view fn s) ins = OK s1 <=>
     ?s0. eval_phis s ins = OK s0 /\ s1 = ricf_retpc_view fn s0)
Proof
  Induct >- (simp[eval_phis_def] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (fs[] >> simp[eval_phis_def] >>
  drule_all ricf_retpc_view_one_phi >> strip_tac >>
  Cases_on `eval_one_phi s h` >> simp[] >>
  rename1 `eval_one_phi s h = SOME pair` >> PairCases_on `pair` >> simp[] >>
  `!z. eval_phis (ricf_retpc_view fn s) ins = OK z <=>
       ?s0. eval_phis s ins = OK s0 /\ z = ricf_retpc_view fn s0` by
    metis_tac[] >>
  Cases_on `eval_phis s ins` >>
  Cases_on `eval_phis (ricf_retpc_view fn s) ins` >>
  gvs[ricf_retpc_view_update_var] >> metis_tac[]) >>
  simp[eval_phis_def] >> metis_tac[]
QED

Theorem ricf_opaque_frame_phis[local]:
  retpc_shape_ok fn /\
  EVERY (\inst. MEM inst (fn_insts fn) /\
    (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands)) ins /\
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  eval_phis s ins = OK s1 ==>
  ?t1. eval_phis t ins = OK t1 /\
    ricf_opaque_frame_agree fn D X sites PG (phis_prov s.vs_prev_bb G ins)
      (tn with t_var := phis_taint s.vs_prev_bb tn ins) s1 t1
Proof
  qid_spec_tac `G` >> qid_spec_tac `tn` >> qid_spec_tac `s1` >>
  qid_spec_tac `t` >> qid_spec_tac `s` >> Induct_on `ins`
  >- (rpt gen_tac >> strip_tac >> qexists_tac `t` >>
      gvs[eval_phis_def, phis_prov_def, phis_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (qpat_x_assum `eval_phis s (h::ins) = _` mp_tac >>
      simp[Once eval_phis_def, AllCaseEqs()] >> strip_tac >>
      gvs[eval_one_phi_def, AllCaseEqs()] >>
      `?x. val_op = Var x` by metis_tac[resolve_phi_well_formed] >> gvs[] >>
      `retpc_var fn out <=> retpc_var fn x` by
        (irule ricf_retpc_phi_source >> metis_tac[resolve_phi_MEM]) >>
      `?v'. eval_operand (Var x) t = SOME v' /\
        ricf_opaque_value_agree sites (op_prov G (Var x))
          (op_taint tn (Var x))
          (if retpc_var fn out then 0w else v)
          (if retpc_var fn out then 0w else v')` by
        (drule_all ricf_opaque_frame_operand_masked >>
         simp[ricf_retpc_operand_def]) >>
      `s.vs_prev_bb = t.vs_prev_bb` by
        (fs[ricf_opaque_frame_agree_def] >>
         drule ricf_frame_agree_normalized >>
         disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
         disch_then (mp_tac o Q.AP_TERM `\u. u.vs_prev_bb`) >>
         simp[ricf_opaque_view_def]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `update_var out v' t1` >>
      simp[Once eval_phis_def, eval_one_phi_def] >>
      simp[phis_taint_def, phi_taint_def, phis_prov_def, phi_prov_def] >>
      drule_all ricf_opaque_frame_bind >> gvs[]) >>
  gvs[eval_phis_def, phis_taint_def, phis_prov_def] >>
  fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def,
     ricf_opaque_view_def, taint_agree_def, ld_shared_agree_def,
     op_taint_def, ircf_cross_def]

QED

Theorem ricf_opaque_frame_enters_block[local]:
  retpc_shape_ok fn /\ fn_inst_wf fn /\
  ricf_opaque_frame_agree fn D X sites PG G0 tn0 s t /\
  enters_block fn s s1 ==>
  ?t1. enters_block fn t t1 /\
    ricf_opaque_frame_agree fn D X sites PG (entry_prov fn s G0)
      (entry_taint_vars fn s tn0) s1 t1
Proof
  strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    (fs[ricf_opaque_frame_agree_def] >>
     drule ricf_frame_agree_normalized >>
     disch_then (mp_tac o MATCH_MP taint_agree_frame) >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_current_bb`) >>
     simp[ricf_opaque_view_def]) >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `EVERY (\inst. MEM inst (fn_insts fn) /\
     (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands))
     bb.bb_instructions` by
    (simp[EVERY_MEM] >> qx_gen_tac `inst` >> strip_tac >>
     `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     conj_tac
     >- (simp[fn_insts_def] >> metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
     `inst_wf inst` by metis_tac[fn_inst_wf_def] >> strip_tac >> gvs[inst_wf_def]) >>
  drule_all ricf_opaque_frame_phis >> strip_tac >>
  qexists_tac `t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac
  >- (simp[enters_block_def] >> metis_tac[]) >>
  gvs[entry_prov_def, entry_taint_vars_def] >>
  irule ricf_opaque_frame_inst_idx >> simp[]
QED

Theorem ricf_opaque_live_support_enters_block:
  retpc_shape_ok fn /\ fn_inst_wf fn /\
  ricf_opaque_frame_agree fn D X sites PG G0 tn0 s t /\
  enters_block fn s s1 /\
  ricf_opaque_live_stack_agree D ids tn0 maps stk targets s t /\
  ircf_cross tn0 cur s t /\ ricf_cert_crosses tn0 curs stk s t /\
  ricf_support_agree B E tn0 s t ==>
  ?t1. enters_block fn t t1 /\
    ricf_opaque_frame_agree fn D X sites PG (entry_prov fn s G0)
      (entry_taint_vars fn s tn0) s1 t1 /\
    ricf_opaque_live_stack_agree D ids (entry_taint_vars fn s tn0)
      maps stk targets s1 t1 /\
    ircf_cross (entry_taint_vars fn s tn0) cur s1 t1 /\
    ricf_cert_crosses (entry_taint_vars fn s tn0) curs stk s1 t1 /\
    ricf_support_agree B E (entry_taint_vars fn s tn0) s1 t1
Proof
  strip_tac >> drule_all ricf_opaque_frame_enters_block >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  qpat_x_assum `enters_block fn s s1` mp_tac >>
  qpat_x_assum `enters_block fn t t1` mp_tac >>
  simp[enters_block_def] >> rpt strip_tac >>
  qpat_assum `eval_phis s _ = _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `eval_phis t _ = _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >>
  gvs[entry_taint_vars_def] >>
  rpt conj_tac
  >- (fs[ricf_opaque_live_stack_agree_def] >> gvs[merge_callee_state_def])
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >> gvs[ricf_support_agree_def]
QED

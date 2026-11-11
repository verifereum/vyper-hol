(* Whole call-entry assembly for related argument vectors. *)
Theory o1LowerDloadJointCall
Ancestors
  o1LowerDloadJointEntry o1LowerDloadJointRelation o1LowerDloadOccurrence
  o1LowerDloadShared o1LowerDloadEnvironment o1ContractLowerDload
  lowerDloadDefs venomExecSemantics venomExecProofs contextCodegenRel venomState venomInst
  finite_map list pred_set

Theorem ld_call_entry_unchanged[local]:
  cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0 /\ enters_block fn cs s1 ==>
  s1 = cs
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all eval_phis_no_prev >> strip_tac >> gvs[]
QED

Theorem ld_call_entry_transport[local]:
  s.vs_prev_bb = NONE /\ t.vs_prev_bb = NONE /\
  t.vs_inst_idx = 0 /\ s.vs_current_bb = t.vs_current_bb /\
  enters_block fn s s1 ==> enters_block fn t t
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all eval_phis_no_prev >> strip_tac >>
  qexistsl_tac [`bb`, `t`] >> simp[] >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]
QED

Theorem ld_call_lookup_name[local]:
  !fns nm callee. lookup_function nm fns = SOME callee ==> callee.fn_name = nm
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  Cases_on `h.fn_name = nm` >> gvs[lookup_function_def]
QED

Theorem ld_joint_boundary_call:
  ld_joint_boundary vs C C' lo D stk PG G tn caller callinst s t
    n a U B HP H sites X ts /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  ir_supply_covers_fn uc callee /\
  lower_dload_function_supply uc callee = (callee',uc') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
  eval_operands ops s = SOME args /\ eval_operands ops t = SOME args' /\
  LENGTH args = LENGTH ops /\ LENGTH args' = LENGTH args /\
  (!k. k < LENGTH ops ==> ld_value_agree sites (op_prov H (EL k ops)) {}
    (EL k args) (EL k args')) /\
  setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ?ct t1. setup_callee callee' args' t = SOME ct /\
    enters_block callee' ct t1 /\
    s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    t1.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
    ld_joint_boundary vs C C' lo D
      (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1 t1
      (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
      B (MAP (op_prov H) ops) FEMPTY sites X (t::ts)
Proof
  strip_tac >>
  `cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  `s1 = cs` by (irule ld_call_entry_unchanged >> simp[] >> metis_tac[]) >>
  drule_all ld_supply_successful_entry >> strip_tac >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  `~NULL callee.fn_blocks /\ ~NULL callee'.fn_blocks` by
    (gvs[setup_callee_def, AllCaseEqs(), fn_labels_def] >>
     Cases_on `callee.fn_blocks` >> Cases_on `callee'.fn_blocks` >> gvs[]) >>
  `?ct. setup_callee callee' args' t = SOME ct` by simp[setup_callee_def] >>
  `cs.vs_current_bb = ct.vs_current_bb /\ ct.vs_prev_bb = NONE /\
   ct.vs_inst_idx = 0` by
    (qpat_assum `fn_labels callee' = _` mp_tac >>
     gvs[setup_callee_def, fn_labels_def] >>
     Cases_on `callee.fn_blocks` >> Cases_on `callee'.fn_blocks` >> gvs[]) >>
  `enters_block callee' ct ct` by
    (irule ld_call_entry_transport >> simp[] >>
     qexistsl_tac [`cs`, `s1`] >> simp[]) >>
  qexistsl_tac [`ct`, `ct`] >> simp[] >>
  `s1.vs_call_ctx = s.vs_call_ctx /\ ct.vs_call_ctx = t.vs_call_ctx` by
    gvs[setup_callee_def] >>
  gvs[] >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  `~MEM n (a::MAP (\x. x.of_owner) U)` by
    (fs[occurrence_annotation_ok_def, EVERY_MEM] >>
     strip_tac >> first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `(!aid. FLOOKUP sites (n,aid) = NONE) /\
   (!did. FLOOKUP X (n,did) = NONE)` by
    (conj_tac >> qx_gen_tac `key` >>
     fs[ld_joint_geometry_def, FLOOKUP_DEF] >>
     qpat_x_assum `!id. id IN FDOM sites \/ id IN FDOM X ==> _`
       (qspec_then `(n,key)` mp_tac) >> simp[]) >>
  simp[ld_joint_boundary_def] >> rpt conj_tac
  >- suspend "source"
  >- suspend "annotation"
  >- suspend "geometry"
  >- suspend "frame"
  >- suspend "saved"
  >- suspend "memory"
  >- suspend "shared"
  >> suspend "returndata"
QED

Resume ld_joint_boundary_call[source]:
  irule occ_frame_reachable_call >>
  goal_assum (drule_at (Pat `occ_frame_reachable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  metis_tac[]
QED

Resume ld_joint_boundary_call[annotation]:
  drule_all (INST_TYPE [alpha |-> ``:string``] occurrence_annotation_call) >>
  disch_then (qspecl_then [`tn.t_var`, `ops`, `caller`, `callinst`] mp_tac) >>
  simp[]
QED
Resume ld_joint_boundary_call[geometry]:
  fs[ld_joint_geometry_def] >> rpt strip_tac >> simp[] >> metis_tac[]
QED
Resume ld_joint_boundary_call[frame]:
  `callee.fn_name = nm` by
    metis_tac[ld_call_lookup_name] >>
  qexistsl_tac [`uc`, `callee'`] >> simp[] >>
  simp[ld_joint_frame_def] >> rpt conj_tac
  >- gvs[setup_callee_def, ld_env_agree_def]
  >- gvs[setup_callee_def, ld_params_agree_def, EL_MAP]
  >- (fs[ld_joint_frame_def, ld_joint_local_fields_def] >>
      gvs[setup_callee_def])
  >- (gvs[ld_joint_control_def] >> metis_tac[])
  >- gvs[setup_callee_def, ld_joint_allocas_def]
  >> (`!id. id IN FDOM X ==> FST id <> n` by
        (fs[ld_joint_geometry_def] >> metis_tac[]) >>
      `{id | id IN FDOM X /\ MEM (FST id) (n::a::MAP (\x. x.of_owner) U)} =
       {id | id IN FDOM X /\ MEM (FST id) (a::MAP (\x. x.of_owner) U)}` by
        (simp[EXTENSION] >> metis_tac[]) >>
      fs[ld_joint_frame_def] >> gvs[setup_callee_def])
QED
Resume ld_joint_boundary_call[saved]:
  simp[ld_joint_saved_def] >> metis_tac[]
QED
Resume ld_joint_boundary_call[memory]:
  gvs[setup_callee_def]
QED
Resume ld_joint_boundary_call[shared]:
  gvs[setup_callee_def, ld_shared_agree_def]
QED
Resume ld_joint_boundary_call[returndata]:
  gvs[setup_callee_def]
QED
Finalise ld_joint_boundary_call

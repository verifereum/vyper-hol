(* Shared observational effects of the checked encoder prefix. *)
Theory revertReasonPrefixFramePtr
Ancestors revertReasonPrefixPtr ghostObservationPtr decoderGhostFramePtr
  fragGasSeqPtr revertReasonLayout context venomInst venomExecSemantics venomState finite_map

Theorem inst_seq_ptr_other_output_frame:
  !is D lo ctx func PG G tn s Gf tnf x.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. ~MEM x i.inst_outputs) is ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_prov_other_output, step_taint_other_output]
QED

Theorem inst_seq_ptr_nonmemory_taint_frame:
  !is D lo ctx func PG G tn s Gf tnf.
    inst_seq_ptr D lo ctx func PG G tn is s Gf tnf /\
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
      i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) is ==>
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[] >> first_x_assum drule >>
  simp[step_taint_nonmemory_frame]
QED

Theorem revert_reason_prefix_ghost_observations:
  inst_seq_ptr D lo ctx func PG G tn (revert_reason_prefix id vn ms) s Gf tnf ==>
  (!x. (!k. k < 3 ==> x <> STRING #"%" (toString (vn+k))) ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  tnf.t_imm = tn.t_imm
Proof
  strip_tac >> conj_tac >-
    (gen_tac >> disch_tac >> irule inst_seq_ptr_other_output_frame >>
     goal_assum (drule_at Any) >>
     simp[revert_reason_prefix_def, mk_inst_def] >>
     qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  irule inst_seq_ptr_nonmemory_taint_frame >>
  goal_assum (drule_at Any) >>
  simp[revert_reason_prefix_def, mk_inst_def]
QED

Theorem alloca_store_add_data_frame:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t \/
  step_inst_base (mk_inst id MSTORE [Var out; Lit value] []) s = OK t \/
  step_inst_base (mk_inst id ADD [left; right] [out]) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >- metis_tac[alloca_step_data_frame] >-
    (fs[step_inst_base_def, mk_inst_def, exec_write2_def, AllCaseEqs()] >>
     gvs[mstore_def]) >>
  fs[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem revert_reason_prefix_data_frame:
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx
Proof
  simp[revert_reason_prefix_def] >> strip_tac >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  metis_tac[alloca_store_add_data_frame]
QED

Theorem alloca_store_add_lookup_frame:
  x <> out /\
  (step_inst_base (mk_inst id ALLOCA [Lit sz] [out]) s = OK t \/
   step_inst_base (mk_inst id MSTORE [Var dst; Lit value] []) s = OK t \/
   step_inst_base (mk_inst id ADD [left; right] [out]) s = OK t) ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >-
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, exec_alloca_def] >>
     Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >-
       (strip_tac >> gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     PairCases_on `x'` >> simp[] >> strip_tac >>
     gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >-
    (fs[step_inst_base_def, mk_inst_def, exec_write2_def, AllCaseEqs()] >>
     gvs[lookup_var_def, mstore_def]) >>
  fs[step_inst_base_def, mk_inst_def, exec_pure2_def, AllCaseEqs()] >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem revert_reason_prefix_lookup_frame:
  run_inst_seq (revert_reason_prefix id vn ms) s = OK t /\
  (!k. k < 3 ==> x <> STRING #"%" (toString (vn+k))) ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >>
  `x <> STRING #"%" (toString vn) /\
   x <> STRING #"%" (toString (vn+1)) /\
   x <> STRING #"%" (toString (vn+2))` by
    (qpat_x_assum `!k. _` mp_tac >>
     disch_then (fn th => map_every (fn k => qspec_then k assume_tac th)
       [`0`, `1`, `2`]) >> gvs[arithmeticTheory.ADD_COMM]) >>
  fs[revert_reason_prefix_def] >>
  drule run_inst_seq_four_endpoint >> strip_tac >>
  metis_tac[alloca_store_add_lookup_frame]
QED

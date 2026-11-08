Theory augAssignPtrScalarFrame
Ancestors augAssignPtrScalarRun augAssignPtrScalarExec augAssignPtrScalarCertificate
  augAssignPtrLoad bodyPtrDefs emitHelperProps venomExecSemantics venomState
  venomInst finite_map pred_set list stateFrame

Theorem scalar_step_concrete_frame:
  scalar_shape i /\ step_inst_base i s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. ~MEM x i.inst_outputs ==>
     FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> Cases_on `i.inst_opcode = ASSIGN`
  >- (gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def,
          LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(), update_var_def,
          FLOOKUP_UPDATE, venom_state_component_equality] >>
      rpt strip_tac >> qpat_x_assum `_ |+ _ = _` (SUBST1_TAC o SYM) >>
      simp[FLOOKUP_UPDATE]) >>
  irule step_pure_opcode_frame >> simp[] >>
  gvs[scalar_shape_def, scalar_binary_def, scalar_unary_def]
QED

Theorem scalar_code_shapes:
  !code A. scalar_code A code ==> EVERY scalar_shape code
Proof
  Induct >> simp[scalar_code_def] >> metis_tac[]
QED

Theorem scalar_seq_concrete_frame:
  scalar_code A code /\ run_inst_seq code s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. ~MEM x (FLAT (MAP (\i. i.inst_outputs) code)) ==>
     FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> ho_match_mp_tac run_inst_seq_protected_frame >>
  qexists `code` >> simp[] >> rpt strip_tac >>
  `scalar_shape i` by (drule scalar_code_shapes >> simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all scalar_step_concrete_frame >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem scalar_seq_ghost_inv:
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
  run_inst_seq code s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
       ~MEM x (FLAT (MAP (\i. i.inst_outputs) code))) ==>
  ghost_inv d cenv cx es H tm t
Proof
  strip_tac >> drule_all scalar_seq_concrete_frame >> strip_tac >>
  drule_all scalar_seq_metadata_frame >> strip_tac >>
  irule ghost_inv_load_frame >> qexistsl [`G`, `s`, `sa`, `tn`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def] >> metis_tac[]) >>
  qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]
QED

Theorem scalar_seq_ghost_kept:
  scalar_code A code /\
  (!v. v IN A ==> op_prov G (Var v) = NONE /\ op_taint tn (Var v) = {}) /\
  inst_seq_ptr D 0 ctx fn PG G tn code s H tm /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
       ~MEM x (FLAT (MAP (\i. i.inst_outputs) code))) ==>
  ghost_kept cenv es sa G0 tn0 s0 H tm
Proof
  strip_tac >> drule_all scalar_seq_metadata_frame >> strip_tac >>
  gvs[ghost_kept_def] >> metis_tac[]
QED

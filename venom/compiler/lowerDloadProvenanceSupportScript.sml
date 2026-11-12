Theory lowerDloadProvenanceSupport
Ancestors
  lowerDloadOwnership irSupply fmpStepSupply pointerConfinedProps ptrDiscipline o1PassContract
  finite_map pred_set list option pointerConfinedDefs venomInst
  execEquivParamBase venomExecProps contextCodegenRel ctxLookupAgreeHelpers

Theorem ld_ptr_roots_finite[local]:
  FINITE (ptr_roots P fn)
Proof
  irule SUBSET_FINITE >>
  qexists_tac `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  simp[] >>
  simp[SUBSET_DEF, ptr_roots_def, alloca_roots_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> gvs[inst_output_def, AllCaseEqs()] >> metis_tac[MEM]
QED

Theorem ld_ptr_root_support[local]:
  v IN ptr_roots P fn ==> v IN fn_pv P fn
Proof
  simp[fn_pv_def, pointer_derived_vars_def] >> strip_tac >>
  irule pointer_use_vars_initial >> simp[MEM_SET_TO_LIST, ld_ptr_roots_finite]
QED

Theorem ld_ptr_output_support[local]:
  MEM i (fn_insts fn) /\ is_pointer_preserving_op i.inst_opcode /\
  MEM (Var u) i.inst_operands /\ u IN fn_pv P fn /\ MEM v i.inst_outputs ==>
  v IN fn_pv P fn
Proof
  simp[fn_pv_def, pointer_derived_vars_def, fn_insts_def, fn_insts_blocks_MEM] >>
  rpt strip_tac >> irule pointer_use_vars_closed >> metis_tac[]
QED

Theorem ld_op_support[local]:
  FDOM AG SUBSET pv /\ ld_op_prov AG op <> NONE ==>
  ?v. op = Var v /\ v IN pv
Proof
  Cases_on `op` >> simp[ld_op_prov_def] >>
  metis_tac[FLOOKUP_DEF, SUBSET_DEF, option_CASES]
QED

Theorem ld_first_support[local]:
  FDOM AG SUBSET pv /\ ld_first_prov AG ops <> NONE ==>
  ?v. MEM (Var v) ops /\ v IN pv
Proof
  Induct_on `ops` >> simp[ld_first_prov_def] >> rpt strip_tac >>
  Cases_on `ld_op_prov AG h` >> gvs[]
  >- (qexists_tac `v` >> simp[]) >>
  `ld_op_prov AG h <> NONE` by simp[] >>
  drule_all ld_op_support >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_set_support[local]:
  FDOM AG SUBSET pv /\ (p <> NONE ==> !v. outs = [v] ==> v IN pv) ==>
  FDOM (ld_set_prov AG outs p) SUBSET pv
Proof
  simp[ld_set_prov_def] >>
  Cases_on `outs` >- simp[SUBSET_DEF, FDOM_DRESTRICT] >>
  Cases_on `t` >> Cases_on `p` >> simp[SUBSET_DEF, FDOM_DRESTRICT] >> metis_tac[]
QED

Theorem ld_step_prov_support:
  MEM i (fn_insts fn) /\ FDOM AG SUBSET fn_pv P fn /\
  (!j. j < LENGTH AP /\ EL j AP <> NONE ==> j IN P fn.fn_name) ==>
  FDOM (ld_step_prov AP AG L i) SUBSET fn_pv P fn
Proof
  strip_tac >> simp[ld_step_prov_def] >> irule ld_set_support >>
  simp[] >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (irule ld_ptr_root_support >> simp[ptr_roots_def, alloca_roots_def] >>
      disj1_tac >> disj1_tac >> qexists_tac `i` >> simp[inst_output_def]) >>
  Cases_on `i.inst_opcode = PARAM`
  >- (Cases_on `i.inst_operands` >> gvs[ld_out_prov_def] >>
      Cases_on `t` >> gvs[] >> Cases_on `h` >> gvs[] >>
      rename1 `i.inst_operands = [Lit idx]` >>
      irule ld_ptr_root_support >> simp[ptr_roots_def] >>
      disj2_tac >> qexistsl_tac [`i`, `idx`] >>
      simp[inst_output_def] >> metis_tac[]) >>
  `?u. MEM (Var u) i.inst_operands /\ u IN fn_pv P fn` by
    (irule ld_first_support >> qexists_tac `AG` >>
     gvs[ld_out_prov_def, AllCaseEqs()]) >>
  irule ld_ptr_output_support >> qexistsl_tac [`i`, `u`] >>
  gvs[ld_out_prov_def, is_pointer_preserving_op_def, AllCaseEqs()]
QED

Theorem ld_phi_support[local]:
  MEM i (fn_insts fn) /\ i.inst_opcode = PHI /\
  FDOM AG SUBSET fn_pv P fn /\ ld_phi_prov prev AG i <> NONE /\
  i.inst_outputs = [v] ==> v IN fn_pv P fn
Proof
  strip_tac >> Cases_on `prev` >> gvs[ld_phi_prov_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> gvs[] >>
  drule_all ld_op_support >> strip_tac >> gvs[] >>
  irule ld_ptr_output_support >> qexistsl_tac [`i`, `v'`] >>
  simp[is_pointer_preserving_op_def] >> metis_tac[resolve_phi_MEM]
QED

Theorem ld_phis_prov_support:
  set ins SUBSET set (fn_insts fn) /\ FDOM AG SUBSET fn_pv P fn ==>
  FDOM (ld_phis_prov prev AG ins) SUBSET fn_pv P fn
Proof
  Induct_on `ins` >- simp[ld_phis_prov_def] >>
  rpt strip_tac >> simp[ld_phis_prov_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  `FDOM (ld_phis_prov prev AG ins) SUBSET fn_pv P fn` by
    (first_x_assum irule >> fs[SUBSET_DEF]) >>
  irule ld_set_support >> simp[] >>
  rpt strip_tac >> irule ld_phi_support >>
  qexistsl_tac [`AG`, `h`, `prev`] >> fs[SUBSET_DEF]
QED

Theorem ld_entry_prov_support:
  FDOM AG SUBSET fn_pv P fn ==>
  FDOM (ld_entry_prov fn s AG) SUBSET fn_pv P fn
Proof
  strip_tac >> simp[ld_entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule ld_phis_prov_support >> simp[] >>
  drule lookup_block_MEM >>
  simp[SUBSET_DEF, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem ld_invoke_prov_support:
  fn_ptr_ok P fn /\ MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (nm,args) /\ FDOM AG SUBSET fn_pv P fn ==>
  !j. j < LENGTH args /\ EL j (MAP (ld_op_prov AG) args) <> NONE ==>
      j IN P nm
Proof
  strip_tac >> rpt strip_tac >>
  `ld_op_prov AG (EL j args) <> NONE` by metis_tac[EL_MAP] >>
  drule_all ld_op_support >> strip_tac >>
  `ptr_use_ok P (fn_pv P fn) i` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
  simp[ptr_use_ok_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_active_inst_member[local]:
  active_inst fn i s ==> MEM i (fn_insts fn)
Proof
  simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[EL_MEM]
QED

Theorem ld_annotated_prov_support_all[local]:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) ==>
  MEM fn ctx.ctx_functions /\ FDOM AG SUBSET fn_pv P fn /\
  (!j. j < LENGTH AP /\ EL j AP <> NONE ==> j IN P fn.fn_name) /\
  EVERY (\f. MEM f.lf_fn ctx.ctx_functions /\
             FDOM f.lf_prov SUBSET fn_pv P f.lf_fn /\
             (!j. j < LENGTH f.lf_params /\ EL j f.lf_params <> NONE ==>
                  j IN P f.lf_fn.fn_name)) astk
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_annotated_prov_support_all[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
  drule lookup_function_MEM >> simp[]
QED
Resume ld_annotated_prov_support_all[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[] >> irule ld_step_prov_support >> simp[] >>
  metis_tac[ld_active_inst_member]
QED
Resume ld_annotated_prov_support_all[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[] >> irule ld_entry_prov_support >> simp[]
QED
Resume ld_annotated_prov_support_all[call]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  `fn'.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  simp[] >> conj_tac >- metis_tac[lookup_function_MEM] >>
  `fn_ptr_ok P fn` by metis_tac[] >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  rpt strip_tac >> drule_all ld_invoke_prov_support >> simp[]
QED
Resume ld_annotated_prov_support_all[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  gvs[] >> fs[FDOM_DRESTRICT, SUBSET_DEF]
QED
Finalise ld_annotated_prov_support_all

Theorem ld_annotated_prov_support:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  FDOM AG SUBSET fn_pv P fn
Proof
  strip_tac >> drule ld_annotated_prov_support_all >> simp[]
QED

Theorem ld_annotated_scalar_prov:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s /\
  (!v. op = Var v ==> v NOTIN fn_pv P fn) ==>
  ld_op_prov AG op = NONE
Proof
  strip_tac >> drule_all ld_annotated_prov_support >> strip_tac >>
  Cases_on `ld_op_prov AG op = NONE` >> simp[] >>
  drule_all ld_op_support >> metis_tac[]
QED

Theorem ld_annotated_fn_member:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  MEM fn ctx.ctx_functions
Proof
  strip_tac >> drule ld_annotated_prov_support_all >>
  disch_then (qspec_then `P` mp_tac) >> simp[]
QED

Theorem ld_annotated_active_inst:
  !vs0 ctx astk k L AP AG tn fn inst s.
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  active_inst fn inst s
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt strip_tac
QED

Theorem ld_fn_pv_ir_vars:
  !P fn. fn_pv P fn SUBSET set (fn_ir_vars fn)
Proof
  rpt gen_tac >> simp[fn_pv_def, pointer_derived_vars_def, SUBSET_DEF] >>
  ho_match_mp_tac pointerConfinedPropsTheory.pointer_use_vars_least >>
  conj_tac
  >- (simp[MEM_SET_TO_LIST, ld_ptr_roots_finite, ptr_roots_def,
           alloca_roots_def] >> rpt strip_tac >>
      gvs[inst_output_def, AllCaseEqs()] >>
      gvs[fn_insts_def, fn_insts_blocks_MEM] >>
      simp[fn_ir_vars_member] >> metis_tac[MEM]) >>
  rpt strip_tac >> simp[fn_ir_vars_member] >> metis_tac[]
QED

Theorem ld_annotated_prov_ir_vars:
  (!f. MEM f ctx.ctx_functions ==> fn_ptr_ok P f) /\
  ld_annotated_reachable vs0 ctx astk k L AP AG tn fn inst s ==>
  FDOM AG SUBSET set (fn_ir_vars fn)
Proof
  strip_tac >> drule_all ld_annotated_prov_support >>
  metis_tac[ld_fn_pv_ir_vars, SUBSET_TRANS]
QED

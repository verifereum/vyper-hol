Theory lowerDloadPtrRetpcClean
Ancestors ptrDiscipline unitShapeDefs execEquivParamBase venomInst o1PassContract contextCodegenRel finite_map list

Theorem dload_retpc_out_taint:
  retpc_shape_ok fn /\ MEM i (fn_insts fn) /\
  MEM v i.inst_outputs /\ retpc_var fn v /\
  (!x. retpc_var fn x ==> op_taint tn (Var x) = {}) ==>
  out_taint tn i s = {}
Proof
  rpt strip_tac >>
  `i.inst_opcode = RETPC_PARAM \/ i.inst_opcode = PHI \/
   (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\ retpc_var fn y)` by
    (gvs[retpc_shape_ok_def] >> metis_tac[]) >>
  gvs[] >> simp[out_taint_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem dload_step_retpc_clean:
  retpc_shape_ok fn /\ MEM i (fn_insts fn) /\
  (!x. retpc_var fn x ==> op_taint tn (Var x) = {}) ==>
  !x. retpc_var fn x ==> op_taint (step_taint i s s' tn) (Var x) = {}
Proof
  rpt strip_tac >>
  `op_taint tn (Var x) = {}` by metis_tac[] >>
  Cases_on `i.inst_outputs` >>
  simp[step_taint_def, set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT] >-
    gvs[op_taint_def] >>
  rename1 `i.inst_outputs = out::outs` >> Cases_on `outs` >>
  simp[step_taint_def, set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE] >>
  Cases_on `x = out` >> gvs[op_taint_def]
  >- (irule dload_retpc_out_taint >> simp[] >> qexists `fn` >>
      simp[] >> gvs[op_taint_def]) >>
  IF_CASES_TAC >> simp[]
QED

Theorem dload_retpc_phi_taint:
  retpc_shape_ok fn /\ MEM i (fn_insts fn) /\
  MEM v i.inst_outputs /\ retpc_var fn v /\ i.inst_opcode = PHI /\
  (!x. retpc_var fn x ==> op_taint tn (Var x) = {}) ==>
  phi_taint prev tn i = {}
Proof
  rpt strip_tac >>
  `!y. MEM (Var y) i.inst_operands ==> retpc_var fn y` by
    (qpat_x_assum `retpc_shape_ok fn` mp_tac >>
     simp[retpc_shape_ok_def] >> strip_tac >>
     qpat_x_assum `!inst x. _` (qspecl_then [`i`, `v`] mp_tac) >> simp[]) >>
  Cases_on `prev` >> simp[phi_taint_def] >>
  Cases_on `resolve_phi x i.inst_operands` >> simp[] >>
  `MEM x' i.inst_operands` by metis_tac[resolve_phi_MEM] >>
  Cases_on `x'` >> simp[op_taint_def] >>
  metis_tac[op_taint_def]
QED

Theorem dload_phis_retpc_clean:
  !is tn prev fn.
  retpc_shape_ok fn /\ EVERY (\i. MEM i (fn_insts fn)) is /\
  (!x. retpc_var fn x ==> op_taint tn (Var x) = {}) ==>
  !x. retpc_var fn x ==>
    op_taint (tn with t_var := phis_taint prev tn is) (Var x) = {}
Proof
  Induct >> simp[phis_taint_def, op_taint_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[phis_taint_def] >> rpt strip_tac >>
      `op_taint (tn with t_var := phis_taint prev tn is) (Var x) = {}` by
        (first_x_assum irule >> simp[op_taint_def] >> metis_tac[]) >>
      Cases_on `h.inst_outputs` >>
      gvs[set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT] >>
      rename1 `h.inst_outputs = out::outs` >> Cases_on `outs` >>
      simp[set_var_taint_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      Cases_on `x = out` >> gvs[]
      >- (irule dload_retpc_phi_taint >> simp[] >> qexists `fn` >>
          simp[op_taint_def]) >>
      IF_CASES_TAC >> simp[]) >>
  simp[phis_taint_def, op_taint_def]
QED

Theorem dload_entry_retpc_clean:
  retpc_shape_ok fn /\
  (!x. retpc_var fn x ==> op_taint tn (Var x) = {}) ==>
  !x. retpc_var fn x ==> op_taint (entry_taint_vars fn s tn) (Var x) = {}
Proof
  rpt strip_tac >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[entry_taint_vars_def] >>
  irule dload_phis_retpc_clean >> simp[] >>
  `MEM x' fn.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  simp[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem dload_active_member[local]:
  active_inst fn i s ==> MEM i (fn_insts fn)
Proof
  simp[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[EL_MEM]
QED

Theorem dload_frame_retpc_clean:
  !vs0 C stk PG G tn fn inst s.
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  EVERY fn_shape_ok C.ctx_functions ==>
  MEM fn C.ctx_functions /\
  (!v. retpc_var fn v ==> op_taint tn (Var v) = {}) /\
  (!c. MEM c stk ==> MEM c.cf_fn C.ctx_functions /\
       !v. retpc_var c.cf_fn v ==>
         op_taint (tn with t_var := c.cf_tvar) (Var v) = {})
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (simp[entry_taint_def, op_taint_def] >> metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `retpc_shape_ok fn` by (gvs[EVERY_MEM, fn_shape_ok_def] >> metis_tac[]) >>
      `MEM inst (fn_insts fn)` by metis_tac[dload_active_member] >>
      simp[] >> conj_tac
      >- metis_tac[dload_step_retpc_clean] >>
      gvs[op_taint_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      `retpc_shape_ok fn` by (gvs[EVERY_MEM, fn_shape_ok_def] >> metis_tac[]) >>
      simp[] >> conj_tac
      >- metis_tac[dload_entry_retpc_clean] >>
      gvs[op_taint_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      simp[op_taint_def] >> rpt strip_tac >> gvs[op_taint_def] >>
      metis_tac[lookup_function_MEM])
  >> rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[op_taint_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

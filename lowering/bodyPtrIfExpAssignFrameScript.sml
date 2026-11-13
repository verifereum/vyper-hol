Theory bodyPtrIfExpAssignFrame
Ancestors
  bodyPtrIfExpAssign bodyPtrDefs ptrDiscipline venomInst venomState
  finite_map pred_set codegenRel

Theorem assign_result_prov:
  op_prov (step_prov PG G (mk_inst id ASSIGN [src] [out]) u) (Var out) =
  op_prov G src
Proof
  Cases_on `op_prov G src` >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def, mk_inst_def] >>
  gvs[op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem assign_other_prov:
  x <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id ASSIGN [src] [out]) u) x = FLOOKUP G x
Proof
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def, mk_inst_def] >>
  Cases_on `op_prov G src` >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem assign_taint:
  eval_operand src s = SOME w ==>
  step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out, op_taint tn src)
Proof
  simp[step_taint_def, mem_taint_def, out_taint_def, set_var_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, mk_inst_def,
       taint_component_equality, update_var_def, new_site_bytes_def,
       step_writes_def, written_taint_def, source_memory_write_ranges_def,
       range_bytes_def, FLOOKUP_DEF] >> SET_TAC[]
QED

Theorem assign_result_taint:
  eval_operand src s = SOME w ==>
  op_taint (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn) (Var out) =
  op_taint tn src
Proof
  strip_tac >> drule assign_taint >> simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem assign_result_value:
  eval_operand (Var out) (update_var out w s) = SOME w
Proof
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem assign_ptr_val_ok:
  eval_operand src s = SOME w /\ ptr_val_ok cx ty v src G tn s ==>
  ptr_val_ok cx ty v (Var out)
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    (update_var out w s)
Proof
  strip_tac >> simp[ptr_val_ok_def, assign_result_prov] >>
  drule assign_result_taint >> simp[] >> strip_tac >>
  conj_tac >- gvs[ptr_val_ok_def] >>
  conj_tac >- gvs[ptr_val_ok_def] >>
  strip_tac >>
  qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_val_ok_def] >> strip_tac >>
  drule assign_taint >> simp[] >> strip_tac >>
  simp[ptr_mem_ok_def, assign_result_value, update_var_def] >>
  rpt strip_tac >>
  `ptr_mem_ok cx ty v src G tn s` by simp[] >>
  gvs[ptr_mem_ok_def] >>
  qexistsl_tac [`b`, `sz`] >> simp[SRULE[op_prov_def] assign_result_prov]
QED

Theorem assign_ghost_kept:
  eval_operand src s = SOME w /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> out) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
Proof
  strip_tac >> drule assign_taint >> simp[] >> strip_tac >>
  simp[ghost_kept_def] >> conj_tac
  >- (gen_tac >> strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[assign_other_prov, op_taint_def, FLOOKUP_UPDATE] >>
      gvs[ghost_kept_def, op_taint_def]) >>
  fs[ghost_kept_def] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem assign_other_covers:
  eval_operand src s = SOME w /\ x <> out /\ ptr_covers G tn x s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    x (update_var out w s) n
Proof
  strip_tac >> drule assign_taint >> simp[] >> strip_tac >>
  gvs[ptr_covers_def, assign_other_prov, op_taint_def, lookup_var_def,
      update_var_def, FLOOKUP_UPDATE]
QED

Theorem assign_ghost_inv:
  eval_operand src s = SOME w /\ ghost_inv d cenv cx es G tn s /\
  (!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    (update_var out w s)
Proof
  strip_tac >> drule assign_taint >> simp[] >> strip_tac >>
  fs[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      conj_tac
      >- (drule_all assign_other_covers >> simp[assign_taint]) >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      first_x_assum drule_all >> simp[lookup_var_def]) >>
  conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >>
      `x <> out` by metis_tac[] >> conj_tac
      >- gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      drule_all assign_other_covers >> simp[assign_taint]) >>
  conj_tac
  >- (rpt strip_tac >> `x <> out` by metis_tac[] >>
      simp[op_taint_def, FLOOKUP_UPDATE] >> gvs[op_taint_def]) >>
  gvs[stor_taint_ok_def, update_var_def]
QED

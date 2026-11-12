Theory bodyFullIfExpGhost
Ancestors
  bodyPtrIfExpAssignFrame bodyPtrIfExpWordFinish bodyPtrDefs
  venomState codegenRel ptrDiscipline

Theorem ghost_inv_at_finish_cursor:
  ghost_inv_at D lo d cenv cx es G tn
    (jump_to lbl (s with vs_inst_idx := k)) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  Cases_on `d` >> simp[ghost_inv_at_def, jump_to_def, ptr_covers_def, lookup_var_def,
       return_buf_ptr_def, stor_taint_ok_at_def, allocas_from_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem assign_suffix_ghost_at:
  eval_operand src s = SOME w /\ ghost_inv_at D lo d cenv cx es G tn s /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  (!name x sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> x <> out) ==>
  ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
    (jump_to lbl (update_var out w s with vs_inst_idx := k)) /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0
    (step_prov PG G (mk_inst id ASSIGN [src] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [src] [out]) s (update_var out w s) tn)
Proof
  strip_tac >> simp[ghost_inv_at_finish_cursor] >> conj_tac
  >- (irule assign_ghost_inv_at >> simp[] >> metis_tac[]) >>
  irule assign_ghost_kept_at >> simp[] >> metis_tac[]
QED

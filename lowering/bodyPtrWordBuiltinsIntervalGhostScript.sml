(* Ghost frame transport for the temporary-only interval witness. *)
Theory bodyPtrWordBuiltinsIntervalGhost
Ancestors bodyPtrDefs stmtFragPtr ptrDiscipline finite_map venomState

Theorem word_interval_temp_observations:
  p <> x ==>
  lookup_var p (update_var x w s) = lookup_var p s /\
  op_taint (tn with t_var := set_var_taint tn.t_var [x] {}) (Var p) =
    op_taint tn (Var p) /\
  (ptr_covers (DRESTRICT G (COMPL {x}))
    (tn with t_var := set_var_taint tn.t_var [x] {}) p (update_var x w s) sz <=>
   ptr_covers G tn p s sz)
Proof
  simp[lookup_var_def, update_var_def, op_taint_def, set_var_taint_def,
       FLOOKUP_UPDATE, ptr_covers_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

Theorem word_interval_ghost_inv_temp:
  ghost_inv d cenv cx es G tn s /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es (DRESTRICT G (COMPL {x}))
    (tn with t_var := set_var_taint tn.t_var [x] {}) (update_var x w s)
Proof
  strip_tac >> fs[ghost_inv_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> x` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[word_interval_temp_observations] >>
      simp[update_var_def]) >>
  conj_tac
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      PairCases_on `x'` >> fs[return_buf_ptr_def] >>
      rpt strip_tac >>
      `x' <> x` by metis_tac[] >>
      metis_tac[word_interval_temp_observations]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `x' <> x` by metis_tac[] >>
      simp[word_interval_temp_observations] >> metis_tac[]) >>
  fs[stor_taint_ok_def, update_var_def]
QED

Theorem word_interval_ghost_kept_temp:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!y. not_fresh_at sa y ==> y <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0 (DRESTRICT G (COMPL {x}))
    (tn with t_var := set_var_taint tn.t_var [x] {})
Proof
  strip_tac >> fs[ghost_kept_def] >>
  conj_tac
  >- (rpt strip_tac >> `x' <> x` by metis_tac[] >>
      simp[FLOOKUP_DRESTRICT, word_interval_temp_observations] >>
      metis_tac[]) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem word_interval_ghost_inv_index:
  ghost_inv d cenv cx es G tn (s with vs_inst_idx := i) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[ghost_inv_def, ptr_covers_def, stor_taint_ok_def, lookup_var_def] >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem word_interval_ghost_inv_jump:
  ghost_inv d cenv cx es G tn (jump_to l s) <=>
  ghost_inv d cenv cx es G tn s
Proof
  simp[jump_to_def, ghost_inv_jump_to]
QED

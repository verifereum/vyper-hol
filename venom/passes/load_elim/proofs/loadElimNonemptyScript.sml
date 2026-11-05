Theory loadElimNonempty
Ancestors
  loadElimDefs loadElimTransferProvenance loadElimLatticeSoundHelpers
  loadElimConvergence loadElimSolverHelpers loadElimSupportHelpers
  loadElimOrderHelpers loadElimBilateralInvariant dfAnalyzeProofs dfAnalyzeDefs
  venomInst finite_map list pred_set

Definition le_lists_nonempty_def:
  le_lists_nonempty ll <=>
    !k vs. FLOOKUP (unwrap_load_lattice ll) k = SOME vs ==> vs <> []
End

Theorem le_lists_nonempty_initial[simp]:
  le_lists_nonempty NONE /\ le_lists_nonempty (SOME FEMPTY)
Proof
  simp[le_lists_nonempty_def, unwrap_load_lattice_def]
QED

Theorem le_lists_nonempty_transfer:
  le_lists_nonempty ll ==> le_lists_nonempty (load_transfer ctx inst ll)
Proof
  simp[le_lists_nonempty_def] >> rpt strip_tac >>
  drule le_transfer_lookup_origin >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem le_lists_nonempty_join:
  le_lists_nonempty a /\ le_lists_nonempty b ==>
  le_lists_nonempty (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >> simp[load_join_def] >>
  simp[le_lists_nonempty_def, unwrap_load_lattice_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  fs[operand_list_union_def] >> metis_tac[]
QED

Theorem le_analyze_lists_nonempty:
  wf_function fn ==>
  (!lbl idx. le_lists_nonempty (df_at NONE (load_analyze ctx fn) lbl idx)) /\
  (!lbl. le_lists_nonempty (df_boundary NONE (load_analyze ctx fn) lbl))
Proof
  strip_tac >> simp[load_analyze_def] >>
  irule le_df_analyze_invariant_bilateral >>
  simp[load_edge_transfer_def, le_lists_nonempty_join, le_lists_nonempty_transfer] >>
  conj_tac >- (Cases_on `fn_entry_label fn` >> simp[]) >>
  qexistsl [
    `le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
       (le_generated_operands (fn_insts fn))`,
    `CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))`,
    `le_solver_leq`,
    `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
       (le_generated_operands (fn_insts fn))`] >>
  simp[GSYM le_solver_process_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all le_solver_process_closed >>
      simp[le_solver_process_def]) >>
  conj_tac
  >- simp[le_solver_process_inflationary] >>
  conj_tac
  >- (drule le_solver_entry_init >>
      Cases_on `fn_entry_label fn` >> simp[fn_labels_def]) >>
  irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] le_solver_bounded_measure) >> simp[]
QED

Theorem le_analyze_point_lookup_nonempty:
  wf_function fn /\
  FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn) lbl idx)) k =
    SOME vs ==> vs <> []
Proof
  strip_tac >> drule le_analyze_lists_nonempty >>
  simp[le_lists_nonempty_def] >> metis_tac[]
QED

Theorem le_analyze_boundary_lookup_nonempty:
  wf_function fn /\
  FLOOKUP (unwrap_load_lattice (df_boundary NONE (load_analyze ctx fn) lbl)) k =
    SOME vs ==> vs <> []
Proof
  strip_tac >> drule le_analyze_lists_nonempty >>
  simp[le_lists_nonempty_def] >> metis_tac[]
QED

(* Membership inclusion does not eliminate duplicates: [v;v] is allowed. *)
Theorem le_nonempty_singleton_members:
  ws <> [] /\ (!x. MEM x ws ==> MEM x [v]) ==>
  EVERY (\x. x = v) ws /\ MEM v ws
Proof
  Cases_on `ws` >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem le_lists_nonempty_fold:
  !insts ll. le_lists_nonempty ll ==>
    le_lists_nonempty (FOLDL (\a i. load_transfer ctx i a) ll insts)
Proof
  Induct >> simp[] >> metis_tac[le_lists_nonempty_transfer]
QED

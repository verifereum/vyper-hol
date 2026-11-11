Theory invariantBlockSimulationProps
Ancestors
  passSimulationDefs venomExecSemantics venomExecProps venomInst stateEquiv

(* Error-excusing, cross-state lifting.  Only the source entry invariant
   must be maintained.  Abort observations need not equal terminal ones,
   and block lookup may be supplied independently of a map transform. *)
Theorem run_blocks_invariant_simulation:
  !fuel ctx fn fn' B Inv R_ok R_term R_abort s t.
    (!lbl. lookup_block lbl fn'.fn_blocks =
      OPTION_MAP B (lookup_block lbl fn.fn_blocks)) /\
    (!u v. R_ok u v ==>
      u.vs_current_bb = v.vs_current_bb /\
      u.vs_halted = v.vs_halted /\ R_term u v) /\
    (!k bb u u'. MEM bb fn.fn_blocks /\ Inv u /\
      run_block k ctx bb u = OK u' /\ ~u'.vs_halted ==> Inv u') /\
    (!k bb u v. MEM bb fn.fn_blocks /\ Inv u /\ R_ok u v ==>
      (?e. run_block k ctx bb u = Error e) \/
      lift_result R_ok R_term R_abort
        (run_block k ctx bb u) (run_block k ctx (B bb) v)) /\
    Inv s /\ R_ok s t ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result R_ok R_term R_abort
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (disj1_tac >> simp[run_blocks_unfold]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `s.vs_current_bb = t.vs_current_bb` by metis_tac[] >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (B bb)` by
    (qpat_x_assum `!lbl. _` (qspec_then `s.vs_current_bb` mp_tac) >>
     simp[]) >>
  `(?e. run_block fuel ctx bb s = Error e) \/
    lift_result R_ok R_term R_abort
      (run_block fuel ctx bb s) (run_block fuel ctx (B bb) t)` by
    (first_x_assum irule >> simp[])
  >- (disj1_tac >> simp[run_blocks_unfold]) >>
  simp[run_blocks_unfold] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx (B bb) t` >> gvs[lift_result_def] >>
  rename1 `R_ok u1 u2` >>
  `u1.vs_halted = u2.vs_halted /\ R_term u1 u2` by metis_tac[] >>
  Cases_on `u1.vs_halted`
  >- metis_tac[lift_result_def] >>
  `~u2.vs_halted` by metis_tac[] >>
  gvs[] >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`B`, `Inv`] >> simp[] >> metis_tac[]
QED

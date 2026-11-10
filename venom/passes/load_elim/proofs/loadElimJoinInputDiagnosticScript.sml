Theory loadElimJoinInputDiagnostic
Ancestors
  loadElimDefs loadElimBoundaryProvenance loadElimOrderHelpers
  loadElimLatticeSoundHelpers loadElimJoinProps
  finite_map pred_set list

(* Updating one predecessor by accumulating a fresh result cannot invalidate
   conditional inclusion into the joined input. This is a set fact, not a
   list-order monotonicity claim. *)
Theorem le_pred_lookup_rel_join_context:
  le_pred_lookup_rel k (load_join a p) b ==>
  le_pred_lookup_rel k (load_join a (load_join p fresh)) b
Proof
  Cases_on `a` >> Cases_on `p` >> Cases_on `fresh` >> Cases_on `b` >>
  simp[load_join_def, unwrap_load_lattice_def, le_pred_lookup_rel_def,
       le_join_raw_lookup_eq] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mem_operand_list_union, SUBSET_DEF] >>
  metis_tac[]
QED

(* NONE-to-reached with no key destroys unconditional input presence, even
   when the old accumulated boundary retains two alternatives. *)
Theorem le_join_input_key_disappears:
  load_join (SOME (FEMPTY |+ (k, [Var "a"; Var "b"]))) NONE =
    SOME (FEMPTY |+ (k, [Var "a"; Var "b"])) /\
  load_join (SOME (FEMPTY |+ (k, [Var "a"; Var "b"])))
    (load_join NONE (SOME FEMPTY)) = SOME FEMPTY /\
  le_pred_lookup_rel k (SOME FEMPTY)
    (SOME (FEMPTY |+ (k, [Var "a"; Var "b"])))
Proof
  simp[load_join_def, load_join_raw_def, le_pred_lookup_rel_def,
       unwrap_load_lattice_def]
QED

(* An arbitrary absorbed boundary may contain an unsupported old alternative.
   Thus fixpoint absorption plus current predecessor singletons is insufficient
   without initialized chronological provenance. *)
Theorem le_join_absorbed_stale_alternative:
  load_join (SOME (FEMPTY |+ (k, [Var "a"; Var "b"; Var "c"])))
    (load_join (SOME (FEMPTY |+ (k, [Var "a"])))
               (SOME (FEMPTY |+ (k, [Var "b"])))) =
    SOME (FEMPTY |+ (k, [Var "a"; Var "b"; Var "c"])) /\
  ~le_pred_lookup_rel k
    (load_join (SOME (FEMPTY |+ (k, [Var "a"])))
               (SOME (FEMPTY |+ (k, [Var "b"]))))
    (SOME (FEMPTY |+ (k, [Var "a"; Var "b"; Var "c"])))
Proof
  simp[load_join_singleton_same, operand_list_union_def,
       le_pred_lookup_rel_def, unwrap_load_lattice_def, SUBSET_DEF,
       FLOOKUP_UPDATE] >>
  qexists `Var "c"` >> simp[]
QED

Theory tupleAssignImmutableDeployIntEntryAudit
Ancestors
  bodyIntCallSeams localPtrsProps loweringStateRelDefs vyperTyping venomMemDefs finite_map

(* Diagnostic only: neither probe is a counterexample to the task. *)
Theorem empty_intret_does_not_type[local]:
  intret_vals_match NoneTV (BoolV T) [] /\
  ~value_has_type NoneTV (BoolV T)
Proof
  simp[intret_vals_match_def, value_has_type_def]
QED

Theorem same_site_not_separated[local]:
  alloca_inv (s with <|vs_allocas := FEMPTY |+ (7,(0,32));
                      vs_alloca_next := 32|>) /\
  FLOOKUP (s with vs_allocas := FEMPTY |+ (7,(0,32))).vs_allocas 7 =
    SOME (0,32) /\
  7 <= (7:num) /\ ~regions_disjoint 0 32 0 32
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       FLOOKUP_UPDATE, loweringStateRelDefsTheory.regions_disjoint_def]
QED

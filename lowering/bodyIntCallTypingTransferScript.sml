(* Permission-enlargement boundaries for callee typing witnesses. *)
Theory bodyIntCallTypingTransfer
Ancestors
  vyperTypeSystem finite_map

Theorem permission_lookup_update:
  (!n. FLOOKUP m n = SOME T ==> FLOOKUP m' n = SOME T) ==>
  !n. FLOOKUP (m |+ (id,b)) n = SOME T ==>
      FLOOKUP (m' |+ (id,b)) n = SOME T
Proof
  rpt strip_tac >> Cases_on `n = id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem type_place_target_name_permission:
  e' = e with var_assignable := m /\
  (!n. FLOOKUP e.var_assignable n = SOME T ==> FLOOKUP m n = SOME T) /\
  type_place_target e (NameTarget id) = SOME vt ==>
  type_place_target e' (NameTarget id) = SOME vt
Proof
  strip_tac >> gvs[Once well_typed_expr_def, AllCaseEqs()] >>
  simp[Once well_typed_expr_def]
QED

Theorem permission_true_map_domain:
  FDOM ((K T) o_f m) = FDOM m
Proof
  simp[]
QED

Theorem permission_true_map_lookup:
  IS_SOME (FLOOKUP m n) ==> FLOOKUP ((K T) o_f m) n = SOME T
Proof
  Cases_on `FLOOKUP m n` >> simp[FLOOKUP_o_f]
QED

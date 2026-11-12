(* Interface audit facts only: these do not produce paired call setup/pop. *)
Theory lowerDloadReturnInvokeInterface
Ancestors
  lowerDloadReturnInterfaceProbe lowerDloadReturnStable finite_map pred_set
Libs
  lowerDloadReturnPackageLib

(* The keep set is independent of the intermediate map. In particular it
   may be the surviving slots computed from the final allocation map. *)
Theorem ld_saved_map_restrict_trans:
  saved SUBSET keep /\
  (!a. a IN saved ==> FLOOKUP A1 a = FLOOKUP A0 a) /\
  (!a. a IN saved ==> FLOOKUP A2 a = FLOOKUP A1 a) ==>
  !a. a IN saved ==> FLOOKUP (DRESTRICT A2 keep) a = FLOOKUP A0 a
Proof
  simp[SUBSET_DEF, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

val _ = if null (hyp ld_saved_map_restrict_trans) then ()
        else raise Fail "saved-map interface has kernel hypotheses";

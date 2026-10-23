Theory placeTypingBuildProps
Ancestors
  placeTypingProps vyperTypeContract

(* A single-module checker does not reject dots in declaration identifiers.
   A fabricated imported namespace can therefore alias a main-module key. *)
Theorem map_namespace_collision_probe:
  let tops = [HashMapDecl Private F "0.m" (BaseT (UintT 256))
                (Type (BaseT (UintT 256))) (SOME 0)] in
  let mods = [(NONE,tops)] in
  let layouts = [(0w, ([( (NONE,"0.m"), 0)], []))] in
  IS_SOME (check_contract F layouts 0w mods) /\
  OPTION_MAP (\(tr,kt,vt). (kt,vt))
    (build_hashmap_info tops (module_var_key (SOME 0,"m"))) =
      SOME (BaseT (UintT 256), Type (BaseT (UintT 256))) /\
  FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes
    (SOME 0,"m") = NONE
Proof
  EVAL_TAC
QED

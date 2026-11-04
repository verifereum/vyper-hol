(* Selected-module type lookup boundaries. Successful lookups, not whole
   maps, are preserved when the source combines all module namespaces. *)
Theory bodyIntCallTypeEval
Ancestors
  vyperContext list alist finite_map

Theorem type_env_for_module_other_namespace:
  !tops src other n.
    src <> other ==>
    FLOOKUP (type_env_for_module src tops) (other,n) = NONE
Proof
  Induct >> simp[type_env_for_module_def] >>
  Cases_on `h` >> simp[type_env_for_module_def, FLOOKUP_UPDATE]
QED

Theorem selected_module_type_lookup:
  !mods src tops n a.
    ALOOKUP mods src = SOME tops /\
    FLOOKUP (type_env_for_module src tops) (src,n) = SOME a ==>
    FLOOKUP (type_env_all_modules mods) (src,n) = SOME a
Proof
  Induct >- simp[] >> PairCases >> rpt gen_tac >>
  simp[ALOOKUP_def, type_env_all_modules_def] >>
  Cases_on `h0 = src` >> gvs[FLOOKUP_FUNION] >>
  simp[type_env_for_module_other_namespace]
QED

Theorem get_tenv_selected_module_type_lookup:
  get_module_code cx src = SOME tops /\
  FLOOKUP (type_env_for_module src tops) (src,n) = SOME a ==>
  FLOOKUP (get_tenv cx) (src,n) = SOME a
Proof
  Cases_on `ALOOKUP cx.sources cx.txn.target` >>
  simp[get_module_code_def, get_tenv_def] >>
  strip_tac >> irule selected_module_type_lookup >> metis_tac[]
QED

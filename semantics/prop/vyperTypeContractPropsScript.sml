(*
 * Bridge properties for the whole-contract Vyper type checker.
 *
 * The definitions in vyperTypeContract build a contract_type_artifact from a
 * module set and check that declarations/bodies satisfy the static rules.  This
 * theory proves that successful checking supplies the proof-facing consistency
 * predicates used by the type-soundness theorems.
 *)

Theory vyperTypeContractProps
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants
Libs
  wordsLib

Theorem get_module_code_initial_evaluation_context:
  ALOOKUP sources addr = SOME mods /\ tx.target = addr ==>
  get_module_code (initial_evaluation_context sources layouts tx) src = ALOOKUP mods src
Proof
  rw[get_module_code_def, initial_evaluation_context_def]
QED

Theorem lookup_callable_function_F:
  lookup_callable_function F fn ts = lookup_function NONE fn Internal ts
Proof
  rw[lookup_callable_function_def] >>
  Cases_on `lookup_function NONE fn Internal ts` >> simp[]
QED
Theorem contract_fn_sig_key_MEM:
  MEM (src,ts) mods /\
  MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) ts ==>
  MEM (src,fn) (contract_keys (fn_sig_keys_toplevel F) mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (fn_sig_keys_toplevel F src) ts)` >>
  simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >>
  qexists `fn_sig_keys_toplevel F src
    (FunctionDecl Internal fm nr raw fn args dflts ret body)` >>
  simp[fn_sig_keys_toplevel_def, include_fn_sig_def] >>
  qexists `FunctionDecl Internal fm nr raw fn args dflts ret body` >>
  simp[fn_sig_keys_toplevel_def, include_fn_sig_def]
QED
Theorem module_fn_sig_key_MEM:
  MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) ts ==>
  MEM (src,fn) (FLAT (MAP (fn_sig_keys_toplevel F src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `fn_sig_keys_toplevel F src
    (FunctionDecl Internal fm nr raw fn args dflts ret body)` >>
  simp[fn_sig_keys_toplevel_def, include_fn_sig_def] >>
  qexists `FunctionDecl Internal fm nr raw fn args dflts ret body` >>
  simp[fn_sig_keys_toplevel_def, include_fn_sig_def]
QED

Theorem lookup_function_Internal_MEM:
  ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel F src) ts)) /\
  MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) ts ==>
  lookup_callable_function F fn ts = SOME (fm,nr,args,dflts,ret,body)
Proof
  Induct_on `ts` >- rw[lookup_callable_function_F, lookup_function_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_callable_function_F, lookup_function_def, fn_sig_keys_toplevel_def,
     include_fn_sig_def] >>
  gvs[lookup_callable_function_F, lookup_function_def, fn_sig_keys_toplevel_def,
      include_fn_sig_def] >>
  drule module_fn_sig_key_MEM >>
  disch_then (qspec_then `src` assume_tac) >>
  TRY (Cases_on `v`) >>
  gvs[lookup_function_def]
QED

Theorem lookup_callable_function_F_SOME_MEM:
  lookup_callable_function F fn ts = SOME (fm,nr,args,dflts,ret,body) ==>
  ?raw. MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) ts
Proof
  Induct_on `ts` >- rw[lookup_callable_function_F, lookup_function_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_callable_function_F, lookup_function_def] >>
  TRY (Cases_on `v`) >>
  gvs[lookup_callable_function_F, lookup_function_def] >-
    (qexists `b0` >> simp[]) >>
  qexists `raw` >> simp[]
QED

Theorem add_toplevel_static_maps_fn_sigs_sound:
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_fn_sigs k = SOME sig ==>
  FLOOKUP art.cta_fn_sigs k = SOME sig \/
  ?fm nr raw fn args dflts ret body.
    tl = FunctionDecl Internal fm nr raw fn args dflts ret body /\
    k = (src,fn) /\ sig = fn_sig_of args dflts ret
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, include_fn_sig_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `f`) >>
  TRY (Cases_on `v0`) >>
  gvs[add_toplevel_static_maps_def, include_fn_sig_def, FLOOKUP_UPDATE] >>
  Cases_on `(src,s) = k` >> gvs[]
QED

Theorem add_toplevel_static_maps_fn_sigs_complete:
  tl = FunctionDecl Internal fm nr raw fn args dflts ret body /\
  k = (src,fn) /\ sig = fn_sig_of args dflts ret ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_fn_sigs k = SOME sig
Proof
  rw[add_toplevel_static_maps_def, include_fn_sig_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_fn_sigs_preserve:
  FLOOKUP art.cta_fn_sigs k = SOME sig /\
  ~(MEM k (fn_sig_keys_toplevel F src tl)) ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_fn_sigs k = SOME sig
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, fn_sig_keys_toplevel_def,
     include_fn_sig_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `f`) >>
  TRY (Cases_on `v0`) >>
  gvs[add_toplevel_static_maps_def, fn_sig_keys_toplevel_def,
      include_fn_sig_def, FLOOKUP_UPDATE]
QED

Theorem add_module_static_maps_fn_sigs_sound:
  FLOOKUP (add_module_static_maps F src tls art).cta_fn_sigs k = SOME sig ==>
  FLOOKUP art.cta_fn_sigs k = SOME sig \/
  ?tl fm nr raw fn args dflts ret body.
    MEM tl tls /\
    tl = FunctionDecl Internal fm nr raw fn args dflts ret body /\
    k = (src,fn) /\ sig = fn_sig_of args dflts ret
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >>
  strip_tac >-
    (drule add_toplevel_static_maps_fn_sigs_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_module_static_maps_fn_sigs_preserve:
  FLOOKUP art.cta_fn_sigs k = SOME sig /\
  ~(MEM k (FLAT (MAP (fn_sig_keys_toplevel F src) tls))) ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_fn_sigs k = SOME sig
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` irule) >>
  simp[] >>
  irule add_toplevel_static_maps_fn_sigs_preserve >>
  simp[]
QED

Theorem add_module_static_maps_fn_sigs_complete:
  ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel F src) tls)) /\
  MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_fn_sigs (src,fn) =
    SOME (fn_sig_of args dflts ret)
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_fn_sigs_preserve >>
     simp[add_toplevel_static_maps_fn_sigs_complete] >>
     gvs[ALL_DISTINCT_APPEND, fn_sig_keys_toplevel_def, include_fn_sig_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >>
  strip_tac >>
  irule add_toplevel_static_maps_fn_sigs_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_fn_sig_key_MEM]
QED

Theorem contract_namespaces_ok_module_fn_sig_keys:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods ==>
  ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel F src) tls))
Proof
  rw[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ mods))` mp_tac >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem add_contract_static_maps_fn_sigs_sound:
  FLOOKUP
    (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_fn_sigs k = SOME sig ==>
  FLOOKUP art.cta_fn_sigs k = SOME sig \/
  ?src tls tl fm nr raw fn args dflts ret body.
    MEM (src,tls) mods /\ MEM tl tls /\
    tl = FunctionDecl Internal fm nr raw fn args dflts ret body /\
    k = (src,fn) /\ sig = fn_sig_of args dflts ret
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  simp[] >>
  strip_tac >-
    (drule add_module_static_maps_fn_sigs_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_contract_static_maps_fn_sigs_preserve:
  FLOOKUP art.cta_fn_sigs k = SOME sig /\
  ~(MEM k (contract_keys (fn_sig_keys_toplevel F) mods)) ==>
  FLOOKUP
    (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_fn_sigs k = SOME sig
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[contract_keys_def] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` irule) >>
  conj_tac >- simp[contract_keys_def] >>
  irule add_module_static_maps_fn_sigs_preserve >>
  simp[]
QED

Theorem add_contract_static_maps_fn_sigs_complete_MEM:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (FunctionDecl Internal fm nr raw fn args dflts ret body) tls ==>
  FLOOKUP
    (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_fn_sigs (src,fn) =
    SOME (fn_sig_of args dflts ret)
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_fn_sigs_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_fn_sig_key_MEM]) >>
     irule add_module_static_maps_fn_sigs_complete >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_fn_sigs_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[contract_fn_sig_key_MEM]
QED

Theorem build_contract_type_artifact_fn_sigs_sound:
  contract_namespaces_ok F mods /\
  FLOOKUP (build_contract_type_artifact F mods).cta_fn_sigs (src,fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    ALOOKUP mods src = SOME ts /\
    lookup_callable_function F fn ts = SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    sig.param_types = MAP SND params /\
    sig.num_defaults = LENGTH dflts
Proof
  rw[build_contract_type_artifact_def] >>
  drule add_contract_static_maps_fn_sigs_sound >> rw[] >> gvs[] >>
  gvs[empty_contract_type_artifact_def] >>
  drule contract_namespaces_ok_module_fn_sig_keys >>
  disch_then drule >> strip_tac >>
  drule lookup_function_Internal_MEM >>
  disch_then drule >> strip_tac >>
  qexistsl [`tls`,`fm`,`nr`,`args`,`dflts`,`body`] >>
  gvs[fn_sig_of_def] >>
  irule ALOOKUP_ALL_DISTINCT_MEM >>
  gvs[contract_namespaces_ok_def]
QED

Theorem build_contract_type_artifact_fn_sigs_complete:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (fm,nr,params,dflts,ret,body) ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_fn_sigs (src,fn) =
    SOME <| param_types := MAP SND params; num_defaults := LENGTH dflts; ret_ty := ret |>
Proof
  rw[build_contract_type_artifact_def] >>
  drule ALOOKUP_MEM >> strip_tac >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  drule add_contract_static_maps_fn_sigs_complete_MEM >>
  disch_then drule >>
  disch_then drule >>
  gvs[fn_sig_of_def]
QED



(* The first bridge target is the function-signature component of the artifact.
 * For post-deployment calls, initial_evaluation_context has in_deploy = F, and
 * check_contract F stores exactly the internal-call signatures that
 * lookup_callable_function F can find.  The namespace check in check_contract is
 * intended to rule out FUPDATE/lookup-order mismatches. *)
Theorem check_contract_fn_sigs_consistent_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  fn_sigs_consistent art.cta_fn_sigs
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, fn_sigs_consistent_def] >> gvs[] >>
  drule build_contract_type_artifact_fn_sigs_sound >>
  disch_then drule >>
  rw[] >>
  qexistsl [`ts`,`fm`,`nr`,`params`,`dflts`,`body`] >>
  simp[get_module_code_def, initial_evaluation_context_def]
QED

Theorem check_contract_fn_sigs_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  fn_sigs_complete art.cta_fn_sigs
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, fn_sigs_complete_def] >> gvs[] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  irule build_contract_type_artifact_fn_sigs_complete >>
  simp[]
QED


(* ===== Static-map soundness bridges for contract artifacts ===== *)

Theorem add_toplevel_static_maps_toplevel_vtypes_sound:
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_toplevel_vtypes k = SOME vt ==>
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt \/
  (?vis mut id ty init.
     tl = VariableDecl vis mut id ty init /\
     k = (src,string_to_num id) /\ vt = Type ty) \/
  (?vis is_transient id kt vty init.
     tl = HashMapDecl vis is_transient id kt vty init /\
     k = (src,string_to_num id) /\ vt = HashMapT kt vty)
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE]) >>
  gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem add_toplevel_static_maps_bare_globals_sound:
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_bare_globals k = SOME ty ==>
  FLOOKUP art.cta_bare_globals k = SOME ty \/
  (?vis id typ init.
     tl = VariableDecl vis Immutable id typ init /\
     k = (src,string_to_num id) /\ ty = typ) \/
  (?vis e id typ init.
     tl = VariableDecl vis (Constant e) id typ init /\
     k = (src,string_to_num id) /\ ty = typ)
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE]) >>
  gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem add_toplevel_static_maps_bare_global_assignable_sound:
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_bare_global_assignable k = SOME ty ==>
  FLOOKUP art.cta_bare_global_assignable k = SOME ty \/
  ?vis id typ init.
    tl = VariableDecl vis Immutable id typ init /\
    k = (src,string_to_num id) /\ ty = typ
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE]) >>
  gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem add_toplevel_static_maps_flag_members_sound:
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_flag_members k = SOME members ==>
  FLOOKUP art.cta_flag_members k = SOME members \/
  ?fid ls.
    tl = FlagDecl fid ls /\ k = (src,fid) /\ members = ls
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE]) >>
  gvs[add_toplevel_static_maps_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem add_module_static_maps_toplevel_vtypes_sound:
  FLOOKUP (add_module_static_maps F src tls art).cta_toplevel_vtypes k = SOME vt ==>
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt \/
  (?tl vis mut id ty init.
     MEM tl tls /\ tl = VariableDecl vis mut id ty init /\
     k = (src,string_to_num id) /\ vt = Type ty) \/
  (?tl vis is_transient id kt vty init.
     MEM tl tls /\ tl = HashMapDecl vis is_transient id kt vty init /\
     k = (src,string_to_num id) /\ vt = HashMapT kt vty)
Proof
  qid_spec_tac `art` >> Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >-
    (drule add_toplevel_static_maps_toplevel_vtypes_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_module_static_maps_bare_globals_sound:
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_globals k = SOME ty ==>
  FLOOKUP art.cta_bare_globals k = SOME ty \/
  (?tl vis id typ init.
     MEM tl tls /\ tl = VariableDecl vis Immutable id typ init /\
     k = (src,string_to_num id) /\ ty = typ) \/
  (?tl vis e id typ init.
     MEM tl tls /\ tl = VariableDecl vis (Constant e) id typ init /\
     k = (src,string_to_num id) /\ ty = typ)
Proof
  qid_spec_tac `art` >> Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >-
    (drule add_toplevel_static_maps_bare_globals_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_module_static_maps_bare_global_assignable_sound:
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_global_assignable k = SOME ty ==>
  FLOOKUP art.cta_bare_global_assignable k = SOME ty \/
  ?tl vis id typ init.
    MEM tl tls /\ tl = VariableDecl vis Immutable id typ init /\
    k = (src,string_to_num id) /\ ty = typ
Proof
  qid_spec_tac `art` >> Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >-
    (drule add_toplevel_static_maps_bare_global_assignable_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_module_static_maps_flag_members_sound:
  FLOOKUP (add_module_static_maps F src tls art).cta_flag_members k = SOME members ==>
  FLOOKUP art.cta_flag_members k = SOME members \/
  ?tl fid ls.
    MEM tl tls /\ tl = FlagDecl fid ls /\ k = (src,fid) /\ members = ls
Proof
  qid_spec_tac `art` >> Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >-
    (drule add_toplevel_static_maps_flag_members_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_contract_static_maps_toplevel_vtypes_sound:
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_toplevel_vtypes k = SOME vt ==>
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt \/
  (?src tls tl vis mut id ty init.
     MEM (src,tls) mods /\ MEM tl tls /\ tl = VariableDecl vis mut id ty init /\
     k = (src,string_to_num id) /\ vt = Type ty) \/
  (?src tls tl vis is_transient id kt vty init.
     MEM (src,tls) mods /\ MEM tl tls /\ tl = HashMapDecl vis is_transient id kt vty init /\
     k = (src,string_to_num id) /\ vt = HashMapT kt vty)
Proof
  qid_spec_tac `art` >> Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  simp[] >> strip_tac >-
    (drule add_module_static_maps_toplevel_vtypes_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_contract_static_maps_bare_globals_sound:
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_globals k = SOME ty ==>
  FLOOKUP art.cta_bare_globals k = SOME ty \/
  (?src tls tl vis id typ init.
     MEM (src,tls) mods /\ MEM tl tls /\ tl = VariableDecl vis Immutable id typ init /\
     k = (src,string_to_num id) /\ ty = typ) \/
  (?src tls tl vis e id typ init.
     MEM (src,tls) mods /\ MEM tl tls /\ tl = VariableDecl vis (Constant e) id typ init /\
     k = (src,string_to_num id) /\ ty = typ)
Proof
  qid_spec_tac `art` >> Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  simp[] >> strip_tac >-
    (drule add_module_static_maps_bare_globals_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_contract_static_maps_bare_global_assignable_sound:
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_global_assignable k = SOME ty ==>
  FLOOKUP art.cta_bare_global_assignable k = SOME ty \/
  ?src tls tl vis id typ init.
    MEM (src,tls) mods /\ MEM tl tls /\ tl = VariableDecl vis Immutable id typ init /\
    k = (src,string_to_num id) /\ ty = typ
Proof
  qid_spec_tac `art` >> Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  simp[] >> strip_tac >-
    (drule add_module_static_maps_bare_global_assignable_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem add_contract_static_maps_flag_members_sound:
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_flag_members k = SOME members ==>
  FLOOKUP art.cta_flag_members k = SOME members \/
  ?src tls tl fid ls.
    MEM (src,tls) mods /\ MEM tl tls /\ tl = FlagDecl fid ls /\
    k = (src,fid) /\ members = ls
Proof
  qid_spec_tac `art` >> Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  simp[] >> strip_tac >-
    (drule add_module_static_maps_flag_members_sound >> rw[] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem build_contract_type_artifact_toplevel_vtypes_sound:
  contract_namespaces_ok F mods /\
  FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes (src,id) = SOME vt ==>
  (?ts vis mut id_str ty init.
     ALOOKUP mods src = SOME ts /\ MEM (VariableDecl vis mut id_str ty init) ts /\
     id = string_to_num id_str /\ vt = Type ty) \/
  (?ts vis is_transient id_str kt vty init.
     ALOOKUP mods src = SOME ts /\ MEM (HashMapDecl vis is_transient id_str kt vty init) ts /\
     id = string_to_num id_str /\ vt = HashMapT kt vty)
Proof
  rw[build_contract_type_artifact_def] >>
  drule add_contract_static_maps_toplevel_vtypes_sound >> rw[] >> gvs[empty_contract_type_artifact_def] >>
  gvs[] >> metis_tac[ALOOKUP_ALL_DISTINCT_MEM, contract_namespaces_ok_def]
QED

Theorem build_contract_type_artifact_bare_globals_sound:
  contract_namespaces_ok F mods /\
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals (src,id) = SOME ty ==>
  (?ts vis id_str init.
     ALOOKUP mods src = SOME ts /\ MEM (VariableDecl vis Immutable id_str ty init) ts /\
     id = string_to_num id_str) \/
  (?ts vis e id_str init.
     ALOOKUP mods src = SOME ts /\ MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
     id = string_to_num id_str)
Proof
  rw[build_contract_type_artifact_def] >>
  drule add_contract_static_maps_bare_globals_sound >> rw[] >> gvs[empty_contract_type_artifact_def] >>
  gvs[] >> metis_tac[ALOOKUP_ALL_DISTINCT_MEM, contract_namespaces_ok_def]
QED

Theorem build_contract_type_artifact_bare_global_assignable_sound:
  contract_namespaces_ok F mods /\
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_global_assignable (src,id) = SOME ty ==>
  ?ts vis id_str init.
    ALOOKUP mods src = SOME ts /\ MEM (VariableDecl vis Immutable id_str ty init) ts /\
    id = string_to_num id_str
Proof
  rw[build_contract_type_artifact_def] >>
  drule add_contract_static_maps_bare_global_assignable_sound >> rw[] >> gvs[empty_contract_type_artifact_def] >>
  qexistsl [`tls`,`vis`,`id'`,`init`] >> simp[] >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM, contract_namespaces_ok_def]
QED

Theorem flag_member_key_MEM:
  MEM (FlagDecl fid members) ts ==>
  MEM ((src : num option),fid) (FLAT (MAP (flag_member_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,fid)]` >> simp[] >>
  qexists `FlagDecl fid members` >>
  simp[flag_member_keys_toplevel_def]
QED

Theorem lookup_flag_MEM_FlagDecl:
  ALL_DISTINCT (FLAT (MAP (flag_member_keys_toplevel (src : num option)) ts)) /\
  MEM (FlagDecl fid members) ts ==>
  lookup_flag fid ts = SOME members
Proof
  Induct_on `ts` >- rw[lookup_flag_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_flag_def, flag_member_keys_toplevel_def] >>
  gvs[lookup_flag_def, flag_member_keys_toplevel_def] >>
  metis_tac[flag_member_key_MEM]
QED

Theorem contract_namespaces_ok_module_flag_member_keys:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods ==>
  ALL_DISTINCT (FLAT (MAP (flag_member_keys_toplevel src) tls))
Proof
  rw[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ mods))` mp_tac >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem square_lt[local]:
  a < b ==> a ** 2 < b ** 2
Proof
  rw[EXP_2]
QED

Theorem square_suc_expand[local]:
  (SUC n) ** 2 = SUC (n + (n + n ** 2))
Proof
  rewrite_tac [EXP_2] >> simp[MULT_CLAUSES, ADD_CLAUSES]
QED

Theorem square_suc_bound[local]:
  b <= n ==> n ** 2 + b < (SUC n) ** 2
Proof
  rw[square_suc_expand] >> decide_tac
QED

Theorem square_le[local]:
  a <= b ==> a ** 2 <= b ** 2
Proof
  metis_tac[LESS_OR_EQ, square_lt]
QED

Theorem pair_num_mixed_lt_left[local]:
  b <= n /\ n < a ==> n + n ** 2 + b < n + a ** 2
Proof
  rw[] >>
  `n ** 2 + b < (SUC n) ** 2` by metis_tac[square_suc_bound] >>
  `(SUC n) ** 2 <= a ** 2` by metis_tac[square_le, LESS_EQ] >>
  decide_tac
QED

Theorem pair_num_same_left_11[local]:
  pair_num n a = pair_num n b ==> a = b
Proof
  rw[pair_num_def]
  >- (`b <= n` by decide_tac >>
      drule_all pair_num_mixed_lt_left >> decide_tac)
  >- (`a < b` by decide_tac >>
      `n + n ** 2 + a < n + b ** 2` by
        (irule pair_num_mixed_lt_left >> simp[]) >>
      decide_tac)
QED

Theorem square_suc_bound_sum[local]:
  b <= n ==> n + n ** 2 + b < (SUC n) ** 2
Proof
  rw[square_suc_expand] >> decide_tac
QED

Theorem pair_num_square_bounds[local]:
  MAX x y ** 2 <= pair_num x y /\
  pair_num x y < (SUC (MAX x y)) ** 2
Proof
  Cases_on `x < y` >> simp[pair_num_def, MAX_DEF]
  >- (`y ** 2 + x < (SUC y) ** 2` by
        (irule square_suc_bound >> simp[]) >>
      decide_tac) >>
  `x + x ** 2 + y < (SUC x) ** 2` by
    (irule square_suc_bound_sum >> simp[]) >>
  decide_tac
QED

Theorem square_interval_unique[local]:
  m ** 2 <= p /\ p < (SUC m) ** 2 /\
  n ** 2 <= p /\ p < (SUC n) ** 2 ==> m = n
Proof
  rw[] >>
  Cases_on `m < n`
  >- (`SUC m <= n` by decide_tac >>
      `(SUC m) ** 2 <= n ** 2` by metis_tac[square_le] >>
      decide_tac) >>
  Cases_on `n < m`
  >- (`SUC n <= m` by decide_tac >>
      `(SUC n) ** 2 <= m ** 2` by metis_tac[square_le] >>
      decide_tac) >>
  decide_tac
QED

Theorem pair_num_11[local]:
  pair_num a b = pair_num c d <=> a = c /\ b = d
Proof
  eq_tac >- (
    strip_tac >>
    `MAX a b = MAX c d` by
      (irule square_interval_unique >>
       qexists `pair_num a b` >>
       metis_tac[pair_num_square_bounds]) >>
    Cases_on `a < b` >> Cases_on `c < d` >>
    gvs[pair_num_def, MAX_DEF] >> decide_tac) >>
  rw[]
QED

Theorem type_key_same_src_11[local]:
  type_key (src,a) = type_key (src,b) <=> a = b
Proof
  Cases_on `src` >> simp[type_key_def] >>
  metis_tac[pair_num_same_left_11, string_to_num_inj]
QED

Theorem type_key_even_odd[local]:
  2 * m <> 2 * n + 1
Proof
  strip_tac >>
  `EVEN (2 * m)` by simp[EVEN_DOUBLE] >>
  `ODD (2 * n + 1)` by simp[GSYM ADD1, ODD_DOUBLE] >>
  metis_tac[EVEN_ODD]
QED

Theorem type_key_11[local]:
  type_key (src1,a) = type_key (src2,b) <=> src1 = src2 /\ a = b
Proof
  Cases_on `src1` >> Cases_on `src2` >> simp[type_key_def, type_key_even_odd]
  >- metis_tac[string_to_num_inj]
  >- (eq_tac >> rw[] >> gvs[] >> metis_tac[pair_num_11, string_to_num_inj])
QED

Theorem type_def_key_MEM_FlagDecl:
  MEM (FlagDecl fid members) ts ==>
  MEM ((src : num option),fid) (FLAT (MAP (type_def_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,fid)]` >> simp[] >>
  qexists `FlagDecl fid members` >>
  simp[type_def_keys_toplevel_def]
QED
Theorem type_def_key_MEM_contract_keys[local]:
  MEM (src,ts) mods /\ MEM (FlagDecl fid members) ts ==>
  MEM (src,fid) (contract_keys type_def_keys_toplevel mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (type_def_keys_toplevel src) ts)` >> simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,fid)]` >> simp[] >>
  qexists `FlagDecl fid members` >> simp[type_def_keys_toplevel_def]
QED


Theorem contract_namespaces_ok_module_type_def_keys:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods ==>
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel src) tls))
Proof
  rw[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ mods))` mp_tac >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[ALL_DISTINCT_APPEND]
QED

Theorem flag_decl_type_env_for_module:
  MEM (FlagDecl fid members) ts /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel src) ts)) ==>
  FLOOKUP (type_env_for_module src ts) (type_key (src,fid)) =
    SOME (FlagArgs (LENGTH members))
Proof
  Induct_on `ts` >- rw[type_env_for_module_def] >>
  gen_tac >> Cases_on `h` >>
  rw[type_env_for_module_def, type_def_keys_toplevel_def, FLOOKUP_UPDATE] >>
  gvs[type_env_for_module_def, type_def_keys_toplevel_def, FLOOKUP_UPDATE,
      type_key_same_src_11] >>
  metis_tac[type_def_key_MEM_FlagDecl]
QED

Theorem type_env_for_module_lookup_type_def_key[local]:
  FLOOKUP (type_env_for_module src ts) (type_key (src',id)) = SOME v ==>
  MEM (src',id) (FLAT (MAP (type_def_keys_toplevel src) ts))
Proof
  qid_spec_tac `src'` >> qid_spec_tac `id` >> qid_spec_tac `v` >>
  Induct_on `ts` >- rw[type_env_for_module_def] >>
  gen_tac >> Cases_on `h` >>
  rw[type_env_for_module_def, type_def_keys_toplevel_def, FLOOKUP_UPDATE] >>
  gvs[type_key_11]
QED

Theorem flag_decl_type_env_all_modules:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FlagDecl fid members) ts ==>
  FLOOKUP (type_env_all_modules mods) (type_key (src,fid)) =
    SOME (FlagArgs (LENGTH members))
Proof
  rw[contract_namespaces_ok_def] >>
  qpat_x_assum `ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel F) mods)` kall_tac >>
  qpat_x_assum `ALL_DISTINCT (contract_keys toplevel_vtype_keys_toplevel mods)` kall_tac >>
  qpat_x_assum `ALL_DISTINCT (contract_keys flag_member_keys_toplevel mods)` kall_tac >>
  qpat_x_assum `MEM (FlagDecl fid members) ts` mp_tac >>
  qpat_x_assum `ALOOKUP mods src = SOME ts` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP FST mods)` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (contract_keys type_def_keys_toplevel mods)` mp_tac >>
  qid_spec_tac `mods` >> qid_spec_tac `ts` >> qid_spec_tac `src` >>
  qid_spec_tac `members` >> qid_spec_tac `fid` >>
  Induct_on `mods` >- rw[contract_keys_def, type_env_all_modules_def] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[type_env_all_modules_def, contract_keys_def, ALL_DISTINCT_APPEND, FLOOKUP_FUNION] >>
  gvs[]
  >- (`FLOOKUP (type_env_for_module h0 h1) (type_key (h0,fid)) =
         SOME (FlagArgs (LENGTH members))` by
        (irule flag_decl_type_env_for_module >> simp[]) >>
      simp[]) >>
  Cases_on `FLOOKUP (type_env_for_module h0 h1) (type_key (src,fid))` >> simp[]
  >- (first_x_assum irule >> simp[contract_keys_def]) >>
  `MEM (src,fid) (FLAT (MAP (type_def_keys_toplevel h0) h1))` by
    metis_tac[type_env_for_module_lookup_type_def_key] >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  `MEM (src,fid) (contract_keys type_def_keys_toplevel mods)` by
    metis_tac[type_def_key_MEM_contract_keys] >>
  metis_tac[contract_keys_def]
QED

Theorem build_contract_type_artifact_flag_members_sound:
  contract_namespaces_ok F mods /\
  FLOOKUP (build_contract_type_artifact F mods).cta_flag_members (src,fid) = SOME members ==>
  ?ts. ALOOKUP mods src = SOME ts /\ MEM (FlagDecl fid members) ts
Proof
  rw[build_contract_type_artifact_def] >>
  drule add_contract_static_maps_flag_members_sound >> rw[] >> gvs[empty_contract_type_artifact_def] >>
  qexists `tls` >> simp[] >>
  irule ALOOKUP_ALL_DISTINCT_MEM >> gvs[contract_namespaces_ok_def] >> metis_tac[]
QED

Theorem is_bare_global_decl_MEM_Immutable[local]:
  MEM (VariableDecl vis Immutable id ty init) ts ==>
  is_bare_global_decl (string_to_num id) ts
Proof
  Induct_on `ts` >- rw[is_bare_global_decl_def] >>
  gen_tac >> Cases_on `h` >> gvs[is_bare_global_decl_def] >>
  TRY (Cases_on `v0` >> gvs[is_bare_global_decl_def]) >>
  metis_tac[]
QED

Theorem is_bare_global_decl_MEM_Constant[local]:
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  is_bare_global_decl (string_to_num id) ts
Proof
  Induct_on `ts` >- rw[is_bare_global_decl_def] >>
  gen_tac >> Cases_on `h` >> gvs[is_bare_global_decl_def] >>
  TRY (Cases_on `v0` >> gvs[is_bare_global_decl_def]) >>
  metis_tac[]
QED

Theorem is_immutable_decl_MEM[local]:
  MEM (VariableDecl vis Immutable id ty init) ts ==>
  is_immutable_decl (string_to_num id) ts
Proof
  Induct_on `ts` >- rw[is_immutable_decl_def] >>
  gen_tac >> Cases_on `h` >> gvs[is_immutable_decl_def] >>
  TRY (Cases_on `v0` >> gvs[is_immutable_decl_def]) >>
  metis_tac[]
QED

Theorem find_var_decl_by_num_NONE_not_toplevel_key[local]:
  ~MEM ((src : num option),n) (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) ==>
  find_var_decl_by_num n ts = NONE
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def])
QED

Theorem find_var_decl_by_num_NONE_not_toplevel_string_key[local]:
  ~MEM ((src : num option),string_to_num id)
      (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) ==>
  find_var_decl_by_num (string_to_num id) ts = NONE
Proof
  metis_tac[find_var_decl_by_num_NONE_not_toplevel_key]
QED

Theorem module_toplevel_vtype_key_MEM[local]:
  (MEM (VariableDecl vis mut id ty init) ts \/
   MEM (HashMapDecl vis is_transient id kt vty init2) ts) ==>
  MEM ((src : num option),string_to_num id)
    (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >-
    (qexists `[(src,string_to_num id)]` >> simp[] >>
     qexists `VariableDecl vis mut id ty init` >>
     simp[toplevel_vtype_keys_toplevel_def]) >>
  qexists `[(src,string_to_num id)]` >> simp[] >>
  qexists `HashMapDecl vis is_transient id kt vty init2` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

Theorem module_toplevel_vtype_key_MEM_Variable[local]:
  MEM (VariableDecl vis mut id ty init) ts ==>
  MEM ((src : num option),string_to_num id)
    (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,string_to_num id)]` >> simp[] >>
  qexists `VariableDecl vis mut id ty init` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED


Theorem find_var_decl_by_num_NONE_after_variable_head_key[local]:
  ALL_DISTINCT
    (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option))
       (VariableDecl vis mut id ty init :: ts))) ==>
  find_var_decl_by_num (string_to_num id) ts = NONE
Proof
  rw[] >>
  `~MEM ((src : num option),string_to_num id)
      (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    gvs[toplevel_vtype_keys_toplevel_def] >>
  metis_tac[find_var_decl_by_num_NONE_not_toplevel_string_key]
QED


Theorem distinct_toplevel_keys_no_tail_Immutable_same_id[local]:
  ALL_DISTINCT
    (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) (h::ts))) /\
  MEM (VariableDecl vis Immutable id ty init) ts /\
  MEM ((src : num option),string_to_num id)
      (toplevel_vtype_keys_toplevel src h) ==>
  F
Proof
  rpt strip_tac >>
  `MEM ((src : num option),string_to_num id)
      (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    metis_tac[module_toplevel_vtype_key_MEM_Variable] >>
  gvs[ALL_DISTINCT_APPEND]
QED


Theorem find_var_decl_by_num_NONE_Immutable[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis Immutable id ty init) ts ==>
  find_var_decl_by_num (string_to_num id) ts = NONE
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  metis_tac[find_var_decl_by_num_NONE_after_variable_head_key,
            find_var_decl_by_num_NONE_not_toplevel_string_key,
            distinct_toplevel_keys_no_tail_Immutable_same_id,
            module_toplevel_vtype_key_MEM_Variable]
QED


Theorem distinct_toplevel_keys_no_tail_Constant_same_id[local]:
  ALL_DISTINCT
    (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) (h::ts))) /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  MEM ((src : num option),string_to_num id)
      (toplevel_vtype_keys_toplevel src h) ==>
  F
Proof
  rpt strip_tac >>
  `MEM ((src : num option),string_to_num id)
      (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    metis_tac[module_toplevel_vtype_key_MEM_Variable] >>
  gvs[ALL_DISTINCT_APPEND]
QED


Theorem find_var_decl_by_num_NONE_Constant[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  find_var_decl_by_num (string_to_num id) ts = NONE
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  metis_tac[find_var_decl_by_num_NONE_after_variable_head_key,
            find_var_decl_by_num_NONE_not_toplevel_string_key,
            distinct_toplevel_keys_no_tail_Constant_same_id,
            module_toplevel_vtype_key_MEM_Variable]
QED


Theorem find_var_decl_by_num_NONE_non_storage_var[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis mut id ty init) ts /\
  (mut = Immutable \/ (?e. mut = Constant e)) ==>
  find_var_decl_by_num (string_to_num id) ts = NONE
Proof
  rw[] >-
   metis_tac[find_var_decl_by_num_NONE_Immutable] >>
  metis_tac[find_var_decl_by_num_NONE_Constant]
QED
(* The old same-source StructDecl/FlagDecl shadowing probe is intentionally not
   kept as a theorem: checked contracts now reject such collisions via
   type_def_keys_toplevel in contract_namespaces_ok. *)

(* ===== Static-map completeness bridges for contract artifacts ===== *)

Theorem check_contract_toplevel_vtypes_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  toplevel_vtypes_complete art.cta_toplevel_vtypes
    (initial_evaluation_context sources layouts tx)
Proof
  cheat
QED

Theorem check_contract_bare_globals_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  bare_globals_complete art.cta_bare_globals
    (initial_evaluation_context sources layouts tx)
Proof
  cheat
QED

Theorem check_contract_bare_global_assignable_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  bare_global_assignable_complete art.cta_bare_global_assignable
    (initial_evaluation_context sources layouts tx)
Proof
  cheat
QED

Theorem check_contract_flag_members_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  flag_members_complete art.cta_flag_members
    (initial_evaluation_context sources layouts tx)
Proof
  cheat
QED



Theorem check_contract_toplevel_decl_MEM[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM tl ts ==>
  check_toplevel_decl layouts addr mods art src tl
Proof
  rw[check_contract_def] >> gvs[] >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  `check_module layouts addr mods (build_contract_type_artifact F mods) (src,ts)` by
    metis_tac[EVERY_MEM] >>
  pop_assum mp_tac >>
  simp[check_module_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem contract_namespaces_ok_module_toplevel_vtype_keys[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))
Proof
  rw[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ mods))` mp_tac >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[ALL_DISTINCT_APPEND]
QED



Theorem check_value_type_well_formed_vtype[local]:
  !tenv vt. check_value_type tenv vt ==> well_formed_vtype tenv vt
Proof
  Induct_on `vt` >>
  rw[check_value_type_def, well_formed_vtype_def] >>
  metis_tac[assignable_type_well_formed]
QED

Theorem find_var_decl_by_num_SOME_storage_var[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis mut id ty init) ts /\
  (mut = Storage \/ mut = Transient) ==>
  find_var_decl_by_num (string_to_num id) ts =
    SOME (StorageVarDecl (mut = Transient) ty,id)
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED


Theorem find_var_decl_by_num_SOME_storage_var_Storage[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis mut id ty init) ts /\
  mut = Storage ==>
  find_var_decl_by_num (string_to_num id) ts =
    SOME (StorageVarDecl F ty,id)
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem find_var_decl_by_num_SOME_storage_var_Transient[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (VariableDecl vis mut id ty init) ts /\
  mut = Transient ==>
  find_var_decl_by_num (string_to_num id) ts =
    SOME (StorageVarDecl T ty,id)
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem find_var_decl_by_num_SOME_hashmap[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) ts)) /\
  MEM (HashMapDecl vis is_transient id kt vt init) ts ==>
  find_var_decl_by_num (string_to_num id) ts =
    SOME (HashMapVarDecl is_transient kt vt,id)
Proof
  Induct_on `ts` >- rw[find_var_decl_by_num_def] >>
  gen_tac >> Cases_on `h` >>
  rw[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >> gvs[find_var_decl_by_num_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM]
QED
(* ===== Static-map consistency bridges for contract artifacts ===== *)

Theorem check_contract_bare_globals_consistent_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  !src id ty.
    FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==>
    ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
         FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
         is_bare_global_decl id ts /\
         find_var_decl_by_num id ts = NONE /\
         ty <> NoneT
Proof
  rw[check_contract_def] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_globals_sound >> rw[]
  >- (qexists `ts` >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      conj_tac >-
       (`toplevel_vtypes_complete (build_contract_type_artifact F mods).cta_toplevel_vtypes
           (initial_evaluation_context sources layouts tx)` by
          (irule check_contract_toplevel_vtypes_complete_initial >>
           simp[check_contract_def]) >>
        gvs[toplevel_vtypes_complete_def] >>
        qpat_x_assum `!src ts vis mut id ty init. _` irule >>
        simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
      conj_tac >- metis_tac[is_bare_global_decl_MEM_Immutable] >>
      conj_tac >-
       (irule find_var_decl_by_num_NONE_non_storage_var >>
        conj_tac >-
         (qexists `src` >>
          irule contract_namespaces_ok_module_toplevel_vtype_keys >>
          metis_tac[ALOOKUP_MEM]) >>
        metis_tac[]) >>
      `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
         (VariableDecl vis Immutable id_str ty init)` by
        (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >>
         metis_tac[]) >>
      gvs[check_toplevel_decl_def] >>
      metis_tac[assignable_type_not_NoneT]) >>
  qexists `ts` >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  conj_tac >-
   (`toplevel_vtypes_complete (build_contract_type_artifact F mods).cta_toplevel_vtypes
       (initial_evaluation_context sources layouts tx)` by
      (irule check_contract_toplevel_vtypes_complete_initial >>
       simp[check_contract_def]) >>
    gvs[toplevel_vtypes_complete_def] >>
        qpat_x_assum `!src ts vis mut id ty init. _` irule >>
        simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[is_bare_global_decl_MEM_Constant] >>
  conj_tac >-
   (irule find_var_decl_by_num_NONE_non_storage_var >>
    conj_tac >-
     (qexists `src` >>
      irule contract_namespaces_ok_module_toplevel_vtype_keys >>
      metis_tac[ALOOKUP_MEM]) >>
    metis_tac[]) >>
  `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
     (VariableDecl vis (Constant e) id_str ty init)` by
    (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >>
     metis_tac[]) >>
  gvs[check_toplevel_decl_def] >>
  metis_tac[assignable_type_not_NoneT]
QED

Theorem check_contract_bare_global_assignable_consistent_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  !src id ty.
    FLOOKUP art.cta_bare_global_assignable (src,id) = SOME ty ==>
    ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
         FLOOKUP art.cta_bare_globals (src,id) = SOME ty /\
         FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
         is_immutable_decl id ts /\
         find_var_decl_by_num id ts = NONE /\
         ty <> NoneT
Proof
  rw[check_contract_def] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >> rw[] >>
  qexists `ts` >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  conj_tac >-
   (`bare_globals_complete (build_contract_type_artifact F mods).cta_bare_globals
       (initial_evaluation_context sources layouts tx)` by
      (irule check_contract_bare_globals_complete_initial >> simp[check_contract_def]) >>
    gvs[bare_globals_complete_def] >>
    qpat_x_assum `!src ts vis mut id ty init. _` irule >>
    simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
  conj_tac >-
   (`toplevel_vtypes_complete (build_contract_type_artifact F mods).cta_toplevel_vtypes
       (initial_evaluation_context sources layouts tx)` by
      (irule check_contract_toplevel_vtypes_complete_initial >> simp[check_contract_def]) >>
    gvs[toplevel_vtypes_complete_def] >>
    qpat_x_assum `!src ts vis mut id ty init. _` irule >>
    simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[is_immutable_decl_MEM] >>
  conj_tac >-
   (irule find_var_decl_by_num_NONE_non_storage_var >>
    conj_tac >-
     (qexists `src` >>
      irule contract_namespaces_ok_module_toplevel_vtype_keys >>
      metis_tac[ALOOKUP_MEM]) >>
    metis_tac[]) >>
  `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
     (VariableDecl vis Immutable id_str ty init)` by
    (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >>
     metis_tac[]) >>
  gvs[check_toplevel_decl_def] >>
  metis_tac[assignable_type_not_NoneT]
QED

Theorem check_contract_toplevel_vtypes_consistent_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  (!src id vt.
     FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME vt ==>
     well_formed_vtype (type_env_all_modules mods) vt) /\
  (!src id ty.
     FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
     FLOOKUP art.cta_bare_globals (src,id) = NONE ==>
     ?ts is_transient typ id_str.
       get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
       find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
       typ = ty /\
       IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
       IS_SOME (lookup_var_slot_from_layout
         (initial_evaluation_context sources layouts tx) is_transient src id_str)) /\
  (!src id kt vt.
     FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
     ?ts is_transient id_str.
       get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
       find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
       IS_SOME (lookup_var_slot_from_layout
         (initial_evaluation_context sources layouts tx) is_transient src id_str))
Proof
  rw[check_contract_def] >> gvs[] >> rpt conj_tac
  >- (rpt strip_tac >>
      drule_all build_contract_type_artifact_toplevel_vtypes_sound >> rw[]
      >- (`check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
             (VariableDecl vis mut id_str ty init)` by
            (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >> metis_tac[]) >>
          Cases_on `mut` >> gvs[check_toplevel_decl_def, well_formed_vtype_def] >>
          metis_tac[assignable_type_well_formed]) >>
      `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
         (HashMapDecl vis is_transient id_str kt vty init)` by
        (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >> metis_tac[]) >>
      gvs[check_toplevel_decl_def, well_formed_vtype_def] >>
      metis_tac[check_value_type_well_formed_vtype])
  >- (rpt strip_tac >>
      drule_all build_contract_type_artifact_toplevel_vtypes_sound >> rw[] >> gvs[] >>
      `mut = Storage \/ mut = Transient` by
        (Cases_on `mut` >> gvs[]
         >- (`bare_globals_complete (build_contract_type_artifact F mods).cta_bare_globals
                (initial_evaluation_context sources layouts tx)` by
               (irule check_contract_bare_globals_complete_initial >> simp[check_contract_def]) >>
             gvs[bare_globals_complete_def] >>
             qpat_x_assum `!src ts vis mut id ty init. _`
               (qspecl_then [`src`,`ts`,`vis`,`Constant e`,`id_str`,`ty`,`init`] mp_tac) >>
             simp[get_module_code_def, initial_evaluation_context_def]) >>
         `bare_globals_complete (build_contract_type_artifact F mods).cta_bare_globals
            (initial_evaluation_context sources layouts tx)` by
           (irule check_contract_bare_globals_complete_initial >> simp[check_contract_def]) >>
         gvs[bare_globals_complete_def] >>
         qpat_x_assum `!src ts vis mut id ty init. _`
           (qspecl_then [`src`,`ts`,`vis`,`Immutable`,`id_str`,`ty`,`init`] mp_tac) >>
         simp[get_module_code_def, initial_evaluation_context_def]) >>
      qexistsl [`ts`,`mut = Transient`,`id_str`] >>
      simp[get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def] >>
      conj_tac >-
       metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
                 find_var_decl_by_num_SOME_storage_var_Transient,
                 contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
      `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
         (VariableDecl vis mut id_str ty init)` by
        (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >> metis_tac[]) >>
      Cases_on `mut` >>
      gvs[check_toplevel_decl_def,
          lookup_var_slot_in_layouts_def, lookup_var_slot_from_layout_def] >>
      metis_tac[assignable_type_well_formed, well_formed_type_def,
                find_var_decl_by_num_SOME_storage_var_Storage,
                find_var_decl_by_num_SOME_storage_var_Transient,
                contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM]) >>
  rpt strip_tac >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >> rw[] >> gvs[] >>
  qexistsl [`ts`,`is_transient`,`id_str`] >>
  simp[get_module_code_def, initial_evaluation_context_def,
       lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def] >>
  conj_tac >-
   metis_tac[find_var_decl_by_num_SOME_hashmap,
             contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `check_toplevel_decl layouts tx.target mods (build_contract_type_artifact F mods) src
     (HashMapDecl vis is_transient id_str kt vt init)` by
    (irule check_contract_toplevel_decl_MEM >> simp[check_contract_def] >> metis_tac[]) >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def,
      lookup_var_slot_from_layout_def]
QED

Theorem check_contract_flag_members_consistent_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  !src fid ls.
    FLOOKUP art.cta_flag_members (src,fid) = SOME ls ==>
    ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
         lookup_flag fid ts = SOME ls /\
         FLOOKUP (type_env_all_modules mods) (type_key (src,fid)) =
           SOME (FlagArgs (LENGTH ls))
Proof
  rw[check_contract_def] >> gvs[] >>
  drule_all build_contract_type_artifact_flag_members_sound >> rw[] >>
  qexists `ts` >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  conj_tac >-
   (irule lookup_flag_MEM_FlagDecl >>
    conj_tac >-
     (qexists `src` >> irule contract_namespaces_ok_module_flag_member_keys >>
      metis_tac[ALOOKUP_MEM]) >>
    simp[]) >>
  metis_tac[flag_decl_type_env_all_modules]
QED

(* ===== Env-context bridge for initial contexts ===== *)

Theorem check_contract_env_context_consistent_initial_NONE:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods NONE)
    (initial_evaluation_context sources layouts tx)
Proof
  rw[env_context_consistent_def, artifact_env_def]
  >- simp[get_tenv_def, initial_evaluation_context_def]
  >- simp[current_module_def, initial_evaluation_context_def]
  >- (irule check_contract_fn_sigs_consistent_initial >> simp[])
  >- (irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (irule check_contract_bare_globals_complete_initial >> simp[])
  >- (irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (irule check_contract_flag_members_complete_initial >> simp[])
  >- metis_tac[check_contract_bare_globals_consistent_initial]
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`src`,`id`,`ty`] mp_tac) >> simp[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def])
QED

Theorem get_tenv_stk[local]:
  !cx stk. get_tenv (cx with stk := stk) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk[local]:
  !cx stk src. get_module_code (cx with stk := stk) src = get_module_code cx src
Proof
  simp[get_module_code_def]
QED

Theorem lookup_var_slot_from_layout_stk[local]:
  !cx stk is_transient src id.
    lookup_var_slot_from_layout (cx with stk := stk) is_transient src id =
    lookup_var_slot_from_layout cx is_transient src id
Proof
  simp[lookup_var_slot_from_layout_def]
QED

Theorem fn_sigs_consistent_stk[local]:
  !sigs cx stk.
    fn_sigs_consistent sigs (cx with stk := stk) <=> fn_sigs_consistent sigs cx
Proof
  simp[fn_sigs_consistent_def, get_module_code_stk]
QED

Theorem fn_sigs_complete_stk[local]:
  !sigs cx stk.
    fn_sigs_complete sigs (cx with stk := stk) <=> fn_sigs_complete sigs cx
Proof
  simp[fn_sigs_complete_def, get_module_code_stk]
QED

Theorem toplevel_vtypes_complete_stk[local]:
  !m cx stk.
    toplevel_vtypes_complete m (cx with stk := stk) <=>
    toplevel_vtypes_complete m cx
Proof
  simp[toplevel_vtypes_complete_def, get_module_code_stk]
QED

Theorem bare_globals_complete_stk[local]:
  !m cx stk.
    bare_globals_complete m (cx with stk := stk) <=> bare_globals_complete m cx
Proof
  simp[bare_globals_complete_def, get_module_code_stk]
QED

Theorem bare_global_assignable_complete_stk[local]:
  !m cx stk.
    bare_global_assignable_complete m (cx with stk := stk) <=>
    bare_global_assignable_complete m cx
Proof
  simp[bare_global_assignable_complete_def, get_module_code_stk]
QED

Theorem flag_members_complete_stk[local]:
  !m cx stk.
    flag_members_complete m (cx with stk := stk) <=> flag_members_complete m cx
Proof
  simp[flag_members_complete_def, get_module_code_stk]
QED

Theorem check_contract_env_context_consistent_initial_with_current_src:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods src)
    ((initial_evaluation_context sources layouts tx) with stk := [(src, fn)])
Proof
  rw[env_context_consistent_def, artifact_env_def]
  >- simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def]
  >- simp[current_module_def]
  >- (simp[fn_sigs_consistent_stk] >>
      irule check_contract_fn_sigs_consistent_initial >> simp[])
  >- (simp[fn_sigs_complete_stk] >>
      irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (simp[toplevel_vtypes_complete_stk] >>
      irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (simp[bare_globals_complete_stk] >>
      irule check_contract_bare_globals_complete_initial >> simp[])
  >- (simp[bare_global_assignable_complete_stk] >>
      irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (simp[flag_members_complete_stk] >>
      irule check_contract_flag_members_complete_initial >> simp[])
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_stk])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_stk])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk, lookup_var_slot_from_layout_stk] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_stk, lookup_var_slot_from_layout_stk] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk])
QED

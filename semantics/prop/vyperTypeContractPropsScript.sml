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
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeInitialState
Libs
  wordsLib

val _ = Parse.hide "body";

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


Theorem add_toplevel_static_maps_toplevel_vtypes_complete_Variable[local]:
  FLOOKUP (add_toplevel_static_maps F src (VariableDecl vis mut id ty init) art).cta_toplevel_vtypes
    (src,string_to_num id) = SOME (Type ty)
Proof
  Cases_on `mut` >> rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_toplevel_vtypes_complete_HashMap[local]:
  FLOOKUP (add_toplevel_static_maps F src (HashMapDecl vis is_transient id kt vt init) art).cta_toplevel_vtypes
    (src,string_to_num id) = SOME (HashMapT kt vt)
Proof
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_toplevel_vtypes_preserve[local]:
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt /\
  ~(MEM k (toplevel_vtype_keys_toplevel src tl)) ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_toplevel_vtypes k = SOME vt
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE])
QED

Theorem add_module_static_maps_toplevel_vtypes_preserve[local]:
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt /\
  ~(MEM k (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))) ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_toplevel_vtypes k = SOME vt
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` irule) >>
  simp[] >>
  irule add_toplevel_static_maps_toplevel_vtypes_preserve >>
  simp[]
QED

Theorem add_module_static_maps_toplevel_vtypes_complete_Variable[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) tls)) /\
  MEM (VariableDecl vis mut id ty init) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_toplevel_vtypes (src,string_to_num id) = SOME (Type ty)
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_toplevel_vtypes_preserve >>
     simp[add_toplevel_static_maps_toplevel_vtypes_complete_Variable] >>
     gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_toplevel_vtypes_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_module_static_maps_toplevel_vtypes_complete_HashMap[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) tls)) /\
  MEM (HashMapDecl vis is_transient id kt vt init) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_toplevel_vtypes (src,string_to_num id) = SOME (HashMapT kt vt)
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_toplevel_vtypes_preserve >>
     simp[add_toplevel_static_maps_toplevel_vtypes_complete_HashMap] >>
     gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_toplevel_vtypes_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_toplevel_vtype_key_MEM]
QED

Theorem add_contract_static_maps_toplevel_vtypes_preserve[local]:
  FLOOKUP art.cta_toplevel_vtypes k = SOME vt /\
  ~(MEM k (contract_keys toplevel_vtype_keys_toplevel mods)) ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_toplevel_vtypes k = SOME vt
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[contract_keys_def] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` irule) >>
  conj_tac >- simp[contract_keys_def] >>
  irule add_module_static_maps_toplevel_vtypes_preserve >>
  simp[]
QED

Theorem add_contract_static_maps_toplevel_vtypes_complete_MEM_Variable[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (VariableDecl vis mut id ty init) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_toplevel_vtypes
    (src,string_to_num id) = SOME (Type ty)
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_toplevel_vtypes_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_toplevel_vtype_key_MEM_Variable]) >>
     irule add_module_static_maps_toplevel_vtypes_complete_Variable >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_toplevel_vtypes_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_contract_static_maps_toplevel_vtypes_complete_MEM_HashMap[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (HashMapDecl vis is_transient id kt vt init) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_toplevel_vtypes
    (src,string_to_num id) = SOME (HashMapT kt vt)
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_toplevel_vtypes_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_toplevel_vtype_key_MEM]) >>
     irule add_module_static_maps_toplevel_vtypes_complete_HashMap >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_toplevel_vtypes_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM]
QED

Theorem build_contract_type_artifact_toplevel_vtypes_complete[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  ((?vis mut id ty init. MEM (VariableDecl vis mut id ty init) ts /\
      k = (src,string_to_num id) /\ vt = Type ty) \/
   (?vis is_transient id kt vty init. MEM (HashMapDecl vis is_transient id kt vty init) ts /\
      k = (src,string_to_num id) /\ vt = HashMapT kt vty)) ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes k = SOME vt
Proof
  rw[build_contract_type_artifact_def] >>
  drule ALOOKUP_MEM >> strip_tac >> gvs[] >-
    metis_tac[add_contract_static_maps_toplevel_vtypes_complete_MEM_Variable] >>
  metis_tac[add_contract_static_maps_toplevel_vtypes_complete_MEM_HashMap]
QED

Theorem add_toplevel_static_maps_bare_globals_complete_Immutable[local]:
  FLOOKUP (add_toplevel_static_maps F src (VariableDecl vis Immutable id ty init) art).cta_bare_globals
    (src,string_to_num id) = SOME ty
Proof
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_bare_globals_complete_Constant[local]:
  FLOOKUP (add_toplevel_static_maps F src (VariableDecl vis (Constant e) id ty init) art).cta_bare_globals
    (src,string_to_num id) = SOME ty
Proof
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_bare_globals_preserve[local]:
  FLOOKUP art.cta_bare_globals k = SOME ty /\
  ~(MEM k (toplevel_vtype_keys_toplevel src tl)) ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_bare_globals k = SOME ty
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE])
QED

Theorem add_module_static_maps_bare_globals_preserve[local]:
  FLOOKUP art.cta_bare_globals k = SOME ty /\
  ~(MEM k (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))) ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_globals k = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` irule) >>
  simp[] >>
  irule add_toplevel_static_maps_bare_globals_preserve >>
  simp[]
QED

Theorem add_module_static_maps_bare_globals_complete_Immutable[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) tls)) /\
  MEM (VariableDecl vis Immutable id ty init) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_globals (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_bare_globals_preserve >>
     simp[add_toplevel_static_maps_bare_globals_complete_Immutable] >>
     gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_bare_globals_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_module_static_maps_bare_globals_complete_Constant[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) tls)) /\
  MEM (VariableDecl vis (Constant e) id ty init) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_globals (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_bare_globals_preserve >>
     simp[add_toplevel_static_maps_bare_globals_complete_Constant] >>
     gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_bare_globals_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_contract_static_maps_bare_globals_preserve[local]:
  FLOOKUP art.cta_bare_globals k = SOME ty /\
  ~(MEM k (contract_keys toplevel_vtype_keys_toplevel mods)) ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_globals k = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[contract_keys_def] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` irule) >>
  conj_tac >- simp[contract_keys_def] >>
  irule add_module_static_maps_bare_globals_preserve >>
  simp[]
QED

Theorem add_contract_static_maps_bare_globals_complete_MEM_Immutable[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (VariableDecl vis Immutable id ty init) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_globals
    (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_bare_globals_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_toplevel_vtype_key_MEM_Variable]) >>
     irule add_module_static_maps_bare_globals_complete_Immutable >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_bare_globals_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_contract_static_maps_bare_globals_complete_MEM_Constant[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (VariableDecl vis (Constant e) id ty init) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_globals
    (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_bare_globals_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_toplevel_vtype_key_MEM_Variable]) >>
     irule add_module_static_maps_bare_globals_complete_Constant >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_bare_globals_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem build_contract_type_artifact_bare_globals_complete[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis mut id ty init) ts /\
  (mut = Immutable \/ ?e. mut = Constant e) ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
    (src,string_to_num id) = SOME ty
Proof
  rw[build_contract_type_artifact_def] >>
  drule ALOOKUP_MEM >> strip_tac >> gvs[] >-
    metis_tac[add_contract_static_maps_bare_globals_complete_MEM_Immutable] >>
  metis_tac[add_contract_static_maps_bare_globals_complete_MEM_Constant]
QED

Theorem add_toplevel_static_maps_bare_global_assignable_complete_Immutable[local]:
  FLOOKUP (add_toplevel_static_maps F src (VariableDecl vis Immutable id ty init) art).cta_bare_global_assignable
    (src,string_to_num id) = SOME ty
Proof
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_bare_global_assignable_preserve[local]:
  FLOOKUP art.cta_bare_global_assignable k = SOME ty /\
  ~(MEM k (toplevel_vtype_keys_toplevel src tl)) ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_bare_global_assignable k = SOME ty
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, toplevel_vtype_keys_toplevel_def, FLOOKUP_UPDATE])
QED

Theorem add_module_static_maps_bare_global_assignable_preserve[local]:
  FLOOKUP art.cta_bare_global_assignable k = SOME ty /\
  ~(MEM k (FLAT (MAP (toplevel_vtype_keys_toplevel src) tls))) ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_global_assignable k = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` irule) >>
  simp[] >>
  irule add_toplevel_static_maps_bare_global_assignable_preserve >>
  simp[]
QED

Theorem add_module_static_maps_bare_global_assignable_complete_Immutable[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src : num option)) tls)) /\
  MEM (VariableDecl vis Immutable id ty init) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_bare_global_assignable (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_bare_global_assignable_preserve >>
     simp[add_toplevel_static_maps_bare_global_assignable_complete_Immutable] >>
     gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_bare_global_assignable_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem add_contract_static_maps_bare_global_assignable_preserve[local]:
  FLOOKUP art.cta_bare_global_assignable k = SOME ty /\
  ~(MEM k (contract_keys toplevel_vtype_keys_toplevel mods)) ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_global_assignable k = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[contract_keys_def] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` irule) >>
  conj_tac >- simp[contract_keys_def] >>
  irule add_module_static_maps_bare_global_assignable_preserve >>
  simp[]
QED

Theorem add_contract_static_maps_bare_global_assignable_complete_MEM_Immutable[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (VariableDecl vis Immutable id ty init) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_bare_global_assignable
    (src,string_to_num id) = SOME ty
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_bare_global_assignable_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[module_toplevel_vtype_key_MEM_Variable]) >>
     irule add_module_static_maps_bare_global_assignable_complete_Immutable >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_bare_global_assignable_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED

Theorem build_contract_type_artifact_bare_global_assignable_complete[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis Immutable id ty init) ts ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_bare_global_assignable
    (src,string_to_num id) = SOME ty
Proof
  rw[build_contract_type_artifact_def] >>
  drule ALOOKUP_MEM >> strip_tac >> gvs[] >>
  metis_tac[add_contract_static_maps_bare_global_assignable_complete_MEM_Immutable]
QED
(* ===== Static-map completeness bridges for contract artifacts ===== *)

Theorem check_contract_toplevel_vtypes_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  toplevel_vtypes_complete art.cta_toplevel_vtypes
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, toplevel_vtypes_complete_def] >> gvs[] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  irule build_contract_type_artifact_toplevel_vtypes_complete >>
  simp[] >> metis_tac[]
QED

Theorem check_contract_bare_globals_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  bare_globals_complete art.cta_bare_globals
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, bare_globals_complete_def] >> gvs[] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  irule build_contract_type_artifact_bare_globals_complete >>
  simp[] >> metis_tac[]
QED

Theorem check_contract_bare_global_assignable_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  bare_global_assignable_complete art.cta_bare_global_assignable
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, bare_global_assignable_complete_def] >> gvs[] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  irule build_contract_type_artifact_bare_global_assignable_complete >>
  simp[] >> metis_tac[]
QED

Theorem lookup_flag_SOME_MEM_FlagDecl[local]:
  lookup_flag fid ts = SOME members ==>
  MEM (FlagDecl fid members) ts
Proof
  Induct_on `ts` >- rw[lookup_flag_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_flag_def] >>
  gvs[AllCaseEqs()]
QED

Theorem add_toplevel_static_maps_flag_members_complete[local]:
  FLOOKUP (add_toplevel_static_maps F src (FlagDecl fid members) art).cta_flag_members
    (src,fid) = SOME members
Proof
  rw[add_toplevel_static_maps_def, FLOOKUP_UPDATE]
QED

Theorem add_toplevel_static_maps_flag_members_preserve[local]:
  FLOOKUP art.cta_flag_members k = SOME members /\
  ~(MEM k (flag_member_keys_toplevel src tl)) ==>
  FLOOKUP (add_toplevel_static_maps F src tl art).cta_flag_members k = SOME members
Proof
  Cases_on `tl` >>
  rw[add_toplevel_static_maps_def, flag_member_keys_toplevel_def, FLOOKUP_UPDATE] >>
  TRY (Cases_on `v0` >> gvs[add_toplevel_static_maps_def, flag_member_keys_toplevel_def, FLOOKUP_UPDATE])
QED

Theorem add_module_static_maps_flag_members_preserve[local]:
  FLOOKUP art.cta_flag_members k = SOME members /\
  ~(MEM k (FLAT (MAP (flag_member_keys_toplevel src) tls))) ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_flag_members k = SOME members
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  rw[add_module_static_maps_def] >>
  simp[GSYM add_module_static_maps_def] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` irule) >>
  simp[] >>
  irule add_toplevel_static_maps_flag_members_preserve >>
  simp[]
QED

Theorem add_module_static_maps_flag_members_complete[local]:
  ALL_DISTINCT (FLAT (MAP (flag_member_keys_toplevel (src : num option)) tls)) /\
  MEM (FlagDecl fid members) tls ==>
  FLOOKUP (add_module_static_maps F src tls art).cta_flag_members (src,fid) = SOME members
Proof
  qid_spec_tac `art` >>
  Induct_on `tls` >- rw[add_module_static_maps_def] >>
  gen_tac >> rw[add_module_static_maps_def] >> gvs[] >-
    (simp[GSYM add_module_static_maps_def] >>
     irule add_module_static_maps_flag_members_preserve >>
     simp[add_toplevel_static_maps_flag_members_complete] >>
     gvs[ALL_DISTINCT_APPEND, flag_member_keys_toplevel_def]) >>
  gvs[ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `add_toplevel_static_maps F src h art` mp_tac) >>
  simp[add_module_static_maps_def] >> strip_tac >>
  irule add_toplevel_static_maps_flag_members_preserve >>
  simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[flag_member_key_MEM]
QED

Theorem add_contract_static_maps_flag_members_preserve[local]:
  FLOOKUP art.cta_flag_members k = SOME members /\
  ~(MEM k (contract_keys flag_member_keys_toplevel mods)) ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_flag_members k = SOME members
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[contract_keys_def] >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` irule) >>
  conj_tac >- simp[contract_keys_def] >>
  irule add_module_static_maps_flag_members_preserve >>
  simp[]
QED

Theorem add_contract_static_maps_flag_members_complete_MEM[local]:
  contract_namespaces_ok F mods /\ MEM (src,tls) mods /\
  MEM (FlagDecl fid members) tls ==>
  FLOOKUP (FOLDL (\art (src,tls). add_module_static_maps F src tls art) art mods).cta_flag_members
    (src,fid) = SOME members
Proof
  qid_spec_tac `art` >>
  Induct_on `mods` >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[] >-
    (irule add_contract_static_maps_flag_members_preserve >>
     conj_tac >-
       (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
        metis_tac[flag_member_key_MEM]) >>
     irule add_module_static_maps_flag_members_complete >>
     gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  first_x_assum (qspec_then `add_module_static_maps F h0 h1 art` mp_tac) >>
  impl_tac >-
    (gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND]) >>
  simp[] >> strip_tac >>
  irule add_module_static_maps_flag_members_preserve >>
  simp[] >>
  gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  metis_tac[flag_member_key_MEM]
QED

Theorem build_contract_type_artifact_flag_members_complete[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FlagDecl fid members) ts ==>
  FLOOKUP (build_contract_type_artifact F mods).cta_flag_members
    (src,fid) = SOME members
Proof
  rw[build_contract_type_artifact_def] >>
  drule ALOOKUP_MEM >> strip_tac >> gvs[] >>
  metis_tac[add_contract_static_maps_flag_members_complete_MEM]
QED

Theorem check_contract_flag_members_complete_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  flag_members_complete art.cta_flag_members
    (initial_evaluation_context sources layouts tx)
Proof
  rw[check_contract_def, flag_members_complete_def] >> gvs[] >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  drule lookup_flag_SOME_MEM_FlagDecl >> strip_tac >>
  irule build_contract_type_artifact_flag_members_complete >>
  simp[] >> metis_tac[]
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

(* ===== Function-body bridge for checked contracts ===== *)

Theorem check_contract_toplevel_body_MEM[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM tl ts ==>
  check_toplevel_body layouts addr mods art src tl
Proof
  rw[check_contract_def] >> gvs[] >>
  `MEM (src,ts) mods` by metis_tac[ALOOKUP_MEM] >>
  `check_module layouts addr mods (build_contract_type_artifact F mods) (src,ts)` by
    metis_tac[EVERY_MEM] >>
  pop_assum mp_tac >>
  simp[check_module_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem check_contract_function_body_MEM[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
  check_function_body layouts addr mods art src mut nr args dflts ret body
Proof
  rw[] >>
  drule_all check_contract_toplevel_body_MEM >>
  simp[check_toplevel_body_def]
QED

Theorem FOLDL_extend_local_args_not_mem[local]:
  !args (base : typing_env) n.
    ~MEM n (MAP (string_to_num o FST) args) ==>
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types n =
      FLOOKUP base.var_types n /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable n =
      FLOOKUP base.var_assignable n
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[extend_local_def] >>
  qpat_x_assum `!base n. _` (qspecl_then [`extend_local base' (string_to_num h0) h1 T`,`n`] mp_tac) >>
  simp[extend_local_def, FLOOKUP_UPDATE]
QED

Theorem FOLDL_extend_local_args_formal_lookup[local]:
  !args (base : typing_env) id typ.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    MEM (id,typ) args ==>
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types
      (string_to_num id) = SOME typ /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable
      (string_to_num id) = SOME T
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def, FLOOKUP_UPDATE] >-
    (qspecl_then [`args`,`extend_local base' (string_to_num h0) h1 T`,`string_to_num h0`]
       mp_tac FOLDL_extend_local_args_not_mem >>
     simp[extend_local_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[]) >-
    (qspecl_then [`args`,`extend_local base' (string_to_num h0) h1 T`,`string_to_num h0`]
       mp_tac FOLDL_extend_local_args_not_mem >>
     simp[extend_local_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `!base id typ. _`
    (qspecl_then [`extend_local base' (string_to_num h0) h1 T`,`id`,`typ`] mp_tac) >>
  simp[extend_local_def]
QED

Theorem FOLDL_extend_local_args_var_types_range[local]:
  !args (base : typing_env) n ty.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_types n = SOME ty ==>
    FLOOKUP base.var_types n = SOME ty \/
    ?id. MEM (id,ty) args /\ n = string_to_num id
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def] >>
  last_x_assum drule >>
  simp[extend_local_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `string_to_num h0 = n` >> gvs[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_var_assignable_range[local]:
  !args (base : typing_env) n b.
    ALL_DISTINCT (MAP (string_to_num o FST) args) /\
    FLOOKUP (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).var_assignable n = SOME b ==>
    FLOOKUP base.var_assignable n = SOME b \/
    ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T
Proof
  Induct >- rw[] >>
  gen_tac >> PairCases_on `h` >> rw[] >> gvs[extend_local_def] >>
  last_x_assum drule >>
  simp[extend_local_def, FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `string_to_num h0 = n` >> gvs[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_lookup[local]:
  !args (base : typing_env) env.
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  env = FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args /\
  base.var_types = FEMPTY /\ base.var_assignable = FEMPTY ==>
  (!id typ. MEM (id,typ) args ==>
     FLOOKUP env.var_types (string_to_num id) = SOME typ /\
     FLOOKUP env.var_assignable (string_to_num id) = SOME T) /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
     ?id. MEM (id,ty) args /\ n = string_to_num id) /\
  (!n b. FLOOKUP env.var_assignable n = SOME b ==>
     ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  rw[] >-
    (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_formal_lookup >> simp[])
  >- (drule_all FOLDL_extend_local_args_var_types_range >> rw[] >> gvs[])
  >- (drule_all FOLDL_extend_local_args_var_assignable_range >> rw[] >> gvs[])
QED

Theorem FOLDL_extend_local_args_static[local]:
  !args (base : typing_env).
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).current_src = base.current_src /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).bare_globals = base.bare_globals /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).bare_global_assignable = base.bare_global_assignable /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).toplevel_vtypes = base.toplevel_vtypes /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).type_defs = base.type_defs /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).fn_sigs = base.fn_sigs /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base args).flag_members = base.flag_members
Proof
  Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[extend_local_def]
QED

Theorem artifact_fn_sigs_lookup_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx) /\
  FLOOKUP (function_entry_env art mods src args).fn_sigs k = SOME sig ==>
  FLOOKUP fn_sigs k = SOME sig
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_fn_sigs_sound >> rw[] >>
  Cases_on `sig` >>
  gvs[fn_sigs_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  first_x_assum drule >> disch_then drule >> simp[fn_sig_component_equality]
QED

Theorem artifact_bare_globals_lookup_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx) /\
  FLOOKUP (function_entry_env art mods src args).bare_globals k = SOME ty ==>
  FLOOKUP bare_globals k = SOME ty
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_globals_sound >> rw[] >>
  gvs[bare_globals_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_bare_global_assignable_lookup_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx) /\
  FLOOKUP (function_entry_env art mods src args).bare_global_assignable k = SOME ty ==>
  FLOOKUP bare_global_assignable k = SOME ty
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_bare_global_assignable_sound >> rw[] >>
  gvs[bare_global_assignable_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_toplevel_vtypes_lookup_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx) /\
  FLOOKUP (function_entry_env art mods src args).toplevel_vtypes k = SOME vt ==>
  FLOOKUP toplevel_vtypes k = SOME vt
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >> rw[] >>
  gvs[toplevel_vtypes_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem artifact_flag_members_lookup_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx) /\
  FLOOKUP (function_entry_env art mods src args).flag_members k = SOME members ==>
  FLOOKUP flag_members k = SOME members
Proof
  PairCases_on `k` >>
  rw[function_entry_env_def, artifact_env_def, check_contract_def, FOLDL_extend_local_args_static] >> gvs[] >>
  drule_all build_contract_type_artifact_flag_members_sound >> rw[] >>
  gvs[flag_members_complete_def, get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[lookup_flag_MEM_FlagDecl, contract_namespaces_ok_module_flag_member_keys, ALOOKUP_MEM]
QED

Theorem artifact_toplevel_non_bare_globals_NONE_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\ tx.target = addr /\
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  FLOOKUP (function_entry_env art mods entry_src args).toplevel_vtypes (src,id) = SOME vt /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_globals (src,id) = NONE ==>
  FLOOKUP bare_globals (src,id) = NONE
Proof
  rw[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static] >>
  Cases_on `FLOOKUP bare_globals (src,id)` >> simp[] >>
  rename1 `FLOOKUP bare_globals (src,id) = SOME bare_ty` >>
  first_x_assum drule >>
  simp[get_module_code_def, initial_evaluation_context_def] >>
  strip_tac >> gvs[] >>
  gvs[check_contract_def] >>
  drule_all build_contract_type_artifact_toplevel_vtypes_sound >>
  strip_tac >> gvs[] >-
   (Cases_on `mut` >> gvs[] >-
     (rw[] >>
      `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
         (src,string_to_num id_str) = SOME ty` by
        (irule build_contract_type_artifact_bare_globals_complete >> simp[] >> metis_tac[]) >>
      gvs[]) >-
     (rw[] >>
      `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
         (src,string_to_num id_str) = SOME ty` by
        (irule build_contract_type_artifact_bare_globals_complete >> simp[] >> metis_tac[]) >>
      gvs[]) >-
     (rw[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
      `find_var_decl_by_num (string_to_num id_str) ts =
         SOME (StorageVarDecl T ty,id_str)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient] >>
      gvs[]) >>
     rw[] >>
     `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
     `find_var_decl_by_num (string_to_num id_str) ts =
        SOME (StorageVarDecl F ty,id_str)` by
       metis_tac[find_var_decl_by_num_SOME_storage_var_Storage] >>
     gvs[]) >>
  rw[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
     metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys, ALOOKUP_MEM] >>
  `find_var_decl_by_num (string_to_num id_str) ts =
     SOME (HashMapVarDecl is_transient kt vty,id_str)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  gvs[]
QED
Theorem well_typed_static_maps_transfer[local]:
  (!env1 e. well_typed_expr env1 e ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_expr env2 e) /\
  (!env1 e vt. type_place_expr env1 e = SOME vt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    type_place_expr env2 e = SOME vt) /\
  (!env1 tgt vt. type_place_target env1 tgt = SOME vt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    type_place_target env2 tgt = SOME vt) /\
  (!env1 es. well_typed_exprs env1 es ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_exprs env2 es) /\
  (!env1 opt. well_typed_opt env1 opt ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_opt env2 opt) /\
  (!env1 kes. well_typed_named_exprs env1 kes ==> !env2.
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
    well_typed_named_exprs env2 kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >>
  rw[well_typed_expr_def, AllCaseEqs()] >>
  gvs[] >>
  metis_tac[]
QED
Definition static_maps_transfer_env_def:
  static_maps_transfer_env env1 env2 <=>
    env2.current_src = env1.current_src /\
    env2.type_defs = env1.type_defs /\
    env2.var_types = env1.var_types /\
    env2.var_assignable = env1.var_assignable /\
    (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==>
       FLOOKUP env2.fn_sigs k = SOME sig) /\
    (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==>
       FLOOKUP env2.bare_globals k = SOME ty) /\
    (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==>
       FLOOKUP env2.bare_global_assignable k = SOME ty) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==>
       FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
    (!k members. FLOOKUP env1.flag_members k = SOME members ==>
       FLOOKUP env2.flag_members k = SOME members) /\
    (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\
            FLOOKUP env1.bare_globals k = NONE ==>
       FLOOKUP env2.bare_globals k = NONE)
End
Theorem well_typed_defaults_static_maps_transfer[local]:
  well_typed_exprs (defaults_env env1) dflts /\
  env2.current_src = env1.current_src /\
  env2.type_defs = env1.type_defs /\
  (!k sig. FLOOKUP env1.fn_sigs k = SOME sig ==> FLOOKUP env2.fn_sigs k = SOME sig) /\
  (!k ty. FLOOKUP env1.bare_globals k = SOME ty ==> FLOOKUP env2.bare_globals k = SOME ty) /\
  (!k ty. FLOOKUP env1.bare_global_assignable k = SOME ty ==> FLOOKUP env2.bare_global_assignable k = SOME ty) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt ==> FLOOKUP env2.toplevel_vtypes k = SOME vt) /\
  (!k members. FLOOKUP env1.flag_members k = SOME members ==> FLOOKUP env2.flag_members k = SOME members) /\
  (!k vt. FLOOKUP env1.toplevel_vtypes k = SOME vt /\ FLOOKUP env1.bare_globals k = NONE ==> FLOOKUP env2.bare_globals k = NONE) ==>
  well_typed_exprs (defaults_env env2) dflts
Proof
  rw[defaults_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem static_maps_transfer_env_extend_local[local]:
  static_maps_transfer_env env1 env2 ==>
  static_maps_transfer_env (extend_local env1 n ty a) (extend_local env2 n ty a)
Proof
  rw[static_maps_transfer_env_def, extend_local_def]
QED

Theorem well_typed_expr_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 ==> well_typed_expr env2 e
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 1 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem well_typed_exprs_static_maps_transfer_env[local]:
  well_typed_exprs env1 es /\ static_maps_transfer_env env1 env2 ==> well_typed_exprs env2 es
Proof
  rw[static_maps_transfer_env_def] >>
  irule (cj 4 well_typed_static_maps_transfer) >>
  first_assum $ irule_at Any >>
  simp[]
QED

Theorem type_place_expr_static_maps_transfer_env[local]:
  type_place_expr env1 e = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_expr env2 e = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 2 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem type_place_target_static_maps_transfer_env[local]:
  type_place_target env1 tgt = SOME vt /\ static_maps_transfer_env env1 env2 ==>
  type_place_target env2 tgt = SOME vt
Proof
  rw[static_maps_transfer_env_def] >>
  drule (cj 3 well_typed_static_maps_transfer) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[]
QED

Theorem type_place_expr_static_maps_transfer_env_reverse_SOME[local]:
  !e env1 env2 vt.
    well_typed_expr env1 e /\
    static_maps_transfer_env env1 env2 /\
    type_place_expr env2 e = SOME vt ==>
    type_place_expr env1 e = SOME vt
Proof
  Induct >>
  rw[well_typed_expr_def, static_maps_transfer_env_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (PairCases_on `p` >> gvs[well_typed_expr_def, vtype_annotation_ok_def]) >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def] >>
  TRY (rename1 `FLOOKUP env1.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` >>
       `FLOOKUP env2.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by metis_tac[] >>
       gvs[]) >>
  TRY (`static_maps_transfer_env env1 env2` by rw[static_maps_transfer_env_def]) >>
  TRY (rename1 `subscript_vtype base_vt (expr_type idx) = SOME result_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`base_vt`] mp_tac) >>
       simp[] >> strip_tac >>
       qexists `base_vt` >> simp[]) >>
  TRY (rename1 `type_place_expr env2 e = SOME env2_vt` >>
       qpat_x_assum `!env1 env2 vt. well_typed_expr env1 e /\ static_maps_transfer_env env1 env2 /\ type_place_expr env2 e = SOME vt ==> type_place_expr env1 e = SOME vt`
         (qspecl_then [`env1`,`env2`,`env2_vt`] mp_tac) >>
       simp[] >> strip_tac >> gvs[]) >>
  TRY (rename1 `type_place_expr env1 e = SOME base_vt` >>
       `type_place_expr env2 e = SOME base_vt` by metis_tac[type_place_expr_static_maps_transfer_env] >>
       gvs[]) >>
  metis_tac[]
QED

Theorem type_place_expr_no_hash_static_maps_transfer_env[local]:
  well_typed_expr env1 e /\
  static_maps_transfer_env env1 env2 /\
  (!kt vt. type_place_expr env1 e <> SOME (HashMapT kt vt)) ==>
  (!kt vt. type_place_expr env2 e <> SOME (HashMapT kt vt))
Proof
  rw[] >>
  strip_tac >>
  drule_all type_place_expr_static_maps_transfer_env_reverse_SOME >>
  metis_tac[]
QED




Theorem well_typed_atarget_static_maps_transfer_env[local]:
  !env1 tgt ty.
    well_typed_atarget env1 tgt ty ==>
    !env2. static_maps_transfer_env env1 env2 ==>
      well_typed_atarget env2 tgt ty
Proof
  recInduct well_typed_atarget_ind >>
  rw[well_typed_atarget_def, well_typed_target_def]
  >- metis_tac[type_place_target_static_maps_transfer_env]
  >> gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  first_x_assum irule >>
  simp[MEM_EL] >>
  conj_tac >- (qexists `n` >> simp[]) >>
  qexists `tys` >> qexists `n` >> simp[] >>
  first_x_assum irule >>
  simp[]
QED

Theorem well_typed_iterator_static_maps_transfer_env[local]:
  well_typed_iterator env1 typ it /\ static_maps_transfer_env env1 env2 ==>
  well_typed_iterator env2 typ it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def] >>
  metis_tac[well_typed_expr_static_maps_transfer_env]
QED

Theorem type_stmt_static_maps_transfer_mutual[local]:
  (!env1 ret s env1'.
     type_stmt env1 ret s = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmt env2 ret s = SOME env2' /\ static_maps_transfer_env env1' env2') /\
  (!env1 ret ss env1'.
     type_stmts env1 ret ss = SOME env1' ==>
     !env2.
       static_maps_transfer_env env1 env2 ==>
       ?env2'. type_stmts env2 ret ss = SOME env2' /\ static_maps_transfer_env env1' env2')
Proof
  ho_match_mp_tac type_stmt_ind >>
  rw[type_stmt_def, AllCaseEqs()] >>
  gvs[] >>
  TRY (rename1 `well_typed_expr env1 e` >> qexists `env2` >> simp[] >>
       conj_tac >- metis_tac[type_place_expr_no_hash_static_maps_transfer_env] >>
       irule well_typed_expr_static_maps_transfer_env >> simp[]) >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  rpt (first_x_assum (drule_then strip_assume_tac)) >>
  gvs[] >>
  TRY (irule_at Any static_maps_transfer_env_extend_local >> simp[]) >>
  TRY (irule_at Any well_typed_expr_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any well_typed_exprs_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_target_static_maps_transfer_env >> simp[]) >>
  TRY (irule_at Any type_place_expr_no_hash_static_maps_transfer_env >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. (!kt vt. type_place_expr env expr <> SOME (HashMapT kt vt)) /\ static_maps_transfer_env env env2 /\ well_typed_expr env expr` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `?env. static_maps_transfer_env env env2 /\ well_typed_exprs env es` >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `assignable_type env2.type_defs ty` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `assignable_type env2.type_defs (expr_type e)` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `string_to_num id NOTIN FDOM env2.var_types` >>
       gvs[static_maps_transfer_env_def]) >>
  TRY (rename1 `type_place_target env1 bt = SOME (Type (ArrayT ty (Dynamic n)))` >>
       qexistsl [`n`,`env1`,`env1`] >> simp[static_maps_transfer_env_def]) >>
  TRY (rename1 `well_typed_atarget env1 tgt (expr_type e)` >>
       irule well_typed_atarget_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `well_typed_target env1 bt ty` >>
       gvs[well_typed_target_def] >>
       irule type_place_target_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss)` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts env2 ret ss')` >>
       metis_tac[IS_SOME_EXISTS]) >>
  TRY (rename1 `IS_SOME (type_stmts (extend_local env2 (string_to_num id) typ F) ret ss)` >>
       metis_tac[IS_SOME_EXISTS, static_maps_transfer_env_extend_local]) >>
  TRY (rename1 `well_typed_iterator env2 typ it` >>
       irule well_typed_iterator_static_maps_transfer_env >>
       qexists `env1` >> simp[]) >>
  gvs[static_maps_transfer_env_def] >>
  metis_tac[static_maps_transfer_env_extend_local,
            well_typed_expr_static_maps_transfer_env,
            well_typed_exprs_static_maps_transfer_env,
            well_typed_atarget_static_maps_transfer_env,
            well_typed_iterator_static_maps_transfer_env,
            type_place_target_static_maps_transfer_env,
            type_place_expr_no_hash_static_maps_transfer_env]
QED


Theorem type_stmts_static_maps_transfer[local]:
  type_stmts env1 ret body = SOME env_after /\
  static_maps_transfer_env env1 env2 ==>
  ?env_after2. type_stmts env2 ret body = SOME env_after2
Proof
  rw[] >>
  drule (cj 2 type_stmt_static_maps_transfer_mutual) >>
  disch_then (qspec_then `env2` mp_tac) >>
  simp[] >>
  metis_tac[]
QED

Theorem FOLDL_extend_local_args_empty_locals[local]:
  !args (base1 : typing_env) (base2 : typing_env).
    base1.var_types = base2.var_types /\
    base1.var_assignable = base2.var_assignable ==>
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base1 args).var_types =
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base2 args).var_types /\
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base1 args).var_assignable =
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T) base2 args).var_assignable
Proof
  Induct >> rw[] >>
  PairCases_on `h` >>
  first_x_assum (qspecl_then [`extend_local base1 (string_to_num h0) h1 T`,
                               `extend_local base2 (string_to_num h0) h1 T`] mp_tac) >>
  simp[extend_local_def]
QED

Theorem function_entry_env_static_maps_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx) /\
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  env_body = FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
    (<| current_src := entry_src;
       var_types := FEMPTY;
       var_assignable := FEMPTY;
       bare_globals := bare_globals;
       bare_global_assignable := bare_global_assignable;
       toplevel_vtypes := toplevel_vtypes;
       type_defs := get_tenv (initial_evaluation_context sources layouts tx);
       fn_sigs := fn_sigs;
       flag_members := flag_members |>) args ==>
  static_maps_transfer_env (function_entry_env art mods entry_src args) env_body
Proof
  rw[static_maps_transfer_env_def]
  >- simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static]
  >- simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static,
           get_tenv_def, initial_evaluation_context_def]
  >- (rw[function_entry_env_def, artifact_env_def] >>
      irule (cj 1 FOLDL_extend_local_args_empty_locals) >> simp[])
  >- (rw[function_entry_env_def, artifact_env_def] >>
      irule (cj 2 FOLDL_extend_local_args_empty_locals) >> simp[])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_fn_sigs_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_bare_globals_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_bare_global_assignable_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_toplevel_vtypes_lookup_transfer_initial])
  >- (simp[FOLDL_extend_local_args_static] >> metis_tac[artifact_flag_members_lookup_transfer_initial])
  >> (simp[FOLDL_extend_local_args_static] >>
      PairCases_on `k` >>
      irule artifact_toplevel_non_bare_globals_NONE_transfer_initial >>
      qexistsl [`tx.target`, `args`, `art`, `entry_src`, `layouts`, `mods`, `sources`, `toplevel_vtypes`, `tx`, `vt`] >>
      simp[])
QED

Theorem function_entry_env_static_maps_transfer_initial_explicit[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx) /\
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) ==>
  static_maps_transfer_env (function_entry_env art mods entry_src args)
    (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<| current_src := entry_src;
         var_types := FEMPTY;
         var_assignable := FEMPTY;
         bare_globals := bare_globals;
         bare_global_assignable := bare_global_assignable;
         toplevel_vtypes := toplevel_vtypes;
         type_defs := get_tenv (initial_evaluation_context sources layouts tx);
         fn_sigs := fn_sigs;
         flag_members := flag_members |>) args)
Proof
  rw[] >>
  irule function_entry_env_static_maps_transfer_initial >>
  qexistsl [`tx.target`, `bare_global_assignable`, `bare_globals`, `flag_members`, `fn_sigs`,
            `layouts`, `sources`, `toplevel_vtypes`, `tx`] >>
  simp[]
QED
Theorem check_function_body_static_maps_transfer_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx) /\
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx) src = SOME ts /\
          FLOOKUP toplevel_vtypes (src,id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  check_function_body layouts addr mods art entry_src mut nr args dflts ret body ==>
  ?env_body ret_tv env_after.
    env_body.current_src = entry_src /\
    env_body.type_defs = get_tenv (initial_evaluation_context sources layouts tx) /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = bare_globals /\
    env_body.bare_global_assignable = bare_global_assignable /\
    env_body.toplevel_vtypes = toplevel_vtypes /\
    env_body.flag_members = flag_members /\
    evaluate_type (get_tenv (initial_evaluation_context sources layouts tx)) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
Proof
  rpt strip_tac >>
  gns[check_function_body_def] >>
  `?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv` by
    (Cases_on `evaluate_type (type_env_all_modules mods) ret` >> gvs[]) >>
  `?env_after_art. type_stmts (function_entry_env art mods entry_src args) ret body = SOME env_after_art` by
    (Cases_on `type_stmts (function_entry_env art mods entry_src args) ret body` >> gvs[]) >>
  `static_maps_transfer_env (function_entry_env art mods entry_src args)
     (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args)` by
    (irule function_entry_env_static_maps_transfer_initial_explicit >>
     simp[]) >>
  `?env_after. type_stmts
     (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args) ret body = SOME env_after` by
    (drule type_stmts_static_maps_transfer >>
     disch_then (qspec_then `FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args` mp_tac) >>
     simp[]) >>
  qexistsl [`FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args`, `ret_tv`, `env_after`] >>
  simp[FOLDL_extend_local_args_static, get_tenv_def, initial_evaluation_context_def] >>
  conj_tac >- (irule well_typed_defaults_static_maps_transfer >>
                 qexists `function_entry_env art mods entry_src args` >>
                 gvs[static_maps_transfer_env_def, get_tenv_def, initial_evaluation_context_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[params_ok_def] >>
                 drule_all FOLDL_extend_local_args_formal_lookup >> simp[]) >>
  conj_tac >- (rpt strip_tac >> gvs[params_ok_def] >>
                 drule_all FOLDL_extend_local_args_var_types_range >> simp[]) >>
  rpt strip_tac >> gvs[params_ok_def] >>
  drule_all FOLDL_extend_local_args_var_assignable_range >> simp[]
QED
Theorem check_contract_lookup_callable_function_F_body[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  lookup_callable_function F fn ts = SOME (fm,nr,args,dflts,ret,body) ==>
  check_function_body layouts addr mods art src fm nr args dflts ret body
Proof
  rw[] >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  drule_all check_contract_function_body_MEM >> simp[]
QED

Theorem check_contract_functions_well_typed_initial:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  functions_well_typed (initial_evaluation_context sources layouts tx)
Proof
  simp[functions_well_typed_def] >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `ALOOKUP mods src_id_opt = SOME ts` by
    gvs[get_module_code_def, initial_evaluation_context_def] >>
  conj_tac >-
   (`check_function_body layouts addr mods art src_id_opt fm nr args dflts ret body` by
      (irule check_contract_lookup_callable_function_F_body >>
       simp[] >>
       qexists `fn` >>
       gvs[initial_evaluation_context_def]) >>
    gvs[initial_evaluation_context_def, check_function_body_def] >>
    Cases_on `lookup_nonreentrant_slot layouts tx.target` >> gvs[] >>
    qexists `fn` >> simp[]) >>
  `check_function_body layouts addr mods art src_id_opt fm nr args dflts ret body` by
    (irule check_contract_lookup_callable_function_F_body >>
     simp[] >>
     qexists `fn` >>
     gvs[initial_evaluation_context_def]) >>
  drule_all check_function_body_static_maps_transfer_initial >>
  simp[]
QED

(* ===== Explicit external entry no-TypeError bridge for checked contracts ===== *)

Theorem functions_well_typed_stk_irrelevant[local]:
  !cx stk. functions_well_typed (cx with stk := stk) <=>
           functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def, get_tenv_def,
       fn_sigs_consistent_def, fn_sigs_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       well_formed_type_def]
QED

Theorem check_contract_functions_well_typed_initial_stk[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  functions_well_typed ((initial_evaluation_context sources layouts tx) with stk := stk)
Proof
  rw[functions_well_typed_stk_irrelevant] >>
  irule check_contract_functions_well_typed_initial >>
  simp[]
QED

Theorem check_contract_explicit_external_entry_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts /\
  context_well_typed
    ((initial_evaluation_context am.sources am.layouts tx) with stk := [(src,fn)]) /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    ((initial_evaluation_context am.sources am.layouts tx) with stk := [(src,fn)])
    am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals ==>
  no_type_error_eval
    (eval_stmts
      ((initial_evaluation_context am.sources am.layouts tx) with stk := [(src,fn)])
      body
      (initial_state am [scope]))
Proof
  cheat
QED

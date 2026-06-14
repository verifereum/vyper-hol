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
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeStmtSoundness
  vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalPreservesImmutablesDom
  vyperScopePreservation vyperStatePreservation
Libs
  wordsLib

val _ = Parse.hide "body";

Theorem get_module_code_initial_evaluation_context:
  ALOOKUP sources addr = SOME mods /\ tx.target = addr ==>
  get_module_code (initial_evaluation_context sources layouts tx src) src = ALOOKUP mods src
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
    (initial_evaluation_context sources layouts tx src)
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
    (initial_evaluation_context sources layouts tx src)
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
    (initial_evaluation_context sources layouts tx src)
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
    (initial_evaluation_context sources layouts tx src)
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
    (initial_evaluation_context sources layouts tx src)
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
    (initial_evaluation_context sources layouts tx src)
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
    ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
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
           (initial_evaluation_context sources layouts tx src)` by
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
       (initial_evaluation_context sources layouts tx src)` by
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
    ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
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
       (initial_evaluation_context sources layouts tx src)` by
      (irule check_contract_bare_globals_complete_initial >> simp[check_contract_def]) >>
    gvs[bare_globals_complete_def] >>
    qpat_x_assum `!src ts vis mut id ty init. _` irule >>
    simp[get_module_code_def, initial_evaluation_context_def] >> metis_tac[]) >>
  conj_tac >-
   (`toplevel_vtypes_complete (build_contract_type_artifact F mods).cta_toplevel_vtypes
       (initial_evaluation_context sources layouts tx src)` by
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
       get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
       find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
       typ = ty /\
       IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
       IS_SOME (lookup_var_slot_from_layout
         (initial_evaluation_context sources layouts tx src) is_transient src id_str)) /\
  (!src id kt vt.
     FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
     ?ts is_transient id_str.
       get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
       find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
       IS_SOME (lookup_var_slot_from_layout
         (initial_evaluation_context sources layouts tx src) is_transient src id_str))
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
                (initial_evaluation_context sources layouts tx src)` by
               (irule check_contract_bare_globals_complete_initial >> simp[check_contract_def]) >>
             gvs[bare_globals_complete_def] >>
             qpat_x_assum `!src ts vis mut id ty init. _`
               (qspecl_then [`src`,`ts`,`vis`,`Constant e`,`id_str`,`ty`,`init`] mp_tac) >>
             simp[get_module_code_def, initial_evaluation_context_def]) >>
         `bare_globals_complete (build_contract_type_artifact F mods).cta_bare_globals
            (initial_evaluation_context sources layouts tx src)` by
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
    ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
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
    (initial_evaluation_context sources layouts tx NONE)
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
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, lookup_var_slot_from_layout_def,
           get_tenv_def, initial_evaluation_context_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src`,`fid`,`ls`] mp_tac) >>
      simp[get_module_code_def, get_tenv_def, initial_evaluation_context_def])
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

Theorem check_contract_env_context_consistent_initial_src:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods src)
    (initial_evaluation_context sources layouts tx src)
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
  >- (dxrule check_contract_bare_globals_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_def, get_tenv_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def,
           get_module_code_def, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_def, initial_evaluation_context_def, get_module_code_def])
QED

Theorem check_contract_env_context_consistent_initial_with_current_src:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  env_context_consistent (artifact_env art mods src)
    ((initial_evaluation_context sources layouts tx src) with stk := [(src, fn)])
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
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_bare_global_assignable_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`id`,`ty`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def,
           get_tenv_stk, get_tenv_def] >> strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk, get_module_code_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_toplevel_vtypes_consistent_initial >>
      simp[] >> disch_then (qspecl_then [`tx`,`sources`] mp_tac) >>
      simp[get_module_code_stk, get_module_code_def, initial_evaluation_context_def,
           lookup_var_slot_from_layout_stk, lookup_var_slot_from_layout_def] >>
      strip_tac >> metis_tac[])
  >- (dxrule check_contract_flag_members_consistent_initial >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`tx`,`sources`,`src'`,`fid`,`ls`] mp_tac) >>
      simp[get_tenv_stk, get_tenv_def, initial_evaluation_context_def,
           get_module_code_stk, get_module_code_def])
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
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).fn_sigs k = SOME sig ==>
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
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_globals k = SOME ty ==>
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
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).bare_global_assignable k = SOME ty ==>
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
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).toplevel_vtypes k = SOME vt ==>
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
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  FLOOKUP (function_entry_env art mods entry_src args).flag_members k = SOME members ==>
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
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx cx_src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
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
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  env_body = FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
    (<| current_src := entry_src;
       var_types := FEMPTY;
       var_assignable := FEMPTY;
       bare_globals := bare_globals;
       bare_global_assignable := bare_global_assignable;
       toplevel_vtypes := toplevel_vtypes;
       type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
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
      qexistsl [`tx.target`, `args`, `art`, `src`, `entry_src`, `layouts`, `mods`, `sources`, `toplevel_vtypes`, `tx`, `vt`] >>
      simp[])
QED

Theorem function_entry_env_static_maps_transfer_initial_explicit[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
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
         type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
         fn_sigs := fn_sigs;
         flag_members := flag_members |>) args)
Proof
  rw[] >>
  irule function_entry_env_static_maps_transfer_initial >>
  qexistsl [`tx.target`, `bare_global_assignable`, `bare_globals`, `flag_members`, `fn_sigs`,
            `layouts`, `sources`, `src`, `toplevel_vtypes`, `tx`] >>
  simp[]
QED
Theorem check_function_body_static_maps_transfer_initial[local]:
  !layouts addr mods art sources tx fn_sigs bare_globals bare_global_assignable
   toplevel_vtypes flag_members entry_src mut nr args dflts ret body.
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr /\
  fn_sigs_complete fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT) /\
  check_function_body layouts addr mods art entry_src mut nr args dflts ret body ==>
  ?env_body ret_tv env_after.
    env_body.current_src = entry_src /\
    env_body.type_defs = get_tenv (initial_evaluation_context sources layouts tx src) /\
    env_body.fn_sigs = fn_sigs /\
    env_body.bare_globals = bare_globals /\
    env_body.bare_global_assignable = bare_global_assignable /\
    env_body.toplevel_vtypes = toplevel_vtypes /\
    env_body.flag_members = flag_members /\
    evaluate_type (get_tenv (initial_evaluation_context sources layouts tx src)) ret = SOME ret_tv /\
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
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args)` by
    (irule function_entry_env_static_maps_transfer_initial_explicit >>
     simp[]) >>
  `?env_after. type_stmts
     (FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args) ret body = SOME env_after` by
    (drule type_stmts_static_maps_transfer >>
     disch_then (qspec_then `FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
        fn_sigs := fn_sigs; flag_members := flag_members|>) args` mp_tac) >>
     simp[]) >>
  qexistsl [`FOLDL (\env (id,ty). extend_local env (string_to_num id) ty T)
      (<|current_src := entry_src; var_types := FEMPTY; var_assignable := FEMPTY;
        bare_globals := bare_globals; bare_global_assignable := bare_global_assignable;
        toplevel_vtypes := toplevel_vtypes;
        type_defs := get_tenv (initial_evaluation_context sources layouts tx src);
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
  functions_well_typed (initial_evaluation_context sources layouts tx src)
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
  functions_well_typed ((initial_evaluation_context sources layouts tx src) with stk := stk)
Proof
  rw[functions_well_typed_stk_irrelevant] >>
  irule check_contract_functions_well_typed_initial >>
  simp[]
QED

Theorem checked_contract_static_maps_transfer_inputs_initial[local]:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP sources addr = SOME mods /\
  tx.target = addr ==>
  fn_sigs_complete art.cta_fn_sigs (initial_evaluation_context sources layouts tx src) /\
  bare_globals_complete art.cta_bare_globals (initial_evaluation_context sources layouts tx src) /\
  bare_global_assignable_complete art.cta_bare_global_assignable (initial_evaluation_context sources layouts tx src) /\
  toplevel_vtypes_complete art.cta_toplevel_vtypes (initial_evaluation_context sources layouts tx src) /\
  flag_members_complete art.cta_flag_members (initial_evaluation_context sources layouts tx src) /\
  (!src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ==>
     ?ts. get_module_code (initial_evaluation_context sources layouts tx src) src' = SOME ts /\
          FLOOKUP art.cta_toplevel_vtypes (src',id) = SOME (Type ty) /\
          is_bare_global_decl id ts /\
          find_var_decl_by_num id ts = NONE /\ ty <> NoneT)
Proof
  rw[] >> rpt conj_tac
  >- (irule check_contract_fn_sigs_complete_initial >> simp[])
  >- (irule check_contract_bare_globals_complete_initial >> simp[])
  >- (irule check_contract_bare_global_assignable_complete_initial >> simp[])
  >- (irule check_contract_toplevel_vtypes_complete_initial >> simp[])
  >- (irule check_contract_flag_members_complete_initial >> simp[]) >>
  drule check_contract_bare_globals_consistent_initial >>
  simp[] >>
  disch_then (qspecl_then [`tx`, `sources`, `src'`, `id`, `ty`] mp_tac) >>
  simp[get_module_code_def, initial_evaluation_context_def]
QED

Theorem checked_explicit_external_body_typing_package[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts ==>
  ?env_body env_after.
    env_body.current_src = src /\
    env_body.type_defs = get_tenv (initial_evaluation_context am.sources am.layouts tx src) /\
    env_body.fn_sigs = art.cta_fn_sigs /\
    env_body.bare_globals = art.cta_bare_globals /\
    env_body.bare_global_assignable = art.cta_bare_global_assignable /\
    env_body.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_body.flag_members = art.cta_flag_members /\
    type_stmts env_body ret body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  rw[] >>
  `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
    metis_tac[check_contract_function_body_MEM] >>
  `fn_sigs_complete art.cta_fn_sigs (initial_evaluation_context am.sources am.layouts tx src) /\
   bare_globals_complete art.cta_bare_globals (initial_evaluation_context am.sources am.layouts tx src) /\
   bare_global_assignable_complete art.cta_bare_global_assignable (initial_evaluation_context am.sources am.layouts tx src) /\
   toplevel_vtypes_complete art.cta_toplevel_vtypes (initial_evaluation_context am.sources am.layouts tx src) /\
   flag_members_complete art.cta_flag_members (initial_evaluation_context am.sources am.layouts tx src) /\
   (!src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ==>
      ?ts'. get_module_code (initial_evaluation_context am.sources am.layouts tx src) src' = SOME ts' /\
            FLOOKUP art.cta_toplevel_vtypes (src',id) = SOME (Type ty) /\
            is_bare_global_decl id ts' /\
            find_var_decl_by_num id ts' = NONE /\ ty <> NoneT)` by
    (irule checked_contract_static_maps_transfer_inputs_initial >> simp[]) >>
  qspecl_then
    [`am.layouts`, `tx.target`, `mods`, `art`, `am.sources`, `tx`,
     `art.cta_fn_sigs`, `art.cta_bare_globals`,
     `art.cta_bare_global_assignable`, `art.cta_toplevel_vtypes`,
     `art.cta_flag_members`, `src`, `mut`, `nr`, `args`, `dflts`, `ret`, `body`]
    mp_tac check_function_body_static_maps_transfer_initial >>
  simp[] >> rw[] >>
  qexistsl [`env_body`, `env_after`] >> simp[] >> metis_tac[]
QED

Theorem checked_explicit_external_entry_establishes_type_soundness_preconditions[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts /\
  context_well_typed
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
    am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals ==>
  ?env_body env_after st.
    st = initial_state am [scope] /\
    functions_well_typed
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
    accounts_well_typed st.accounts /\
    state_well_typed st /\
    env_consistent env_body
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) st /\
    type_stmts env_body ret body = SOME env_after
Proof
  strip_tac >> gvs[] >>
  drule_all checked_explicit_external_body_typing_package >>
  strip_tac >>
  `scope_well_typed scope` by
    (qspecl_then [`type_env_all_modules mods`, `args`, `vals`, `scope`] mp_tac
       bind_arguments_scope_well_typed_stmt >>
     simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     gvs[args_values_typed_def]) >>
  qexistsl [`env_body`, `env_after`] >>
  rw[initial_state_accounts_well_typed, initial_state_single_scope_well_typed] >-
    (irule check_contract_functions_well_typed_initial_stk >> simp[]) >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_with_current_src >>
      simp[])
  >- (`env_scopes_consistent env_body
         ((initial_evaluation_context am.sources am.layouts tx env_body.current_src) with stk := [(env_body.current_src,fn)])
         ((initial_state am []) with scopes := [scope])` suffices_by
        simp[initial_state_def] >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (irule immutables_ready_env_immutables_consistent >>
      qexists `artifact_env art mods src` >>
      gvs[artifact_env_def])
QED

Theorem check_contract_explicit_external_entry_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts /\
  context_well_typed
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)]) /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
    am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals ==>
  no_type_error_eval
    (eval_stmts
      ((initial_evaluation_context am.sources am.layouts tx src) with stk := [(src,fn)])
      body
      (initial_state am [scope]))
Proof
  metis_tac[
    checked_explicit_external_entry_establishes_type_soundness_preconditions,
    eval_stmts_no_type_error]
QED

Theorem checked_explicit_external_post_prefix_body_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_stmts cx body st)
Proof
  strip_tac >> gvs[] >>
  drule_all checked_explicit_external_body_typing_package >>
  strip_tac >>
  `functions_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  irule eval_stmts_no_type_error >>
  simp[] >>
  rpt (conj_tac >- simp[]) >>
  qexistsl [`env_body`, `env_after`, `ret`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >>
      simp[])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >>
      rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >>
      strip_tac >>
      first_x_assum drule_all >>
      simp[])
QED

Theorem immutables_ready_initial_evaluation_context_source[local]:
  immutables_ready bare_globals toplevel_vtypes
    (initial_evaluation_context sources layouts tx NONE) imms ==>
  immutables_ready bare_globals toplevel_vtypes
    (initial_evaluation_context sources layouts tx src) imms
Proof
  rw[immutables_ready_def, get_tenv_def, get_module_code_def,
     initial_evaluation_context_def] >> metis_tac[]
QED


(* ===== External lookup provenance for checked contracts ===== *)

Definition is_public_getter_decl_def:
  is_public_getter_decl fn (VariableDecl Public mut id typ init) = (id = fn) /\
  is_public_getter_decl fn (HashMapDecl Public is_transient id kt vt init) = (id = fn) /\
  is_public_getter_decl _ _ = F
End

Definition external_getter_tuple_def:
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    (if ~is_ArrayT typ then
       SOME (View,F,[],[],typ,[Return (SOME (TopLevelName NoneT (src,id)))])
     else
       SOME (getter (TopLevelName NoneT (src,id)) (BaseT (UintT 256)) (Type (ArrayT_type typ)))) /\
  external_getter_tuple src (HashMapDecl Public is_transient id kt vt init) =
    SOME (getter (TopLevelName NoneT (src,id)) kt vt) /\
  external_getter_tuple _ _ = NONE
End

Theorem lookup_function_External_cases[local]:
  lookup_function src fn External ts = SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw. MEM (FunctionDecl External mut nr raw fn args dflts ret body) ts) \/
  (?decl. MEM decl ts /\ is_public_getter_decl fn decl /\
          external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  Induct_on `ts` >- rw[lookup_function_def] >>
  gen_tac >> Cases_on `h` >>
  rw[lookup_function_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  TRY (Cases_on `v`) >>
  gvs[AllCaseEqs(), lookup_function_def, is_public_getter_decl_def, external_getter_tuple_def] >>
  TRY (disj1_tac >> qexists `b0` >> simp[] >> NO_TAC) >>
  TRY (disj1_tac >> qexists `raw` >> simp[] >> NO_TAC) >>
  TRY (disj1_tac >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `VariableDecl Public v0 fn ret o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `VariableDecl Public v0 fn t o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> qexists `HashMapDecl Public b fn t v0 o'` >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  TRY (disj2_tac >> goal_assum (drule_at Any) >>
       simp[is_public_getter_decl_def, external_getter_tuple_def] >> NO_TAC) >>
  metis_tac[]
QED

Theorem lookup_exported_function_checked_cases_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code cx src = SOME ts /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw.
     MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
  (?decl.
     MEM decl ts /\
     is_public_getter_decl tx.function_name decl /\
     external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  rpt strip_tac >>
  gvs[find_function_module_def, initial_evaluation_context_def] >>
  gvs[lookup_exported_function_def, get_self_code_def, AllCaseEqs()] >>
  drule lookup_function_External_cases >>
  simp[]
QED


Theorem scalar_raw_public_getter_body_typing_annotation_contradiction[local]:
  typ <> NoneT /\
  FLOOKUP env.toplevel_vtypes (src,string_to_num fn) = SOME (Type typ) ==>
  type_stmts env typ [Return (SOME (TopLevelName NoneT (src,fn)))] = NONE
Proof
  rw[type_stmt_def, well_typed_expr_def]
QED

Theorem raw_getter_index_name_annotation_contradiction[local]:
  kt <> NoneT /\
  FLOOKUP env.var_types (string_to_num vn) = SOME kt ==>
  ~well_typed_expr env (Name NoneT vn)
Proof
  rw[well_typed_expr_def]
QED

Theorem checked_scalar_public_getter_body_typing_package_contradiction[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  ~is_ArrayT typ ==>
  ~(?env_after.
      type_stmts (artifact_env art mods src) typ
        [Return (SOME (TopLevelName NoneT (src,fn)))] = SOME env_after)
Proof
  rw[] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def, get_module_code_def,
         initial_evaluation_context_def] >>
     metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `typ <> NoneT` by
    (Cases_on `mut` >> gvs[check_toplevel_decl_def] >>
     metis_tac[assignable_type_not_NoneT]) >>
  `type_stmts (artifact_env art mods src) typ
     [Return (SOME (TopLevelName NoneT (src,fn)))] = NONE` by
    (irule scalar_raw_public_getter_body_typing_annotation_contradiction >>
     simp[artifact_env_def]) >>
  gvs[]
QED
(* ===== Top-level checked call_external no-TypeError theorem ===== *)

Theorem checked_scalar_public_getter_eval_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
      imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule checked_scalar_public_getter_eval_no_type_error >> metis_tac[]) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem checked_scalar_public_getter_eval_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
      simp[get_module_code_def, initial_evaluation_context_def] >>
    `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
      (`toplevel_vtypes_complete art.cta_toplevel_vtypes
          (initial_evaluation_context am.sources am.layouts tx src)` by
         (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
       gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
    `check_toplevel_decl am.layouts tx.target mods art src
       (VariableDecl Public mut fn typ init)` by
      metis_tac[check_contract_toplevel_decl_MEM] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
      (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
       gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
         return_def, raise_def, initial_evaluation_context_def] >>
    Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                          well_formed_type_def]
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts =
           SOME (StorageVarDecl T typ,fn)` by
          metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                    contract_namespaces_ok_module_toplevel_vtype_keys,
                    ALOOKUP_MEM, check_contract_def] >>
        gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
            get_tenv_def, initial_evaluation_context_def] >>
        drule assignable_type_well_formed >> simp[well_formed_type_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
        gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
        imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
        gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    `find_var_decl_by_num (string_to_num fn) ts =
       SOME (StorageVarDecl F typ,fn)` by
      metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
                contract_namespaces_ok_module_toplevel_vtype_keys,
                ALOOKUP_MEM, check_contract_def] >>
    gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
        get_tenv_def, initial_evaluation_context_def] >>
    drule assignable_type_well_formed >> simp[well_formed_type_def] >>
    strip_tac >> gvs[IS_SOME_EXISTS] >>
    Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
    imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
    gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_evaluation_context_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME typ` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`typ`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T typ,fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      drule assignable_type_well_formed >> simp[well_formed_type_def] >>
      strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `x'` >> simp[return_def, bind_def] >>
      gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F typ,fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  drule assignable_type_well_formed >> simp[well_formed_type_def] >>
  strip_tac >> gvs[IS_SOME_EXISTS] >>
  Cases_on `x'` >> simp[return_def, bind_def] >>
  gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem bind_arguments_scope_covers_params_getter[local]:
  !tenv params vs sc id typ.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,typ) params /\
    (!id' typ'. MEM (id',typ') params /\ string_to_num id' = string_to_num id ==> typ' = typ) ==>
    ?entry. FLOOKUP sc (string_to_num id) = SOME entry /\
            evaluate_type tenv typ = SOME entry.type /\ entry.assignable
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      qpat_x_assum `id = q` SUBST_ALL_TAC >>
      qpat_x_assum `typ = r` SUBST_ALL_TAC >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `string_to_num q = string_to_num id`
  >- (qexists_tac `<|assignable := T; type := tv; value := v'|>` >>
      `r = typ` by metis_tac[] >>
      qpat_x_assum `r = typ` SUBST_ALL_TAC >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `m`, `id`, `typ`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id'' typ''. _` (qspecl_then [`id'`, `typ'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED

Theorem bind_arguments_scope_covers_uint_getter[local]:
  !tenv params vs sc id.
    bind_arguments tenv params vs = SOME sc /\ MEM (id,BaseT (UintT 256)) params /\
    (!id' typ'. MEM (id',typ') params /\ string_to_num id' = string_to_num id ==>
       typ' = BaseT (UintT 256)) ==>
    ?i entry. FLOOKUP sc (string_to_num id) = SOME entry /\
              entry.type = BaseTV (UintT 256) /\ entry.assignable /\
              entry.value = IntV i
Proof
  Induct_on `params` >> simp[Once bind_arguments_def] >>
  Cases >> simp[Once bind_arguments_def] >>
  rpt gen_tac >> Cases_on `vs` >> simp[Once bind_arguments_def] >>
  Cases_on `evaluate_type tenv r` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv params t` >> simp[] >>
  rpt strip_tac >> gvs[PULL_EXISTS]
  >- (`r = BaseT (UintT 256)` by metis_tac[] >> gvs[evaluate_type_def] >>
      Cases_on `h` >> gvs[vyperValueOperationTheory.safe_cast_def] >>
      qexists_tac `i` >>
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i|>` >>
      rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  Cases_on `string_to_num q = string_to_num id`
  >- (`r = BaseT (UintT 256)` by metis_tac[] >> gvs[evaluate_type_def] >>
      Cases_on `h` >> gvs[vyperValueOperationTheory.safe_cast_def] >>
      qexists_tac `i` >>
      qexists_tac `<|assignable := T; type := BaseTV (UintT 256); value := IntV i|>` >>
      asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]) >>
  first_x_assum (qspecl_then [`tenv`, `t`, `x''`, `id`] mp_tac) >>
  impl_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!id'' typ''. _` (qspecl_then [`id'`, `typ'`] mp_tac) >>
      simp[]) >>
  strip_tac >>
  qexists_tac `i` >> qexists_tac `entry` >> asm_rewrite_tac[FLOOKUP_UPDATE] >> simp[]
QED
Theorem bind_arguments_scope_covers_generated_uint_ambient[local]:
  !tenv all_args vals scope n.
    bind_arguments tenv all_args vals = SOME scope /\
    MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
    (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
        string_to_num id' = string_to_num id ==> typ' = typ) ==>
    ?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
              entry.type = BaseTV (UintT 256) /\ entry.assignable /\
              entry.value = IntV i
Proof
  rpt strip_tac >>
  irule bind_arguments_scope_covers_uint_getter >>
  qexistsl [`all_args`, `tenv`, `vals`] >>
  simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
  simp[]
QED

Theorem bind_arguments_Name_eval_no_type_error[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem bind_arguments_Name_eval_Value[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (INL tvl,st') ==>
  ?v. tvl = Value v
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, initial_state_def, get_scopes_def,
       lookup_scopes_val_def, bind_def, lift_option_def, lift_option_type_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem bind_arguments_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (id,typ) args /\
  (!id' typ'. MEM (id',typ') args /\ string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope (string_to_num id) = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT id) st = (INL (Value entry.value),st)
Proof
  rpt strip_tac >>
  drule_all bind_arguments_scope_covers_params_getter >> strip_tac >>
  qexists_tac `entry` >>
  gvs[Once evaluate_def, get_scopes_def, lookup_scopes_val_def,
      bind_def, lift_option_def, lift_option_type_def, return_def]
QED

Theorem bind_arguments_generated_Name_eval_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n,typ) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] ==>
  ?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
          evaluate_type tenv typ = SOME entry.type /\ entry.assignable /\
          eval_expr cx (Name NoneT (num_to_dec_string n)) st =
            (INL (Value entry.value),st)
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_post_prefix >>
  simp[] >>
  qexistsl [`args`,`vals`] >> simp[] >>
  metis_tac[]
QED

Theorem evaluate_subscript_hashmap_getter_error_not_TypeError[local]:
  !vt.
    check_value_type tenv vt /\
    evaluate_subscript tenv arr_tv (HashMapRef is_transient slot kt vt) idx = INR err ==>
    !msg. err <> TypeError msg
Proof
  Induct_on `vt` >>
  rw[check_value_type_def, evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
  Cases_on `t` >> gvs[assignable_type_def, well_formed_type_def,
                    evaluate_type_def, AllCaseEqs()]
QED

Theorem evaluate_subscript_getter_error_not_TypeError[local]:
  ((?av i. x = Value (ArrayV av) /\ idx = IntV i) \/
   (?is_transient slot kt vt.
      x = HashMapRef is_transient slot kt vt /\ check_value_type tenv vt) \/
   (?is_transient slot elem_tv bd i.
      x = ArrayRef is_transient slot elem_tv bd /\ idx = IntV i)) /\
  evaluate_subscript tenv arr_tv x idx = INR err ==>
  !msg. err <> TypeError msg
Proof
  rpt strip_tac >> gvs[] >>
  gvs[evaluate_subscript_def, vyperValueOperationTheory.array_index_def, AllCaseEqs(), LET_THM] >>
  TRY (Cases_on `t` >> gvs[check_value_type_def, assignable_type_def,
                          well_formed_type_def, evaluate_type_def, AllCaseEqs()]) >>
  metis_tac[evaluate_subscript_hashmap_getter_error_not_TypeError]
QED

Theorem evaluate_subscript_Value_ArrayV_IntV_error_not_TypeError[local]:
  evaluate_subscript tenv arr_tv (Value (ArrayV av)) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, vyperValueOperationTheory.array_index_def,
     AllCaseEqs(), LET_THM]
QED

Theorem Subscript_NoneTV_HashMapRef_no_TypeError[local]:
  check_value_type (get_tenv cx) vt /\
  (do
     check_array_bounds cx (HashMapRef is_transient base_slot kt vt) kv;
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV
              (HashMapRef is_transient base_slot kt vt) kv);
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rw[check_array_bounds_def, bind_def, ignore_bind_def, return_def,
     raise_def, lift_sum_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `vt` >>
  gvs[evaluate_subscript_def, check_value_type_def,
      assignable_type_def, well_formed_type_def,
      evaluate_type_def, AllCaseEqs(), bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (imp_res_tac assignable_type_well_formed) >>
  TRY (Cases_on `evaluate_type (get_tenv cx) t` >> gvs[well_formed_type_def, bind_def, return_def, raise_def]) >>
  TRY (Cases_on `read_storage_slot cx is_transient
                   (hashmap_slot base_slot (encode_hashmap_key kt kv)) x s''` >>
       gvs[bind_def, return_def, raise_def]) >>
  TRY (Cases_on `q` >> gvs[bind_def, return_def, raise_def]) >>
  TRY (Cases_on `kv` >> gvs[check_array_bounds_def, return_def]) >>
  gvs[check_array_bounds_def, return_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[])
QED

Theorem materialise_getter_result_no_type_error[local]:
  ((?v. tv = Value v) \/
   (?is_transient base_slot elem_tv bd.
      tv = ArrayRef is_transient base_slot elem_tv bd)) /\
  materialise cx tv st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[materialise_def, bind_def, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `read_storage_slot cx is_transient base_slot (ArrayTV elem_tv bd) st` >>
  Cases_on `q` >> gvs[return_def, raise_def] >>
  imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem array_public_getter_tuple_shape[local]:
  is_ArrayT typ /\
  external_getter_tuple src (VariableDecl Public mut id typ init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?kt vt exp. build_getter (TopLevelName NoneT (src,id)) kt (Type vt) 0 =
                 (args,ret,exp) /\ body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName NoneT (src,id)) (BaseT (UintT 256))
              (Type (ArrayT_type typ)) 0` >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem hashmap_public_getter_tuple_shape[local]:
  external_getter_tuple src (HashMapDecl Public is_transient id kt vt init) =
    SOME (gm,gnr,args,dflts,ret,body) ==>
  gm = View /\ gnr = F /\ dflts = [] /\
  ?exp. build_getter (TopLevelName NoneT (src,id)) kt vt 0 =
          (args,ret,exp) /\ body = [Return (SOME exp)]
Proof
  rw[external_getter_tuple_def, getter_def] >>
  Cases_on `build_getter (TopLevelName NoneT (src,id)) kt vt 0` >>
  Cases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem checked_hashmap_decl_value_type_checked[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts ==>
  check_value_type (type_env_all_modules mods) vt
Proof
  rpt strip_tac >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  gvs[check_toplevel_decl_def]
QED

Theorem checked_public_hashmap_TopLevelName_carrier[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope]) = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def] >>
  metis_tac[]
QED

Theorem checked_public_hashmap_TopLevelName_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem checked_public_hashmap_TopLevelName_carrier_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (INL tvl,st') ==>
  ?slot. tvl = HashMapRef is_transient slot kt vt
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def] >>
  metis_tac[]
QED

Theorem checked_public_hashmap_TopLevelName_no_type_error_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,id)) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  `find_var_decl_by_num (string_to_num id) ts =
     SOME (HashMapVarDecl is_transient kt vt,id)` by
    metis_tac[find_var_decl_by_num_SOME_hashmap] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (HashMapDecl Public is_transient id kt vt init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, get_module_code_def,
       initial_evaluation_context_def, bind_def, lift_option_type_def,
       return_def, raise_def, lookup_var_slot_from_layout_def,
       lookup_var_slot_in_layouts_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                       vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED
Theorem build_getter_args_index_ge_aux[local]:
  !e kt vt n args ret exp id typ.
    build_getter e kt vt n = (args,ret,exp) /\ MEM (id,typ) args ==>
    ?m. n <= m /\ id = num_to_dec_string m
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  first_x_assum drule >> rw[] >>
  qexists_tac `m` >> simp[]
QED

Theorem string_to_num_eq_imp[local]:
  !s t. string_to_num s = string_to_num t ==> s = t
Proof
  metis_tac[string_to_num_inj]
QED

Theorem build_getter_args_no_current_name[local]:
  !e kt vt n args ret exp typ.
    build_getter e kt vt (SUC n) = (args,ret,exp) /\
    MEM (num_to_dec_string n,typ) args ==> F
Proof
  rpt strip_tac >>
  drule_all build_getter_args_index_ge_aux >>
  strip_tac >>
  gvs[ASCIInumbersTheory.toString_11] >>
  decide_tac
QED

Theorem build_getter_args_no_current_num[local]:
  !e kt vt n args ret exp id typ.
    build_getter e kt vt (SUC n) = (args,ret,exp) /\
    MEM (id,typ) args /\
    string_to_num id = string_to_num (num_to_dec_string n) ==> F
Proof
  rpt strip_tac >>
  drule string_to_num_eq_imp >>
  strip_tac >> gvs[] >>
  metis_tac[build_getter_args_no_current_name]
QED

Theorem build_getter_args_num_unique[local]:
  !e kt vt n args ret exp id typ id' typ'.
    build_getter e kt vt n = (args,ret,exp) /\
    MEM (id,typ) args /\ MEM (id',typ') args /\
    string_to_num id' = string_to_num id ==> typ' = typ
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[] >> gvs[] >>
  imp_res_tac string_to_num_eq_imp >>
  gvs[ASCIInumbersTheory.toString_11] >>
  TRY (imp_res_tac build_getter_args_no_current_name) >>
  TRY (imp_res_tac build_getter_args_no_current_num) >>
  metis_tac[]
QED

Theorem build_getter_bound_Name_eval_no_type_error[local]:
  build_getter e kt vt n = (args,ret,exp) /\
  MEM (id,typ) args /\
  bind_arguments tenv args vals = SOME scope /\
  eval_expr cx (Name NoneT id) (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule bind_arguments_Name_eval_no_type_error >>
  simp[] >>
  metis_tac[build_getter_args_num_unique]
QED

Theorem build_getter_exp_pure[local]:
  !e kt vt n args ret exp.
    pure_expr e /\ build_getter e kt vt n = (args,ret,exp) ==> pure_expr exp
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, pure_expr_def] >>
  Cases_on `is_ArrayT vt` >> simp[pure_expr_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[pure_expr_def] >>
  first_x_assum irule >> simp[pure_expr_def]
QED

Theorem build_getter_exp_type_NoneTV[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) /\ evaluate_type tenv (expr_type e) = SOME NoneTV ==>
    evaluate_type tenv (expr_type exp) = SOME NoneTV
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, expr_type_def, evaluate_type_def] >>
  Cases_on `is_ArrayT vt` >> simp[expr_type_def, evaluate_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[expr_type_def, evaluate_type_def] >>
  first_x_assum irule >> simp[expr_type_def, evaluate_type_def]
QED

Theorem generated_hashmap_subscript_step_no_type_error[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  irule Subscript_NoneTV_HashMapRef_no_TypeError >>
  qexistsl [`slot`, `cx`, `is_transient`, `kt`, `entry.value`,
            `<|immutables := am.immutables; logs := []; scopes := [scope];
               accounts := am.accounts; tStorage := am.tStorage|>`, `st2`, `vt`] >>
  simp[]
QED

Theorem generated_hashmap_subscript_step_no_type_error_params[local]:
  !tenv params vals scope n kt vt cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  metis_tac[generated_hashmap_subscript_step_no_type_error]
QED


Theorem generated_hashmap_subscript_step_error_no_type_error_params[local]:
  !tenv params vals scope n kt vt cx e am is_transient slot st1 err st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INR err,st2) ==>
  no_type_error_result (INR err)
Proof
  rpt strip_tac >> drule_all generated_hashmap_subscript_step_no_type_error_params >>
  asm_rewrite_tac[] >> strip_tac >>
  fs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED
Theorem generated_hashmap_array_subscript_step_no_type_error_params[local]:
  !tenv params vals scope n kt t b cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) (ArrayT t b) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT t b))),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> irule generated_hashmap_subscript_step_no_type_error_params >>
  qexistsl [`am`, `cx`, `e`, `is_transient`, `kt`, `n`, `params`, `scope`,
            `slot`, `st1`, `st2`, `tenv`, `vals`, `Type (ArrayT t b)`] >>
  simp[check_value_type_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem generated_hashmap_subscript_step_success_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (HashMapT kt' vt')),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,st2) ==>
  ?slot'. tvl = HashMapRef is_transient slot' kt' vt'
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_success_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type vt) /\ is_ArrayT vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type vt)),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,st2) ==>
  (?av. tvl = Value (ArrayV av)) \/
  (?is_transient' slot' elem_tv bd. tvl = ArrayRef is_transient' slot' elem_tv bd)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  Cases_on `vt` >> gvs[is_ArrayT_def, check_value_type_def,
                        assignable_type_def, well_formed_type_def,
                        evaluate_type_def, AllCaseEqs(), bind_def,
                        return_def, raise_def, IS_SOME_EXISTS] >>
  rename [`evaluate_type (get_tenv cx) t = SOME elem_tv`,
          `type_slot_size (ArrayTV elem_tv bd)`] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[initial_state_def, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd)` by
    (`evaluate_type (get_tenv cx) (ArrayT t bd) = SOME (ArrayTV elem_tv bd)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_typed_package[local]:
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) elem_ast /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) elem_ast = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT elem_ast bd_ast))),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (INL tvl,step_st) ==>
  ((?av bd. tvl = Value (ArrayV av) /\
            value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient' slot' bd. tvl = ArrayRef is_transient' slot' elem_tv bd))
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `0 < type_slot_size elem_tv /\
            type_slot_size (ArrayTV elem_tv bd_ast) < dimword (:256)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd_ast) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[initial_state_def, bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd_ast)` by
    (`evaluate_type (get_tenv cx) (ArrayT elem_ast bd_ast) = SOME (ArrayTV elem_tv bd_ast)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem build_getter_args_current[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) ==>
    MEM (num_to_dec_string n,kt) args
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem machine_well_typed_get_source_immutables_value_has_type[local]:
  machine_well_typed am /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  value_has_type tv v /\ well_formed_type_value tv
Proof
  rw[machine_well_typed_def] >>
  Cases_on `ALOOKUP am.immutables tx.target` >> gvs[get_source_immutables_def] >>
  `MEM (tx.target,x) am.immutables` by metis_tac[ALOOKUP_MEM] >>
  `imms_well_typed x` by
    (gvs[EVERY_MEM] >>
     qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x)` mp_tac) >>
     simp[]) >>
  gvs[imms_well_typed_def, get_source_immutables_def] >>
  Cases_on `ALOOKUP x src` >> gvs[] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_indexable_carrier[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  (?av. tvl = Value (ArrayV av)) \/
  (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `value_has_type x'0 x'1` by
        (gvs[machine_well_typed_def] >>
         `MEM (tx.target,x'') am.immutables` by metis_tac[ALOOKUP_MEM] >>
         `imms_well_typed x''` by
           (gvs[EVERY_MEM] >>
            qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x'')` mp_tac) >>
            simp[]) >>
         Cases_on `ALOOKUP x'' src` >> gvs[imms_well_typed_def] >>
         metis_tac[]) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `value_has_type x'0 x'1` by
        (gvs[machine_well_typed_def] >>
         `MEM (tx.target,x'') am.immutables` by metis_tac[ALOOKUP_MEM] >>
         `imms_well_typed x''` by
           (gvs[EVERY_MEM] >>
            qpat_x_assum `!x. MEM x am.immutables ==> _` (qspec_then `(tx.target,x'')` mp_tac) >>
            simp[]) >>
         Cases_on `ALOOKUP x'' src` >> gvs[imms_well_typed_def] >>
         metis_tac[]) >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED


Theorem checked_public_array_TopLevelName_typed_indexable_carrier[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) typ =
    SOME (ArrayTV elem_tv bd) /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_state_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) (initial_state am [scope]) = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv b) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv b))
Proof
  rpt strip_tac >>
  irule (Q.INST [`typ` |-> `ArrayT t b`, `bd` |-> `b`]
           checked_public_array_TopLevelName_typed_indexable_carrier) >>
  qexistsl [`am`, `art`, `fn`, `init`, `mods`, `mut`, `scope`, `src`,
            `st'`, `t`, `ts`, `tx`] >>
  simp[is_ArrayT_def, evaluate_type_def, get_tenv_def,
       initial_evaluation_context_def]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) typ =
    SOME (ArrayTV elem_tv bd) /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
    simp[get_module_code_def, initial_evaluation_context_def] >>
  `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type typ)` by
    (`toplevel_vtypes_complete art.cta_toplevel_vtypes
        (initial_evaluation_context am.sources am.layouts tx src)` by
       (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
     gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn typ init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
    (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
     gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, initial_evaluation_context_def] >>
  Cases_on `typ` >> gvs[is_ArrayT_def] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                        well_formed_type_def]
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
        (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
      `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
        (`bare_globals_complete art.cta_bare_globals
            (initial_evaluation_context am.sources am.layouts tx src)` by
           (irule check_contract_bare_globals_complete_initial >> simp[]) >>
         gvs[bare_globals_complete_def] >> metis_tac[]) >>
      gvs[immutables_ready_def] >>
      qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      qpat_x_assum `∀src' id ty tv v. _`
        (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
      simp[initial_evaluation_context_def] >>
      rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
      Cases_on `ALOOKUP am.immutables tx.target` >>
      gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
          bind_def, return_def, raise_def, get_source_immutables_def,
          AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      PairCases_on `x'` >> gvs[] >>
      `FLOOKUP (get_source_immutables src
          (case ALOOKUP am.immutables tx.target of SOME m => m | NONE => []))
         (string_to_num fn) = SOME (ArrayTV elem_tv bd,x'1)` by
        simp[get_source_immutables_def] >>
      `value_has_type (ArrayTV elem_tv bd) x'1 /\
       well_formed_type_value (ArrayTV elem_tv bd)` by
        metis_tac[machine_well_typed_get_source_immutables_value_has_type] >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      Cases_on `x'1` >> gvs[vyperTypingTheory.value_has_type_def] >>
      metis_tac[])
  >- (`find_var_decl_by_num (string_to_num fn) ts =
         SOME (StorageVarDecl T (ArrayT t b),fn)` by
        metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                  contract_namespaces_ok_module_toplevel_vtype_keys,
                  ALOOKUP_MEM, check_contract_def] >>
      gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
          get_tenv_def, initial_evaluation_context_def] >>
      gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
      metis_tac[]) >>
  `find_var_decl_by_num (string_to_num fn) ts =
     SOME (StorageVarDecl F (ArrayT t b),fn)` by
    metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
              contract_namespaces_ok_module_toplevel_vtype_keys,
              ALOOKUP_MEM, check_contract_def] >>
  gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
      get_tenv_def, initial_evaluation_context_def] >>
  gvs[evaluate_type_def, IS_SOME_EXISTS, AllCaseEqs(), bind_def, return_def] >>
  metis_tac[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV elem_tv b) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot elem_tv b))
Proof
  rpt strip_tac >>
  irule (Q.INST [`typ` |-> `ArrayT t b`, `bd` |-> `b`]
           checked_public_array_TopLevelName_typed_indexable_carrier_post_prefix) >>
  qexistsl [`am`, `art`, `fn`, `init`, `mods`, `mut`, `src`,
            `st`, `st'`, `t`, `ts`, `tx`] >>
  simp[is_ArrayT_def, evaluate_type_def, get_tenv_def,
       initial_evaluation_context_def]
QED

Theorem checked_public_array_TopLevelName_materialisable_carrier_ArrayT_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  (?v. tvl = Value v) \/
  (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
Proof
  rpt strip_tac >>
  drule_all checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix_any_bd[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv /\
  0 < type_slot_size elem_tv /\
  type_slot_size (ArrayTV elem_tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  st.immutables = am.immutables /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (INL tvl,st') ==>
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
Proof
  rpt strip_tac >>
  drule_all checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix >>
  simp[] >> strip_tac >> gvs[]
  >- (qexists `b` >> simp[]) >>
  metis_tac[]
QED


Theorem all_have_type_oEL_nested_array[local]:
  all_have_type tv vs /\ oEL j vs = SOME v ==> value_has_type tv v
Proof
  rw[vyperTypingTheory.all_have_type_EVERY, oEL_THM, EVERY_EL] >>
  first_x_assum irule >> simp[]
QED

Theorem sparse_has_type_ALOOKUP_nested_array[local]:
  sparse_has_type tv n sparse /\ ALOOKUP sparse k = SOME v ==>
  value_has_type tv v
Proof
  Induct_on `sparse` >> simp[vyperTypingTheory.value_has_type_def] >>
  Cases >> rw[vyperTypingTheory.value_has_type_def] >>
  Cases_on `q = k` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem typed_ArrayV_array_index_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  array_index (ArrayTV (ArrayTV inner_tv inner_bd) bd) av i = SOME v ==>
  ?av'. v = ArrayV av' /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rpt strip_tac >>
  `value_has_type (ArrayTV inner_tv inner_bd) v` by
    (qspecl_then [`ArrayTV (ArrayTV inner_tv inner_bd) bd`,
                  `ArrayTV inner_tv inner_bd`,`bd`,`av`,`i`,`v`]
       mp_tac vyperAssignPreservesTypeTheory.array_index_has_type >>
     simp[]) >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem typed_ArrayV_array_index_NoneTV_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  array_index NoneTV av i = SOME v ==>
  ?av'. v = ArrayV av' /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rpt strip_tac >>
  Cases_on `av` >> gvs[vyperValueOperationTheory.array_index_def,
                        vyperTypingTheory.value_has_type_def] >>
  Cases_on `0 <= i` >> gvs[]
  >- (Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def] >>
      drule_all all_have_type_oEL_nested_array >> strip_tac >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def])
  >- (Cases_on `bd` >> gvs[AllCaseEqs(), vyperTypingTheory.value_has_type_def] >>
      drule_all sparse_has_type_ALOOKUP_nested_array >> strip_tac >>
      Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all all_have_type_oEL_nested_array >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem evaluate_subscript_typed_Value_ArrayV_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (Value (ArrayV av)) (IntV i) = INL (INL tvl) ==>
  ?av'. tvl = Value (ArrayV av') /\
        value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rw[evaluate_subscript_def, AllCaseEqs()] >>
  drule_all typed_ArrayV_array_index_nested_carrier >>
  strip_tac >> gvs[]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier[local]:
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) = INL (INL tvl) ==>
  ?av'. tvl = Value (ArrayV av') /\
        value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
Proof
  rw[evaluate_subscript_def, AllCaseEqs()] >>
  drule_all typed_ArrayV_array_index_NoneTV_nested_carrier >>
  strip_tac >> gvs[]
QED


Theorem check_array_bounds_error_not_TypeError_getter[local]:
  check_array_bounds cx tv v st = (INR err,st') ==> !msg. err <> Error (TypeError msg)
Proof
  rpt strip_tac >> Cases_on `tv` >> Cases_on `v` >>
  TRY (Cases_on `b0`) >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  metis_tac[vyperTypeExprSoundnessTheory.get_storage_backend_no_error]
QED

Theorem check_array_bounds_ArrayRef_error_not_TypeError_getter[local]:
  check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i) st =
    (INR err,st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  rpt strip_tac >> Cases_on `bd` >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  metis_tac[vyperTypeExprSoundnessTheory.get_storage_backend_no_error]
QED

Theorem evaluate_subscript_ArrayRef_nested_carrier[local]:
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INL (INL tvl) ==>
  ?slot'. tvl = ArrayRef is_transient slot' inner_tv inner_bd
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_nested_carrier[local]:
  evaluate_subscript tenv NoneTV
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INL (INL tvl) ==>
  ?slot'. tvl = ArrayRef is_transient slot' inner_tv inner_bd
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED
Theorem evaluate_subscript_ArrayRef_nested_error_not_TypeError[local]:
  evaluate_subscript tenv (ArrayTV (ArrayTV inner_tv inner_bd) bd)
    (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM]
QED

Theorem generated_array_subscript_step_Value_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL (Value (ArrayV av)),st1) /\
  value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')
   | INR _ => T)
Proof
  rpt strip_tac >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
              <|immutables := am.immutables; logs := []; scopes := [scope];
                accounts := am.accounts; tStorage := am.tStorage|>` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res` >> simp[bind_def, return_def, raise_def]
  >- (Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
          (Value (ArrayV av)) (IntV i)` >> simp[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >> simp[bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
          qpat_x_assum `check_array_bounds _ _ _ _ = (INL _,bounds_st)` (fn th => simp[th, bind_def, ignore_bind_def, return_def, raise_def]) >>
          rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
          gvs[evaluate_subscript_def, AllCaseEqs()] >>
          drule_all evaluate_subscript_typed_Value_ArrayV_nested_carrier >> simp[]) >>
      strip_tac >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      drule_all evaluate_subscript_Value_ArrayV_IntV_error_not_TypeError >> simp[]) >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[check_array_bounds_def, return_def, raise_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
              (Value (ArrayV av)) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x` >> gvs[bind_def, return_def, raise_def] >>
      gvs[evaluate_subscript_def, AllCaseEqs()] >>
      drule_all typed_ArrayV_array_index_nested_carrier >> simp[])
QED

Theorem generated_array_subscript_step_ArrayRef_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd),st1) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => ?slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd
   | INR _ => T)
Proof
  rpt strip_tac >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)
              <|immutables := am.immutables; logs := []; scopes := [scope];
                accounts := am.accounts; tStorage := am.tStorage|>` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res`
  >- (Cases_on `evaluate_subscript (get_tenv cx) (ArrayTV (ArrayTV inner_tv inner_bd) bd)
          (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
      simp[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >> simp[bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
          simp[bind_def, ignore_bind_def, return_def, raise_def] >>
          rpt strip_tac >>
          gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
          gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM] >>
          drule_all evaluate_subscript_ArrayRef_nested_carrier >> simp[]) >>
      rpt strip_tac >>
      qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
      simp[bind_def, ignore_bind_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      drule_all evaluate_subscript_ArrayRef_nested_error_not_TypeError >> simp[]) >>
  simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `bd` >>
  gvs[check_array_bounds_def, bind_def, return_def, raise_def,
      get_storage_backend_def, check_def, assert_def, AllCaseEqs()] >>
  gvs[vyperTypeExprSoundnessTheory.get_storage_backend_no_error] >>
  gvs[evaluate_subscript_def, lift_sum_def, bind_def, ignore_bind_def,
      return_def, raise_def, bound_length_def, AllCaseEqs(), LET_THM] >>
  Cases_on `0 <= i /\ Num i < n'` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs(), LET_THM]
QED

Theorem generated_array_subscript_step_typed_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV (ArrayTV inner_tv inner_bd) bd) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt strip_tac >> gvs[]
  >- (drule_all_then assume_tac generated_array_subscript_step_Value_typed_carrier >> gvs[])
  >- (drule_all_then assume_tac generated_array_subscript_step_Value_typed_carrier >> Cases_on `res` >> gvs[])
  >- (drule_all_then assume_tac generated_array_subscript_step_ArrayRef_typed_carrier >> gvs[]) >>
  drule_all_then assume_tac generated_array_subscript_step_ArrayRef_typed_carrier >> Cases_on `res` >> gvs[]
QED
Theorem build_getter_recursive_base_expr_type_NoneTV_probe[local]:
  evaluate_type tenv (expr_type (Subscript NoneT e idx)) = SOME NoneTV
Proof
  simp[expr_type_def, evaluate_type_def]
QED

Theorem generated_outer_subscript_uses_NoneTV_probe[local]:
  eval_expr cx (Subscript NoneT e idx1) st = (INL tvl,st1) /\
  eval_expr cx idx2 st1 = (INL (Value v),st2) ==>
  eval_expr cx (Subscript NoneT (Subscript NoneT e idx1) idx2) st =
    (do
       check_array_bounds cx tvl v;
       res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV tvl v);
       case res of
       | INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od) st2
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       lift_option_type_def, expr_type_def, evaluate_type_def]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_result_probe[local]:
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) =
    (case array_index NoneTV av i of
     | SOME v => INL (INL (Value v))
     | NONE => INR (RuntimeError "subscript array_index"))
Proof
  simp[evaluate_subscript_def]
QED

Theorem evaluate_subscript_NoneTV_Value_ArrayV_error_not_TypeError_probe[local]:
  evaluate_subscript tenv NoneTV (Value (ArrayV av)) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, AllCaseEqs()]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_result_probe[local]:
  evaluate_subscript tenv NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i) =
    (if 0 <= i /\ Num i < bound_length bd then
       let elem_offset = (case bd of Fixed _ => 0 | Dynamic _ => 1) in
       let slot = base_slot + n2w (elem_offset + Num i * type_slot_size elem_tv) in
       case elem_tv of
       | ArrayTV inner_tv inner_bd => INL (INL (ArrayRef is_transient slot inner_tv inner_bd))
       | _ => INL (INR (is_transient,slot,elem_tv))
     else INR (RuntimeError "subscript array out of bounds"))
Proof
  rw[evaluate_subscript_def]
QED

Theorem evaluate_subscript_NoneTV_ArrayRef_error_not_TypeError_probe[local]:
  evaluate_subscript tenv NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i) = INR err ==>
  !msg. err <> TypeError msg
Proof
  rw[evaluate_subscript_def, AllCaseEqs(), LET_THM]
QED

Theorem Subscript_NoneTV_Value_ArrayV_no_TypeError[local]:
  (do
     check_array_bounds cx (Value (ArrayV av)) (IntV i);
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i));
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rw[check_array_bounds_def, evaluate_subscript_def, lift_sum_def,
     bind_def, ignore_bind_def, return_def, raise_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def,
     AllCaseEqs()] >>
  Cases_on `array_index NoneTV av i` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem Subscript_NoneTV_ArrayRef_no_TypeError[local]:
  (do
     check_array_bounds cx (ArrayRef is_transient base_slot elem_tv bd) (IntV i);
     res <- lift_sum (evaluate_subscript (get_tenv cx) NoneTV (ArrayRef is_transient base_slot elem_tv bd) (IntV i));
     case res of
     | INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od) st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient base_slot elem_tv bd) (IntV i) st` >>
  rename1 `check_array_bounds _ _ _ _ = (bounds_res,bounds_st)` >>
  Cases_on `bounds_res`
  >- (qpat_x_assum `do check_array_bounds _ _ _; _ od _ = _` mp_tac >>
      simp[evaluate_subscript_def, lift_sum_def, bind_def, ignore_bind_def,
           return_def, raise_def, bound_length_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `elem_tv` >>
      Cases_on `0 <= i /\ Num i < bound_length bd` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def,
          AllCaseEqs(), LET_THM] >>
      TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error) >>
      strip_tac >> gvs[]) >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac
  >- (drule Subscript_NoneTV_Value_ArrayV_no_TypeError >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  drule Subscript_NoneTV_ArrayRef_no_TypeError >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem generated_array_subscript_step_NoneTV_materialisable[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => (?v. tvl' = Value v) \/
                  (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error] >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          lift_sum_def, evaluate_subscript_def, AllCaseEqs()] >>
      Cases_on `array_index NoneTV av i` >>
      gvs[bind_def, return_def, raise_def]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot elem_tv bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >> gvs[bind_def, return_def, raise_def]
      >- gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
              vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `r` >> gvs[bind_def, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac
  >- (drule Subscript_NoneTV_Value_ArrayV_no_TypeError >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  drule Subscript_NoneTV_ArrayRef_no_TypeError >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_array_subscript_step_NoneTV_materialisable_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av)) \/
   (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' => (?v. tvl' = Value v) \/
                  (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix] >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i) st` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          lift_sum_def, evaluate_subscript_def, AllCaseEqs()] >>
      Cases_on `array_index NoneTV av i` >>
      gvs[bind_def, return_def, raise_def]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot elem_tv bd) (IntV i) st` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot elem_tv bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >> gvs[bind_def, return_def, raise_def]
      >- gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
              vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `r` >> gvs[bind_def, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  metis_tac[check_array_bounds_error_not_TypeError_getter]
QED

Theorem generated_array_subscript_step_NoneTV_nested_carrier[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (FIRST [irule generated_array_subscript_step_NoneTV_carrier_no_type_error,
            irule (cj 2 generated_array_subscript_step_NoneTV_materialisable)] >>
     gvs[] >> metis_tac[]) >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`]
       mp_tac bind_arguments_scope_covers_uint_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `BaseT (UintT 256)`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
      Cases_on `evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i)` >>
      gvs[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >>
          gvs[bind_def, return_def, raise_def,
              vyperTypeExprSoundnessTheory.no_type_error_result_def]
          >- (drule_all evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier >>
              strip_tac >> metis_tac[]) >>
          gvs[evaluate_subscript_def, AllCaseEqs()]) >>
      gvs[evaluate_subscript_def, AllCaseEqs()]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)
                    <|immutables := am.immutables; logs := []; scopes := [scope];
                      accounts := am.accounts; tStorage := am.tStorage|>` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >>
      gvs[bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `x` >> gvs[bind_def, return_def, raise_def,
                               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `y'` >> gvs[bind_def, return_def, raise_def,
                                 vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `r'` >> gvs[bind_def, return_def, raise_def,
                                vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `read_storage_slot cx q q' r'' r` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `q''` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
           strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      TRY (drule_all evaluate_subscript_NoneTV_ArrayRef_nested_carrier >>
           strip_tac >> metis_tac[])) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule check_array_bounds_ArrayRef_error_not_TypeError_getter >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
QED

Theorem eval_stmts_single_Return_no_type_error[local]:
  eval_expr cx e st = (expr_res,st1) /\
  no_type_error_result expr_res /\

  (!tv mat_res st2.
     expr_res = INL tv /\ materialise cx tv st1 = (mat_res,st2) ==>
     no_type_error_result mat_res) /\
  eval_stmts cx [Return (SOME e)] st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def, bind_def, ignore_bind_def,
       return_def, raise_def] >>
  Cases_on `expr_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `materialise cx x st1` >> gvs[return_def, raise_def] >>
  Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem TopLevelName_missing_address_immutables_RuntimeError_probe:
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code = NONE /\
  ALOOKUP st.immutables cx.txn.target = NONE ==>
  eval_expr cx (TopLevelName ty (src,id)) st =
    (INR (Error (RuntimeError "get_address_immutables")), st)
Proof
  simp[Once evaluate_def, Once lookup_global_def, bind_def,
       lift_option_type_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, raise_def]
QED


Definition call_tx_well_typed_def:
  call_tx_well_typed tx <=>
    tx.value < 2 ** 256 /\
    tx.time_stamp < 2 ** 256 /\
    tx.block_number < 2 ** 256 /\
    tx.blob_base_fee < 2 ** 256 /\
    tx.gas_price < 2 ** 256 /\
    tx.chain_id < 2 ** 256 /\
    tx.gas_limit < 2 ** 256 /\
    tx.base_fee < 2 ** 256 /\
    tx.prev_randao < 2 ** 256
End

Theorem call_tx_well_typed_empty_zero_witness:
  ?tx. tx.args = [] /\ tx.value = 0 /\ call_tx_well_typed tx
Proof
  qexists `empty_call_txn` >>
  simp[empty_call_txn_def, call_tx_well_typed_def]
QED

Theorem call_tx_well_typed_initial_context[local]:
  call_tx_well_typed tx ==>
  context_well_typed (initial_evaluation_context sources layouts tx src)
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_tx_well_typed_initial_context_stk[local]:
  call_tx_well_typed tx ==>
  context_well_typed
    ((initial_evaluation_context sources layouts tx src) with stk := [(src,fn)])
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_external_args_defaults_bind_typed[local]:
  evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
  bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME scope /\
  LIST_REL
    (\v arg. ?tv. evaluate_type (type_env_all_modules all_mods) (SND arg) = SOME tv /\
                   value_has_type tv v)
    (vals ++ dflt_vs) args ==>
  args_values_typed (type_env_all_modules all_mods) args (vals ++ dflt_vs)
Proof
  rw[args_values_typed_def]
  >- (imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_APPEND] >> decide_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >>
  strip_tac >>
  first_x_assum drule >>
  simp[]
QED

Definition checked_contract_runtime_ready_def:
  checked_contract_runtime_ready art mods am tx <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
      (initial_evaluation_context am.sources am.layouts tx NONE)
      am.immutables
End

(* checked_call_external_no_type_error is proved near the end of this file,
   after its explicit-function and public-getter branch helpers. *)

(* ===== Deployment establishes runtime immutable readiness ===== *)

Theorem load_contract_success_cases[local]:
  load_contract am tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <| immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps) |>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE) with in_deploy := T)
      nr mut ts mods args dflts tx.args body ret = (INL v, am_ctor) /\
    am_deployed = am_ctor with sources updated_by CONS (tx.target,mods)
Proof
  rw[load_contract_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[] >>
  Cases_on `lookup_function NONE tx.function_name Deploy
              (case ALOOKUP mods NONE of SOME ts => ts | NONE => [])` >> gvs[] >>
  Cases_on `x'` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `call_external_function
      (am with <|immutables updated_by CONS (tx.target,x);
                exports updated_by CONS (tx.target,exps)|>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx NONE)
         with in_deploy := T)
      q' q (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods q'' q''' tx.args r q''''` >>
  gvs[] >>
  Cases_on `q'''''` >> gvs[] >>
  qexists `a` >> simp[]
QED

Theorem call_external_function_deploy_success_evaluate_all_constants[local]:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) ==>
  ?am_c.
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()]
QED

Theorem deployed_check_contract_bare_globals_consistent[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    ?ts.
      get_module_code
        (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx src) src = SOME ts /\
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      is_bare_global_decl id ts /\
      find_var_decl_by_num id ts = NONE /\
      ty <> NoneT
Proof
  rw[] >>
  drule load_contract_success_cases >>
  strip_tac >> gvs[] >>
  drule check_contract_bare_globals_consistent_initial >>
  simp[] >>
  disch_then (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
  simp[]
QED

Theorem constants_env_preserves_lookup_not_key[local]:
  constants_env cx am addr src ts acc = SOME cenv /\
  ~(MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))) /\
  FLOOKUP acc id = SOME x ==>
  FLOOKUP cenv id = SOME x
Proof
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  Induct_on `ts` >- (rw[constants_env_def] >> gvs[]) >>
  gen_tac >> gen_tac >> Cases_on `h` >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >>
       gvs[constants_env_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  TRY (first_x_assum (qspecl_then [`acc |+ (string_to_num s,(tv,v))`,`cenv`] mp_tac) >>
       simp[FLOOKUP_UPDATE] >> NO_TAC) >>
  first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[]
QED


Theorem constants_env_head_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src)
    ((VariableDecl vis (Constant e) id ty init)::ts))) /\
  constants_env cx am addr src
    ((VariableDecl vis (Constant e) id ty init)::ts) acc = SOME cenv ==>
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs()] >>
  qexists `v` >> simp[] >>
  metis_tac[constants_env_preserves_lookup_not_key, FLOOKUP_UPDATE]
QED
Theorem constants_env_contains_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
  constants_env cx am addr src ts acc = SOME cenv /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `init` >> qid_spec_tac `ty` >> qid_spec_tac `id` >>
  qid_spec_tac `e` >> qid_spec_tac `vis` >>
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >> qid_spec_tac `addr` >>
  qid_spec_tac `am` >> qid_spec_tac `cx` >>
  recInduct constants_env_ind >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  metis_tac[constants_env_head_constant_type, constants_env_preserves_lookup_not_key,
            FLOOKUP_UPDATE]
QED

Theorem merge_constants_preserves_lookup_not_source[local]:
  src <> src' /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP (merge_constants addr src' cenv am).immutables addr of
     | SOME m => m
     | NONE => [])) id = SOME x
Proof
  rw[merge_constants_def, get_source_immutables_set_other,
     empty_immutables_def, alistTheory.ALOOKUP_ADELKEY]
QED

Theorem evaluate_all_constants_preserves_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx am addr mods = SOME am_c /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- (rw[evaluate_all_constants_def] >> gvs[]) >>
  gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum irule >>
  simp[] >>
  qexists `merge_constants addr h0 cenv am` >>
  simp[] >>
  irule merge_constants_preserves_lookup_not_source >>
  simp[]
QED
Theorem evaluate_all_constants_preserves_merged_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx (merge_constants addr src cenv am) addr mods = SOME am_c /\
  FLOOKUP cenv id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  rw[] >>
  drule evaluate_all_constants_preserves_lookup_not_source >>
  disch_then drule >>
  disch_then irule >>
  simp[merge_constants_def, get_source_immutables_set_same,
       empty_immutables_def, FLOOKUP_FUNION]
QED

Theorem evaluate_all_constants_contains_constant_type[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  ?tv v. FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    (string_to_num id) = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def, alistTheory.ALOOKUP_def] >>
  gvs[AllCaseEqs()] >-
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel h0) h1))` by
       gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     drule constants_env_contains_constant_type >>
     disch_then drule >>
     disch_then drule >>
     strip_tac >>
     `FLOOKUP (get_source_immutables h0
        (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
        (string_to_num id) = SOME (tv,v)` by
       (gvs[contract_namespaces_ok_def] >>
        drule evaluate_all_constants_preserves_merged_lookup_not_source >>
        disch_then drule >>
        disch_then drule >>
        simp[]) >>
     qexistsl [`tv`,`v`] >>
     gvs[set_current_module_def, get_tenv_def]) >>
  first_x_assum irule >>
  gvs[contract_namespaces_ok_def] >>
  conj_tac >- metis_tac[] >>
  gvs[contract_keys_def, ALL_DISTINCT_APPEND]
QED

Theorem contract_toplevel_vtype_key_MEM_Variable[local]:
  MEM (src,ts) mods /\ MEM (VariableDecl vis mut id ty init) ts ==>
  MEM ((src : num option),string_to_num id)
    (contract_keys toplevel_vtype_keys_toplevel mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)` >> simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED
Theorem module_toplevel_vtype_key_MEM_Variable_any[local]:
  MEM (VariableDecl vis mut id ty init) ts ==>
  MEM (src,string_to_num id)
    (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,string_to_num id)]` >> simp[] >>
  qexists `VariableDecl vis mut id ty init` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED


Theorem module_immutable_constant_string_nums_distinct[local]:
  !src ts visI idI tyI initI visC e idC tyC slotC.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visC (Constant e) idC tyC slotC) ts ==>
    string_to_num idI <> string_to_num idC
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED
Theorem module_immutable_string_num_type_unique[local]:
  !src ts visI idI tyI initI visJ idJ tyJ initJ.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visJ Immutable idJ tyJ initJ) ts /\
    string_to_num idJ = string_to_num idI ==>
    tyJ = tyI
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED


Theorem constants_do_not_clobber_single_immutable[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis Immutable id_str ty init) ts ==>
  constants_do_not_clobber_bare_globals
    mods (FEMPTY |+ ((src,string_to_num id_str), ty))
Proof
  rw[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE] >>
  gvs[] >>
  rename1 `ALOOKUP mods src0 = SOME ts` >>
  `MEM (src0,ts) mods` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `ALOOKUP mods src0 = SOME ts'` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src0) ts))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
  irule module_immutable_constant_string_nums_distinct >>
  qexistsl [`e`,`init`,`slot`,`src0`,`ts`,`typ`,`ty`,`vis'`,`vis`] >>
  simp[]
QED

Theorem deploy_constants_setup_bare_globals_ready[local]:
  check_contract F layouts target mods = SOME call_art /\
  ALOOKUP sources target = SOME mods /\
  tx.target = target /\
  get_tenv cx = type_env_all_modules mods /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  (!src id ty.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
     IS_SOME (FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id)) /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules mods) ty = SOME tv)
Proof
  rw[check_contract_def] >>
  gvs[]
  >- (rw[] >>
      drule build_contract_type_artifact_bare_globals_sound >>
      disch_then drule >>
      strip_tac >>
      gvs[]
      >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
            (irule initial_immutables_contains_decl >>
             qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
             simp[] >>
             conj_tac
             >- (irule find_var_decl_by_num_NONE_Immutable >>
                 conj_tac
                 >- (qexists `src` >>
                     irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                     metis_tac[alistTheory.ALOOKUP_MEM]) >>
                 metis_tac[]) >>
             metis_tac[is_immutable_decl_MEM]) >>
          gvs[IS_SOME_EXISTS] >>
          qexists `x` >>
          irule evaluate_all_constants_preserves_bare_global_lookup_type >>
          qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
          gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
          gvs[] >>
          metis_tac[constants_do_not_clobber_single_immutable]) >>
      metis_tac[evaluate_all_constants_contains_constant_type, IS_SOME_EXISTS]) >>
  rw[] >>
  `(?ts vis id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis Immutable id_str ty init) ts /\
      id = string_to_num id_str) \/
   (?ts vis e id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
      id = string_to_num id_str)` by
    metis_tac[build_contract_type_artifact_bare_globals_sound] >>
  gvs[]
  >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
        (irule initial_immutables_contains_decl >>
         qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
         simp[] >>
         conj_tac
         >- (irule find_var_decl_by_num_NONE_Immutable >>
             conj_tac
             >- (qexists `src` >>
                 irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                 metis_tac[alistTheory.ALOOKUP_MEM]) >>
             metis_tac[]) >>
         metis_tac[is_immutable_decl_MEM]) >>
      gvs[IS_SOME_EXISTS] >>
      `FLOOKUP
         (get_source_immutables src
            (case ALOOKUP am_c.immutables tx.target of NONE => [] | SOME m => m))
         (string_to_num id_str) = SOME x` by
        (irule evaluate_all_constants_preserves_bare_global_lookup_type >>
         qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
         gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
         metis_tac[constants_do_not_clobber_single_immutable]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
         metis_tac[alistTheory.ALOOKUP_MEM]) >>
      `is_immutable_decl (string_to_num id_str) ts` by
        metis_tac[is_immutable_decl_MEM] >>
      irule initial_immutables_all_bare_global_type >>
      qexistsl [`string_to_num id_str`, `imms`, `mods`, `src`, `ts`, `v`] >>
      gvs[] >>
      metis_tac[module_immutable_string_num_type_unique]) >>
  drule evaluate_all_constants_contains_constant_type >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
      gvs[]
QED

Theorem send_call_value_preserves_tv[local]:
  send_call_value mut cx st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), preserves_tv_def] >>
  TRY (qpat_x_assum `assert _ _ _ = _` mp_tac >> rw[assert_def] >> gvs[]) >>
  imp_res_tac transfer_value_scopes >>
  imp_res_tac transfer_value_immutables >>
  gvs[preserves_tv_def]
QED
Theorem call_lock_action_preserves_tv[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[] >>
  gvs[return_def, raise_def, preserves_tv_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def, preserves_tv_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[preserves_tv_def]
QED

Theorem call_unlock_action_preserves_immutables[local]:
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  gvs[]
QED

Theorem call_body_prefix_preserves_tv[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac call_lock_action_preserves_tv >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

Theorem call_body_prefix_lock_preserves_tv[local]:
  (do
     (case cx.nonreentrant_slot of
        NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
      | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view);
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

Theorem preserves_tv_initial_immutables_lookup[local]:
  !cx am_c env st src id tv x.
    preserves_tv cx (initial_state am_c [env]) st ==>
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
    ?y.
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[preserves_tv_def, initial_state_def] >>
  metis_tac[]
QED

Theorem preserves_tv_unlock_abstract_machine_immutables_lookup[local]:
  preserves_tv cx (initial_state am_c [env]) st_body /\
  st_unlocked.immutables = st_body.immutables /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[abstract_machine_from_state_def] >>
  drule preserves_tv_initial_immutables_lookup >>
  disch_then drule >>
  rw[] >>
  metis_tac[]
QED

Theorem call_external_function_deploy_normal_success_lookup_transport[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INL (),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_deploy_return_success_lookup_transport[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INR (ReturnException v_ret),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_success_result_cases[local]:
  (\(res,st). (res,st))
    (case body_res of
       (INL (), st) =>
         (case unlock st of
            (INL u, st') => (INL NoneV, abstract_machine_from_state srcs exps layouts st')
          | (INR e, st') => (INR e, am))
     | (INR (ReturnException v_ret), st) =>
         (case unlock st of
            (INL u, st') =>
              (case evaluate_type tenv ret of
                 NONE => (INR (Error (RuntimeError "eval ret")), am)
               | SOME tv =>
                   case safe_cast tv v_ret of
                     NONE => (INR (Error (RuntimeError "ext cast ret")), am)
                   | SOME v_cast =>
                       (INL v_cast, abstract_machine_from_state srcs exps layouts st'))
          | (INR e, st') => (INR e, am))
     | (INR e, st) => (INR e, am)) = (INL v, am_out) ==>
  ((?st_body st_unlocked u.
      body_res = (INL (), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked) \/
   (?v_ret st_body st_unlocked u tv v_cast.
      body_res = (INR (ReturnException v_ret), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      evaluate_type tenv ret = SOME tv /\
      safe_cast tv v_ret = SOME v_cast /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked))
Proof
  PairCases_on `body_res` >>
  Cases_on `body_res0` >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem call_external_function_deploy_success_cases[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  ?dflt_vs env.
    evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
    bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME env /\
    ((?st_body st_unlocked u.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INL (), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked) \/
     (?v_ret st_body st_unlocked u tv v_cast.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INR (ReturnException v_ret), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        evaluate_type (type_env_all_modules all_mods) ret = SOME tv /\
        safe_cast tv v_ret = SOME v_cast /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked))
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()] >>
  drule call_external_function_success_result_cases >>
  simp[]
QED

Theorem call_external_function_deploy_success_preserves_immutable_type_tags_from_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[] >-
    (irule call_external_function_deploy_normal_success_lookup_transport >>
     qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `x`] >>
     simp[]) >>
  irule call_external_function_deploy_return_success_lookup_transport >>
  qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `v_ret`, `x`] >>
  simp[]
QED

Theorem send_call_value_preserves_immutables[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     type_check_def, assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_immutables >>
  gvs[]
QED

Theorem call_lock_action_preserves_immutables[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[]
QED


Theorem bind_arguments_length_c53[local]:
  !tenv args vs env.
    bind_arguments tenv args vs = SOME env ==> LENGTH args = LENGTH vs
Proof
  Induct_on `args` >> simp[bind_arguments_def] >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[bind_arguments_def] >>
  Cases_on `evaluate_type tenv h'1` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv args t` >> simp[] >>
  strip_tac >> res_tac
QED

Theorem call_external_function_exact_args_rewrites_c53[local]:
  bind_arguments (type_env_all_modules all_mods) args vals = SOME scope ==>
  LENGTH vals = LENGTH args /\
  DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts = [] /\
  vals ++ [] = vals
Proof
  strip_tac >>
  `LENGTH vals = LENGTH args` by metis_tac[bind_arguments_length_c53] >>
  simp[]
QED

Theorem transfer_value_no_type_error_c53[local]:
  !from to amount st s.
    FST (transfer_value from to amount st) <> INR (Error (TypeError s))
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem transfer_value_accounts_well_typed_c53[local]:
  !from to amount st.
    accounts_well_typed st.accounts ==>
    accounts_well_typed (SND (transfer_value from to amount st)).accounts
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >> decide_tac
QED

Theorem send_call_value_no_type_error_c53[local]:
  no_type_error_eval (send_call_value mut cx st)
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def,
     vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `mut = Payable` >> gvs[return_def, raise_def] >>
  metis_tac[transfer_value_no_type_error_c53]
QED

Theorem send_call_value_preserves_scopes_c53[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem send_call_value_accounts_well_typed_c53[local]:
  accounts_well_typed st.accounts /\
  send_call_value mut cx st = (res,st') ==>
  accounts_well_typed st'.accounts
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  `accounts_well_typed
     (SND (transfer_value cx.txn.sender cx.txn.target cx.txn.value st)).accounts` by
    metis_tac[transfer_value_accounts_well_typed_c53] >>
  gvs[]
QED

Theorem call_lock_action_preserves_accounts_c53[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_action_preserves_scopes_c53[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready_c53[local]:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes_c53 >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem call_lock_action_no_type_error_c53[local]:
  no_type_error_eval
    ((if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem unlock_action_no_type_error_c53[local]:

  no_type_error_eval
    ((if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_send_eval_prefix_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       send_call_value mut cx;
       eval_stmts cx body
     od (initial_state am [scope]))
Proof
  rpt strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `scope_well_typed scope` by
    (qspecl_then [`type_env_all_modules mods`, `args`, `vals`, `scope`] mp_tac
       bind_arguments_scope_well_typed_stmt >>
     simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     gvs[args_values_typed_def]) >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
       bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
                 NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock
                   (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (`r''.scopes = [scope] /\ r''.immutables = am.immutables /\ state_well_typed r''` by
            (irule call_lock_send_prefix_body_state_ready_c53 >>
             simp[bind_def, ignore_bind_def] >>
             qexistsl [`initial_evaluation_context am.sources am.layouts tx src`, `mut`, `nr`] >>
             simp[]) >>
          `accounts_well_typed r.accounts` by
            (imp_res_tac call_lock_action_preserves_accounts_c53 >>
             gvs[initial_state_accounts_well_typed]) >>
          `accounts_well_typed r''.accounts` by
            (imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_eval_def] >>
          irule checked_explicit_external_post_prefix_body_no_type_error_selected >>
          simp[] >>
          qexistsl [`am`, `args`, `art`, `dflts`, `mods`, `mut`, `nr`, `raw`,
                    `ret`, `src`, `ts`, `tx`, `vals`] >>
          simp[]) >>
      `no_type_error_eval
         (send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r)` by
        simp[send_call_value_no_type_error_c53] >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]) >>
  `no_type_error_eval
     ((if nr then
         case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
           NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock
             (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
             (mut = View \/ mut = Pure)
       else return ()) (initial_state am [scope]))` by
    simp[call_lock_action_no_type_error_c53] >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED

Theorem call_external_function_exact_selected_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `scope_well_typed scope` by
    (qspecl_then [`type_env_all_modules mods`, `args`, `vals`, `scope`] mp_tac
       bind_arguments_scope_well_typed_stmt >>
     simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     gvs[args_values_typed_def]) >>
  `no_type_error_eval
     (do
        (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock
               (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
               (mut = View \/ mut = Pure)
         else return ());
        send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
        eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
      od (initial_state am [scope]))` by
    metis_tac[call_lock_send_eval_prefix_no_type_error_c53,
              checked_contract_runtime_ready_def] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      initial_evaluation_context_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  qpat_x_assum `!msg. FST _ <> INR (Error (TypeError msg))`
    (qspec_then `msg` mp_tac) >>
  qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[return_def, raise_def,
        vyperTypeExprSoundnessTheory.no_type_error_eval_def,
        vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >>
  qpat_x_assum
    `(if nr /\ mut <> View /\ mut <> Pure then
        case lookup_nonreentrant_slot am.layouts tx.target of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock tx.target slot
      else return ()) r = (INR y,r'')` mp_tac >>
  Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
  Cases_on `nr` >>
  Cases_on `mut` >>
  gvs[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
      get_transient_storage_def, update_transient_def,
      return_def, raise_def, assert_def, check_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem checked_explicit_external_entry_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  args_values_typed (type_env_all_modules mods) args vals /\
  call_external_function am (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  metis_tac[call_external_function_exact_selected_no_type_error_c53]
QED
Theorem initial_state_immutables[local]:
  (initial_state am scs).immutables = am.immutables
Proof
  simp[initial_state_def]
QED

Theorem preserves_immutables_dom_same_initial_from_mid[local]:
  st0.immutables = am_c.immutables /\
  (?st_mid. st_mid.immutables = am_c.immutables /\
            preserves_immutables_dom cx st_mid st') ==>
  preserves_immutables_dom cx st0 st'
Proof
  rw[preserves_immutables_dom_def] >> metis_tac[]
QED

Theorem preserves_immutables_dom_eq_local[local]:
  st'.immutables = st.immutables ==> preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans_local[local]:
  preserves_immutables_dom cx st1 st2 /\
  preserves_immutables_dom cx st2 st3 ==>
  preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  `?imms2. ALOOKUP st2.immutables cx.txn.target = SOME imms2` by
    (gvs[IS_SOME_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem call_body_prefix_preserves_immutables_dom[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (res,st')) ==>
  preserves_immutables_dom cx (initial_state am_c [env]) st'
Proof
  rw[bind_def, ignore_bind_def] >>
  imp_res_tac call_lock_action_preserves_immutables >>
  gvs[AllCaseEqs()] >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INL (),s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INR e,s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (qpat_x_assum `return () _ = (INL (),s'')` mp_tac >>
       rw[return_def, initial_state_def]) >>
  imp_res_tac send_call_value_preserves_immutables >>
  imp_res_tac eval_stmts_preserves_immutables_addr_dom >>
  imp_res_tac eval_stmts_preserves_immutables_dom >>
  fs[preserves_immutables_dom_def, initial_state_immutables] >> rw[] >> gvs[]
QED

Theorem preserves_immutables_dom_final_lookup_exists_in_initial[local]:
  preserves_immutables_dom cx st0 st_body /\
  st0.immutables = am_c.immutables /\
  st_unlocked.immutables = st_body.immutables /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP st_unlocked.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[preserves_immutables_dom_def] >>
  Cases_on `ALOOKUP am_c.immutables cx.txn.target` >>
  gvs[get_source_immutables_def]
  >- (Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
      gvs[get_source_immutables_def] >>
      qpat_x_assum `!tgt. _` (qspec_then `cx.txn.target` mp_tac) >>
      simp[IS_SOME_EXISTS]) >>
  rename1 `ALOOKUP am_c.immutables cx.txn.target = SOME imms0` >>
  Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP st_body.immutables cx.txn.target = SOME imms1` >>
  qpat_x_assum `!src' n. _`
    (qspecl_then [`src`,`id`] mp_tac) >>
  simp[IS_SOME_EXISTS, EXISTS_PROD]
QED

Theorem call_external_function_deploy_success_final_lookup_source_exists_in_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[]
  >- (imp_res_tac call_body_prefix_preserves_immutables_dom >>
      `st_unlocked.immutables = st_body.immutables` by
        (Cases_on `nr` >> gvs[return_def] >>
         Cases_on `mut = View` >> gvs[return_def] >>
         Cases_on `mut = Pure` >> gvs[return_def] >>
         Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
         imp_res_tac release_nonreentrant_lock_immutables) >>
      gvs[abstract_machine_from_state_def] >>
      irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]) >>
  imp_res_tac call_body_prefix_preserves_immutables_dom >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `nr` >> gvs[return_def] >>
     Cases_on `mut = View` >> gvs[return_def] >>
     Cases_on `mut = Pure` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  gvs[abstract_machine_from_state_def] >>
  irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]
QED

Theorem deploy_call_success_transports_bare_global_readiness_clause[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_assum (irule_at Any) >>
  first_assum (irule_at Any)
QED

Theorem deploy_context_constants_bare_globals_type_ready[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  `(((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps)) with
      immutables updated_by CONS (deploy_tx.target,imms)) =
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
              exports updated_by CONS (deploy_tx.target,exps)|>)` by simp[] >>
  gvs[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  strip_tac >>
  first_x_assum (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`, `imms`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps))`] mp_tac) >>
  gvs[get_tenv_def, initial_evaluation_context_def, alistTheory.ALOOKUP_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv`,`v`] mp_tac) >>
  simp[]
QED

Theorem deploy_call_success_scalar_bare_global_type_from_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret = (INL v_out,am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  gvs[] >>
  rename1 `FLOOKUP _ _ = SOME (tv0,y0)` >>
  `evaluate_type (type_env_all_modules all_mods) ty = SOME tv0` by
    (first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv0`,`y0`] mp_tac) >>
     simp[]) >>
  `?y'.
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y')` by
    (drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
     simp[]) >>
  gvs[]
QED

Theorem deploy_constructor_success_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  irule deploy_call_success_scalar_bare_global_type_from_constants >>
  simp[] >>
  qexistsl
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `am_c`, `am_ctor`, `args`, `body`, `call_art`, `cx0`, `dflts`,
     `id`, `mut`, `nr`, `ret`, `src`, `ts`, `v`, `v'`, `deploy_tx.args`] >>
  gvs[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`src'`,`id'`,`ty'`,`tv'`,`v''`] mp_tac) >>
  simp[]
QED

Theorem evaluate_all_constants_preserves_layouts[local]:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.layouts = am.layouts
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  Cases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs(), merge_constants_def] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_deploy_success_preserves_layouts[local]:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out am_c.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  am_out.layouts = am.layouts
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  drule evaluate_all_constants_preserves_layouts >>
  strip_tac >>
  strip_tac >>
  gvs[abstract_machine_from_state_def]
QED

Theorem load_contract_success_constructor_constants_context[local]:
  load_contract am deploy_tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor am_c.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE deploy_tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      nr mut ts mods args dflts deploy_tx.args body ret = (INL v, am_ctor) /\
    evaluate_all_constants
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      deploy_tx.target mods = SOME am_c /\
    am_ctor.layouts = am.layouts /\
    am_deployed = am_ctor with sources updated_by CONS (deploy_tx.target,mods)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  qspecl_then
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `((initial_evaluation_context ((deploy_tx.target,mods)::am.sources)
          am.layouts deploy_tx NONE) with in_deploy := T)`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`]
    mp_tac call_external_function_deploy_success_evaluate_all_constants >>
  simp[] >> strip_tac >>
  qexists `am_c` >>
  gvs[initial_evaluation_context_def] >>
  qspecl_then
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `<|stk := [(NONE,deploy_tx.function_name)]; txn := deploy_tx;
        sources := (deploy_tx.target,mods)::am.sources; layouts := am.layouts;
        in_deploy := T;
        nonreentrant_slot := lookup_nonreentrant_slot am.layouts deploy_tx.target|>`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`]
    mp_tac call_external_function_deploy_success_preserves_layouts >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_constructor_context_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
    deploy_tx.args body ret = (INL v',am_ctor) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
     deploy_tx.args body ret = (INL v',am_ctor)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  metis_tac[deploy_call_success_scalar_bare_global_type_from_constants]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type
      (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
      ty = SOME tv
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  gvs[get_tenv_def, initial_evaluation_context_def] >>
  irule load_contract_constructor_context_bare_global_type_from_constants >>
  gvs[initial_evaluation_context_def] >>
  qexistsl
    [`am`, `am_c`, `am_ctor`, `args`, `body`, `call_art`, `deploy_tx`,
     `dflts`, `exps`, `id`, `mut`, `nr`, `ret`, `src`, `v`, `v'`] >>
  gvs[]
QED

Theorem deployed_toplevel_vtypes_immutables_ready_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type
       (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
       ty = SOME tv) ==>
  !src id ty ts.
    FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
    get_module_code
      (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE) src = SOME ts ==>
    (!is_transient typ id_str.
       find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
       typ = ty) /\
    (!is_transient kt vt id_str.
       find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
       F) /\
    (find_var_decl_by_num id ts = NONE ==>
     !tv v.
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
       evaluate_type
         (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
         ty = SOME tv)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  `ALOOKUP ((deploy_tx.target,mods)::am_ctor.sources) call_tx.target = SOME mods` by
    simp[] >>
  `(!src id vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype (type_env_all_modules mods) vt) /\
    (!src id ty.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==>
      ?ts is_transient typ id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
        typ = ty /\
        IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str)) /\
    (!src id kt vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
      ?ts is_transient id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str))` by
    (irule check_contract_toplevel_vtypes_consistent_initial >> simp[]) >>
  rpt conj_tac
  >- (Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >> rpt strip_tac >>
     Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
     >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
           (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
     `bare_ty = ty` by
       (drule check_contract_bare_globals_consistent_initial >>
        disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
        simp[get_module_code_def, initial_evaluation_context_def] >>
        rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     gvs[] >>
     qpat_x_assum `!src' id' ty' tv' v'. FLOOKUP call_art.cta_bare_globals (src',id') = SOME ty' /\ FLOOKUP _ id' = SOME (tv',v') ==> _`
       (qspecl_then [`src`,`id`,`bare_ty`,`tv`,`v`] mp_tac) >>
     simp[]
QED

Theorem deploy_context_constants_bare_globals_lookup_exists[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
  ?tv v.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v)
Proof
  rw[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  disch_then (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `am with exports updated_by CONS (deploy_tx.target,exps)`] mp_tac) >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  impl_tac >- gvs[initial_evaluation_context_def] >>
  rw[]
QED

Theorem call_external_function_deploy_success_final_lookup_exists_from_constants[local]:
  !cx am nr mut ts all_mods args dflts vals body ret v am_out am_c src id.
    cx.in_deploy /\
    call_external_function am cx nr mut ts all_mods args dflts vals body ret =
      (INL v, am_out) /\
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id) ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id)
Proof
  rw[IS_SOME_EXISTS, EXISTS_PROD] >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  simp[IS_SOME_EXISTS]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_exists_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id)
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  qspecl_then [`(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am with <|exports updated_by CONS (deploy_tx.target,exps);
              immutables updated_by CONS (deploy_tx.target,imms)|>`,
    `nr`, `mut`, `case ALOOKUP mods NONE of NONE => [] | SOME ts => ts`, `mods`,
    `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`, `src`, `id`]
    mp_tac call_external_function_deploy_success_final_lookup_exists_from_constants >>
  simp[initial_evaluation_context_def] >>
  disch_then irule >>
  conj_tac
  >- (simp[IS_SOME_EXISTS, EXISTS_PROD] >>
      irule deploy_context_constants_bare_globals_lookup_exists >>
      qexistsl [`am`,`call_art`,`exps`,`imms`,`mods`,`ty`] >>
      gvs[]) >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_immutables_ready:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  immutables_ready call_art.cta_bare_globals call_art.cta_toplevel_vtypes
    (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE)
    am_deployed.immutables
Proof
  rw[immutables_ready_def]
  >- (simp[initial_evaluation_context_def] >>
      irule load_contract_deployed_bare_globals_immutables_ready_exists_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `mods`, `ty`] >>
      gvs[])
  >- (irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `v`] >>
      gvs[initial_evaluation_context_def])
  >- (irule (cj 1 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `mods`, `src`, `ts`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >- (strip_tac >>
      irule (cj 2 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `kt`, `mods`, `src`, `ts`, `ty`, `vt`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >> irule (cj 3 deployed_toplevel_vtypes_immutables_ready_clause) >>
     qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `ts`, `v`] >>
     simp[] >>
     rpt strip_tac >>
     drule load_contract_deployed_bare_globals_immutables_ready_clause >>
     simp[] >>
     disch_then drule >>
     simp[] >>
     disch_then (qspecl_then [`src'`, `id'`, `ty'`, `tv'`, `v'`] mp_tac) >>
     simp[initial_evaluation_context_def] >>
     strip_tac >>
     gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_checked_contract_runtime_ready:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME art /\
  call_tx.target = deploy_tx.target ==>
  checked_contract_runtime_ready art mods am_deployed call_tx
Proof
  rw[checked_contract_runtime_ready_def]
  >- (drule load_contract_success_cases >> strip_tac >> gvs[])
  >> irule load_contract_establishes_immutables_ready
  >> qexistsl [`am`, `deploy_tx`, `exps`, `mods`]
  >> simp[]
QED

Theorem generated_array_getter_recursive_step_no_type_error_materialisable[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type vt) (SUC n) = (args',ret,exp) /\
  bind_arguments (get_tenv cx) ((num_to_dec_string n,BaseT (UintT 256))::args') vals = SOME scope /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV inner_tv b) bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV inner_tv b) bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  (case step_res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv b) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv b))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) vt = SOME inner_tv` by
    (qpat_x_assum `evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b)` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  `(!id typ id' typ'.
      MEM (id,typ) ((num_to_dec_string n,BaseT (UintT 256))::args') /\
      MEM (id',typ') ((num_to_dec_string n,BaseT (UintT 256))::args') /\
      string_to_num id' = string_to_num id ==> typ' = typ)` by
    (rpt strip_tac >> gvs[] >>
     imp_res_tac string_to_num_eq_imp >> gvs[] >>
     TRY (metis_tac[build_getter_args_no_current_name]) >>
     metis_tac[build_getter_args_num_unique]) >>
  irule generated_array_subscript_step_NoneTV_nested_carrier >>
  simp[evaluate_type_def] >>
  conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
  >- (qexistsl [`am`, `((num_to_dec_string n,BaseT (UintT 256))::args')`, `bd`,
                `cx`, `e`, `n`, `scope`, `st1`, `step_st`, `get_tenv cx`, `tvl`, `vals`] >>
      simp[] >> rpt strip_tac >> simp[] >>
      imp_res_tac string_to_num_eq_imp >> simp[] >>
      TRY (metis_tac[build_getter_args_no_current_name]) >>
      metis_tac[build_getter_args_num_unique])
  >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
  >- (qexistsl [`am`, `((num_to_dec_string n,BaseT (UintT 256))::args')`, `bd`,
                `cx`, `e`, `n`, `scope`, `st1`, `step_st`, `get_tenv cx`, `tvl`, `vals`] >>
      simp[] >> rpt strip_tac >> simp[] >>
      imp_res_tac string_to_num_eq_imp >> simp[] >>
      TRY (metis_tac[build_getter_args_no_current_name]) >>
      metis_tac[build_getter_args_num_unique])
QED

Theorem generated_array_getter_recursive_step_no_type_error_materialisable_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type vt) (SUC n) = (args',ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b) /\
  eval_expr cx e (initial_state am [scope]) = (INL tvl,st1) /\
  ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV inner_tv b) bd) (ArrayV av)) \/
   (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV inner_tv b) bd)) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  (case step_res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv b) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv b))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) vt = SOME inner_tv` by
    (qpat_x_assum `evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV inner_tv b)` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  irule generated_array_subscript_step_NoneTV_nested_carrier >>
  simp[] >>
  metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]
QED

Theorem generated_array_subscript_base_error_no_type_error[local]:
  eval_expr cx e (initial_state am [scope]) = (INR err, st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx (Subscript NoneT e idx) (initial_state am [scope]) = (step_res, step_st) ==>
  no_type_error_result step_res /\
  (case step_res of INR _ => T | INL _ => T)
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript NoneT e idx) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `no_type_error_result (INR err)` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem build_getter_ArrayT_tail_all_args[local]:
  build_getter e kt (Type (ArrayT vt b)) n = (args,ret,exp) /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) ==>
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type vt) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,kt)::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args) /\
    MEM (num_to_dec_string n,kt) all_args
Proof
  rpt strip_tac >>
  qabbrev_tac `tail = build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (BaseT (UintT 256)) (Type vt) (SUC n)` >>
  PairCases_on `tail` >>
  qexistsl [`tail0`, `tail1`, `tail2`] >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def, is_ArrayT_def, ArrayT_type_def] >>
  strip_tac >> gvs[] >>
  metis_tac[]
QED


Theorem generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient[local]:
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >> Cases_on `base_res` >> gvs[]
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error]
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error] >>
  metis_tac[generated_array_subscript_base_error_no_type_error]
QED
Theorem generated_array_subscript_step_NoneTV_materialisable_ambient[local]:
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt strip_tac
  >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient] >>
  Cases_on `base_res` >> gvs[]
  >- metis_tac[cj 2 generated_array_subscript_step_NoneTV_materialisable]
  >- metis_tac[cj 2 generated_array_subscript_step_NoneTV_materialisable] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_tail_IH_package_ambient[local]:
  build_getter e (BaseT (UintT 256)) (Type (ArrayT vt b)) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) (ArrayT vt b) = SOME (ArrayTV tv b) /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type vt) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,BaseT (UintT 256))::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all build_getter_ArrayT_tail_all_args >> strip_tac >> gvs[] >>
  `MEM (num_to_dec_string n,BaseT (UintT 256)) all_args` by metis_tac[] >>
  conj_tac >- metis_tac[generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient] >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  Cases_on `base_res` >> gvs[]
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[] >> metis_tac[]) 
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_tail_IH_package_ambient_ArrayT[local]:
  build_getter e (BaseT (UintT 256)) (Type (ArrayT t b)) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  ?args_tail ret_tail exp_tail.
    build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
      (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
    args = ((num_to_dec_string n,BaseT (UintT 256))::args_tail) /\
    ret = ret_tail /\ exp = exp_tail /\
    (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT t b) = SOME (ArrayTV tv b)` by
    simp[evaluate_type_def] >>
  drule_all generated_array_getter_ArrayT_tail_IH_package_ambient >>
  simp[]
QED

Theorem ArrayT_type_value_type_size_lt[local]:
  is_ArrayT vt ==> value_type_size (Type (ArrayT_type vt)) < value_type_size (Type vt)
Proof
  Cases_on `vt` >> simp[is_ArrayT_def, ArrayT_type_def]
QED

Theorem build_getter_total[local]:
  ?args ret exp. build_getter e kt vt n = (args,ret,exp)
Proof
  Cases_on `build_getter e kt vt n` >> PairCases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem generated_array_getter_ArrayT_step_carrier_shape_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) all_args /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `base_res` >> gvs[]
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)`
      >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[evaluate_type_def] >>
      qexistsl [`all_args`,`am`,`args_tail`,`cx`,`e`,`exp_tail`,`n`,`ret_tail`,
                `scope`,`st1`,`step_st`,`tenv`,`Value (ArrayV av)`,`vals`,`t`] >>
      simp[evaluate_type_def] >> metis_tac[])
  >- (qsuff_tac `no_type_error_result step_res /\
        (case step_res of
         | INL tvl' =>
             ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
              (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
         | INR _ => T)`
      >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
      irule generated_array_getter_recursive_step_no_type_error_materialisable_ambient >>
      simp[evaluate_type_def] >>
      qexistsl [`all_args`,`am`,`args_tail`,`cx`,`e`,`exp_tail`,`n`,`ret_tail`,
                `scope`,`st1`,`step_st`,`tenv`,`ArrayRef is_transient slot (ArrayTV tv b) bd`,`vals`,`t`] >>
      simp[evaluate_type_def] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. (id = num_to_dec_string n /\ typ = BaseT (UintT 256) \/ MEM (id,typ) args_tail) ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (num_to_dec_string n, BaseT (UintT 256)) all_args` by metis_tac[] >>
  conj_tac
  >- (drule_all generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient >> simp[]) >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  conj_tac
  >- (drule_all generated_array_getter_ArrayT_step_carrier_shape_ambient >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED


Theorem generated_array_getter_expr_no_type_error_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (metis_tac[build_getter_total]) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) (initial_state am [scope])` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `vals`, `scope`, `q`, `r`,
         `res`, `st'`, `cx`, `am`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  drule_all generated_array_subscript_step_NoneTV_carrier_no_type_error_ambient >>
  simp[]
QED

Theorem generated_array_getter_expr_materialisable_shape_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (metis_tac[build_getter_total]) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) (initial_state am [scope])` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_ambient >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `vals`, `scope`, `q`, `r`,
         `res`, `st'`, `cx`, `am`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  drule_all generated_array_subscript_step_NoneTV_materialisable_ambient >>
  simp[]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_ambient_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_array_getter_expr_no_type_error_ambient_aux >> simp[])
  >> drule_all generated_array_getter_expr_materialisable_shape_ambient_aux >> simp[]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_aux[local]:
  !vt e n args ret exp vals scope base_res st1 res st' cx am elem_tv.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments (get_tenv cx) args vals = SOME scope /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e (initial_state am [scope]) = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  irule generated_array_getter_expr_no_type_error_materialisable_ambient_aux >>
  simp[] >> metis_tac[build_getter_args_num_unique]
QED

Theorem build_getter_base_error_no_type_error[local]:
  !e kt vt n args ret exp cx am scope err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e (initial_state am [scope]) = (INR err,st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def]) 
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_materialisable_shape[local]:
  !e kt vt n args ret exp cx am scope err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e (initial_state am [scope]) = (INR err,st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`am`, `cx`, `err`, `scope`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_no_type_error_post_prefix[local]:
  !e kt vt n args ret exp cx st err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e st = (INR err,st1) /\
  no_type_error_result (INR err) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem build_getter_base_error_materialisable_shape_post_prefix[local]:
  !e kt vt n args ret exp cx st err st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  eval_expr cx e st = (INR err,st1) /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (first_x_assum irule >> simp[] >>
      qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
      simp[] >>
      qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def])
  >- (qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`cx`, `err`, `st`, `st'`, `st1`] >>
  simp[] >>
  qpat_x_assum `eval_expr cx e _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def]
QED


Theorem generated_array_subscript_step_NoneTV_nested_carrier_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, BaseT (UintT 256)) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL tvl,st1) /\
  ((?av. tvl = Value (ArrayV av) /\
         value_has_type (ArrayTV (ArrayTV inner_tv inner_bd) bd) (ArrayV av)) \/
   (?is_transient slot. tvl = ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd)) /\
  well_formed_type_value (ArrayTV inner_tv inner_bd) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res /\
  (case res of
   | INL tvl' =>
       ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV inner_tv inner_bd) (ArrayV av')) \/
        (?is_transient slot'. tvl' = ArrayRef is_transient slot' inner_tv inner_bd))
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >-
    (FIRST [irule generated_array_subscript_step_NoneTV_carrier_no_type_error_post_prefix,
            irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix)] >>
     gvs[] >> metis_tac[]) >>
  Cases_on `res` >> gvs[] >>
  `?i entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
             entry.type = BaseTV (UintT 256) /\ entry.assignable /\
             entry.value = IntV i` by
    (irule bind_arguments_scope_covers_generated_uint_ambient >>
     qexistsl [`args`,`tenv`,`vals`] >> simp[] >> metis_tac[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `check_array_bounds cx (Value (ArrayV av)) (IntV i) st` >>
      Cases_on `q` >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
      Cases_on `evaluate_subscript (get_tenv cx) NoneTV (Value (ArrayV av)) (IntV i)` >>
      gvs[lift_sum_def, bind_def, return_def, raise_def]
      >- (Cases_on `x'` >>
          gvs[bind_def, return_def, raise_def,
              vyperTypeExprSoundnessTheory.no_type_error_result_def]
          >- (drule_all evaluate_subscript_NoneTV_Value_ArrayV_nested_carrier >>
              strip_tac >> metis_tac[]) >>
          gvs[evaluate_subscript_def, AllCaseEqs()]) >>
      gvs[evaluate_subscript_def, AllCaseEqs()]) >>
  Cases_on `check_array_bounds cx (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i) st` >>
  Cases_on `q` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, lift_sum_def] >>
  Cases_on `evaluate_subscript (get_tenv cx) NoneTV
              (ArrayRef is_transient slot (ArrayTV inner_tv inner_bd) bd) (IntV i)` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def]
  >- (Cases_on `x'` >>
      gvs[bind_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `x` >> gvs[bind_def, return_def, raise_def,
                               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `y'` >> gvs[bind_def, return_def, raise_def,
                                 vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `r'` >> gvs[bind_def, return_def, raise_def,
                                vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `read_storage_slot cx q q' r'' r` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           Cases_on `q''` >>
           gvs[bind_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
           drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
           strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      TRY (drule_all evaluate_subscript_NoneTV_ArrayRef_nested_carrier >>
           strip_tac >> metis_tac[])) >>
  gvs[evaluate_subscript_def, bound_length_def, AllCaseEqs(), LET_THM,
      bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  TRY (drule check_array_bounds_ArrayRef_error_not_TypeError_getter >>
       strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
QED


Theorem generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix[local]:
  build_getter (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (BaseT (UintT 256)) (Type t) (SUC n) = (args_tail,ret_tail,exp_tail) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. (id = num_to_dec_string n /\ typ = BaseT (UintT 256) \/ MEM (id,typ) args_tail) ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  0 < type_slot_size tv /\
  type_slot_size (ArrayTV tv b) <
    115792089237316195423570985008687907853269984665640564039457584007913129639936 /\
  eval_expr cx e st = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV (ArrayTV tv b) bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot (ArrayTV tv b) bd))
   | INR _ => T) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (step_res,step_st) ==>
  no_type_error_result step_res /\
  pure_expr (Subscript NoneT e (Name NoneT (num_to_dec_string n))) /\
  evaluate_type (get_tenv cx)
    (expr_type (Subscript NoneT e (Name NoneT (num_to_dec_string n)))) = SOME NoneTV /\
  (case step_res of
   | INL tvl' =>
       ((?av' bd'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv bd') (ArrayV av')) \/
        (?is_transient slot' bd'. tvl' = ArrayRef is_transient slot' tv bd'))
   | INR _ => T) /\
  (!id typ. MEM (id,typ) args_tail ==> MEM (id,typ) all_args)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (num_to_dec_string n, BaseT (UintT 256)) all_args` by metis_tac[] >>
  `well_formed_type_value (ArrayTV tv b)` by
    (qsuff_tac `evaluate_type (get_tenv cx) (ArrayT t b) = SOME (ArrayTV tv b)`
     >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
     simp[evaluate_type_def]) >>
  conj_tac
  >- (Cases_on `base_res` >> gvs[]
      >- (irule (cj 1 generated_array_subscript_step_NoneTV_nested_carrier_post_prefix) >> simp[] >> metis_tac[])
      >- (irule (cj 1 generated_array_subscript_step_NoneTV_nested_carrier_post_prefix) >> simp[] >> metis_tac[]) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      simp[] >> strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  conj_tac >- simp[pure_expr_def] >>
  conj_tac >- simp[expr_type_def, evaluate_type_def] >>
  conj_tac
  >- (Cases_on `base_res` >> gvs[]
      >- (qsuff_tac `no_type_error_result step_res /\
            (case step_res of
             | INL tvl' =>
                 ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
                  (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
             | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
          irule generated_array_subscript_step_NoneTV_nested_carrier_post_prefix >> simp[] >> metis_tac[])
      >- (qsuff_tac `no_type_error_result step_res /\
            (case step_res of
             | INL tvl' =>
                 ((?av'. tvl' = Value (ArrayV av') /\ value_has_type (ArrayTV tv b) (ArrayV av')) \/
                  (?is_transient slot'. tvl' = ArrayRef is_transient slot' tv b))
             | INR _ => T)` >- (strip_tac >> Cases_on `step_res` >> gvs[] >> metis_tac[]) >>
          irule generated_array_subscript_step_NoneTV_nested_carrier_post_prefix >> simp[] >> metis_tac[]) >>
      qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, raise_def] >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem generated_array_getter_expr_no_type_error_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\ pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\ no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (irule build_getter_total) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `tenv`, `vals`, `scope`, `q`, `st`, `r`,
         `res`, `st'`, `cx`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `base_res` >> gvs[]
  >- (irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `Value (ArrayV av)`,`vals`] >>
      simp[] >> metis_tac[])
  >- (irule (cj 1 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `ArrayRef is_transient slot elem_tv bd`,`vals`] >>
      simp[] >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_array_getter_expr_materialisable_shape_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\ pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\ no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  completeInduct_on `value_type_size (Type vt)` >> rpt strip_tac >>
  TRY (irule build_getter_total) >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      drule_all generated_array_getter_ArrayT_unfolded_tail_IH_antecedents_post_prefix >>
      strip_tac >> gvs[] >>
      first_x_assum (qspec_then `value_type_size (Type t)` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      disch_then (qspecl_then
        [`Subscript NoneT e (Name NoneT (num_to_dec_string n))`, `SUC n`,
         `args'`, `ret`, `exp`, `tenv`, `vals`, `scope`, `q`, `st`, `r`,
         `res`, `st'`, `cx`, `tv`, `all_args`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  Cases_on `base_res` >> gvs[]
  >- (irule (cj 2 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `Value (ArrayV av)`,`vals`] >>
      simp[] >> metis_tac[])
  >- (irule (cj 2 generated_array_subscript_step_NoneTV_materialisable_post_prefix) >>
      qexistsl [`all_args`,`cx`,`e`,`n`,`scope`,`st`,`st1`,`st'`,`tenv`,
                `ArrayRef is_transient slot elem_tv bd`,`vals`] >>
      simp[] >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, return_def, raise_def]
QED

Theorem generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux[local]:
  !vt e n args ret exp tenv vals scope base_res st st1 res st' cx elem_tv all_args.
  build_getter e (BaseT (UintT 256)) (Type vt) n = (args,ret,exp) /\
  bind_arguments tenv all_args vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) all_args) /\
  (!id typ id' typ'. MEM (id,typ) all_args /\ MEM (id',typ') all_args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  st.scopes = [scope] /\
  pure_expr e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) vt = SOME elem_tv /\
  eval_expr cx e st = (base_res,st1) /\
  no_type_error_result base_res /\
  (case base_res of
   | INL tvl =>
       ((?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd))
   | INR _ => T) /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl' => (?v. tvl' = Value v) \/
                (?is_transient slot elem_tv bd. tvl' = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_array_getter_expr_no_type_error_post_prefix_aux >> simp[]) >>
  drule_all generated_array_getter_expr_materialisable_shape_post_prefix_aux >> simp[]
QED

Theorem generated_hashmap_subscript_step_no_type_error_post_prefix[local]:
  !tenv params vals scope n kt vt cx e st is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  irule Subscript_NoneTV_HashMapRef_no_TypeError >>
  qexistsl [`slot`, `cx`, `is_transient`, `kt`, `entry.value`, `st`, `st2`, `vt`] >>
  simp[]
QED

Theorem generated_hashmap_subscript_step_error_no_type_error_post_prefix[local]:
  !tenv params vals scope n kt vt cx e st is_transient slot st1 err st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INR err,st2) ==>
  no_type_error_result (INR err)
Proof
  rpt strip_tac >>
  qspecl_then [`tenv`,`params`,`vals`,`scope`,`n`,`kt`,`vt`,`cx`,`e`,`st`,
               `is_transient`,`slot`,`st1`,`INR err`,`st2`]
    mp_tac generated_hashmap_subscript_step_no_type_error_post_prefix >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem generated_hashmap_subscript_step_materialisable_post_prefix[local]:
  !tenv params vals scope n kt t cx e st is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type t) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (Type t)),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (res,st2) ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[return_def, raise_def, bind_def, check_value_type_def,
      assignable_type_def, well_formed_type_def] >>
  TRY (Cases_on `res'` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `y` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `read_storage_slot cx q r r' s''` >>
       Cases_on `q'` >> gvs[return_def, raise_def, bind_def]) >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL (v:value),s'') => (INL (Value v),s'')
                 | (INR (err:vyperState$exception),s'') => (INR err,s'')) = (res,st2)` mp_tac >>
  CASE_TAC >> CASE_TAC >>
  gvs[return_def, raise_def, bind_def, vyperStorageTheory.encode_hashmap_key_def] >>
  TRY (Cases_on `q` >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED



Theorem generated_hashmap_subscript_step_success_carrier_post_prefix[local]:
  bind_arguments tenv args vals = SOME scope /\
  MEM (num_to_dec_string n, kt) args /\
  (!id typ id' typ'. MEM (id,typ) args /\ MEM (id',typ') args /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (HashMapT kt' vt')),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INL tvl,st2) ==>
  ?slot'. tvl = HashMapRef is_transient slot' kt' vt'
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `args`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_array_tail_subscript_typed_package_post_prefix[local]:
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  assignable_type (get_tenv cx) elem_ast /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  evaluate_type (get_tenv cx) elem_ast = SOME elem_tv /\
  eval_expr cx e st =
    (INL (HashMapRef is_transient slot kt (Type (ArrayT elem_ast bd_ast))),st1) /\
  st.scopes = [scope] /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st = (INL tvl,step_st) ==>
  ((?av bd. tvl = Value (ArrayV av) /\
            value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
   (?is_transient' slot' bd. tvl = ArrayRef is_transient' slot' elem_tv bd))
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >>
     simp[]) >>
  `st1 = st` by metis_tac[eval_expr_preserves_state] >> gvs[] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  gvs[check_array_bounds_def, ignore_bind_def, lift_sum_def,
      evaluate_subscript_def, evaluate_type_def, LET_THM,
      bind_def, return_def, raise_def] >>
  Cases_on `entry.value` >> gvs[check_array_bounds_def, return_def] >>
  Cases_on `0 < type_slot_size elem_tv /\
            type_slot_size (ArrayTV elem_tv bd_ast) < dimword (:256)` >>
  gvs[bind_def, return_def, raise_def] >>
  Cases_on `read_storage_slot cx is_transient
             (hashmap_slot slot (encode_hashmap_key kt entry.value))
             (ArrayTV elem_tv bd_ast) st` >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  (`well_formed_type_value (ArrayTV elem_tv bd_ast)` by
    (`evaluate_type (get_tenv cx) (ArrayT elem_ast bd_ast) = SOME (ArrayTV elem_tv bd_ast)` by
       simp[evaluate_type_def] >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value])) >>
  drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
  strip_tac >>
  Cases_on `x` >> gvs[vyperTypingTheory.value_has_type_def] >>
  metis_tac[]
QED

Theorem generated_hashmap_getter_expr_no_type_error_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                              assignable_type_def, well_formed_type_def,
                              evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
      irule (cj 1 generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux) >>
      qexistsl [`params`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package_post_prefix >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) vtyp` by
        (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
         simp[Once check_value_type_def]) >>
      `no_type_error_result (INR y)` by
        (drule_all generated_hashmap_subscript_step_error_no_type_error_post_prefix >> simp[]) >>
      drule_all build_getter_base_error_no_type_error_post_prefix >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
  `check_value_type (get_tenv cx) vtyp` by
    (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
     simp[Once check_value_type_def]) >>
  `no_type_error_result (INR y)` by
    (drule_all generated_hashmap_subscript_step_error_no_type_error_post_prefix >> simp[]) >>
  drule_all build_getter_base_error_no_type_error_post_prefix >> simp[]
QED

Theorem generated_hashmap_getter_expr_materialisable_shape_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                            assignable_type_def, well_formed_type_def,
                            evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_post_prefix >> simp[]) >>
      irule (cj 2 generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux) >>
      qexistsl [`params`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package_post_prefix >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_materialisable_post_prefix >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n))) st` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      drule_all build_getter_base_error_materialisable_shape_post_prefix >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier_post_prefix >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`cx`, `is_transient`, `params`, `scope`, `slot'`, `st`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  drule_all build_getter_base_error_materialisable_shape_post_prefix >> simp[]
QED

Theorem generated_hashmap_getter_expr_no_type_error_materialisable_post_prefix[local]:
  !e kt vt n args ret exp tenv params vals scope cx st
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e st = (INL (HashMapRef is_transient slot kt vt),st1) /\
  st.scopes = [scope] /\
  eval_expr cx exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_hashmap_getter_expr_no_type_error_post_prefix >> simp[]) >>
  drule_all generated_hashmap_getter_expr_materialisable_shape_post_prefix >> simp[]
QED


Theorem generated_hashmap_getter_expr_no_type_error[local]:
  !e kt vt n args ret exp tenv params vals scope cx am
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                              assignable_type_def, well_formed_type_def,
                              evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (initial_state am [scope])` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_params >>
         simp[]) >>
      irule (cj 1 generated_array_getter_expr_no_type_error_materialisable_ambient_aux) >>
      qexistsl [`params`,`am`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package >>
          simp[] >> metis_tac[]) >>
      metis_tac[])
  >- (drule_all generated_hashmap_subscript_step_no_type_error_params >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
              (initial_state am [scope])` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) vtyp` by
        (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
         simp[Once check_value_type_def]) >>
      `no_type_error_result (INR y)` by
        (drule_all generated_hashmap_subscript_step_error_no_type_error_params >> simp[]) >>
      drule_all build_getter_base_error_no_type_error >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
  `check_value_type (get_tenv cx) vtyp` by
    (qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
     simp[Once check_value_type_def]) >>
  `no_type_error_result (INR y)` by
    (drule_all generated_hashmap_subscript_step_error_no_type_error_params >> simp[]) >>
  drule_all build_getter_base_error_no_type_error >> simp[]
QED

Theorem generated_public_array_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,fn)) (initial_state am [scope])` >>
  `no_type_error_result q` by
    (qunabbrev_tac `cx` >> metis_tac[checked_scalar_public_getter_eval_no_type_error]) >>
  Cases_on `typ` >> gvs[is_ArrayT_def, ArrayT_type_def, Abbr `cx`] >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn (ArrayT t b) init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def] >>
  Cases_on `evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t` >>
  gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
      evaluate_type_def, get_tenv_def, initial_evaluation_context_def] >>
  irule generated_array_getter_expr_no_type_error_materialisable_aux >>
  qexistsl [`am`, `args`, `q`, `initial_evaluation_context am.sources am.layouts tx src`,
            `TopLevelName NoneT (src,fn)`, `x`, `exp`, `0`, `ret`, `scope`,
            `st'`, `r`, `vals`, `t`] >>
  simp[pure_expr_def, expr_type_def, evaluate_type_def,
       get_tenv_def, initial_evaluation_context_def] >>
  Cases_on `q` >> simp[] >>
  `(?av. x' = Value (ArrayV av) /\ value_has_type (ArrayTV x b) (ArrayV av)) \/
   (?is_transient slot. x' = ArrayRef is_transient slot x b)` suffices_by metis_tac[] >>
  irule checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT >>
  simp[get_tenv_def, initial_evaluation_context_def] >>
  goal_assum $ drule_at Any >>
  simp[get_tenv_def, initial_evaluation_context_def] >>
  metis_tac[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) (initial_state am [scope])` >>
  `no_type_error_result q` by
    (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_no_type_error]) >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_no_type_error >>
      qexistsl [`am`, `args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  drule_all build_getter_base_error_no_type_error >> simp[]
QED

Theorem generated_hashmap_subscript_step_materialisable_params[local]:
  !tenv params vals scope n kt t cx e am is_transient slot st1 res st2.
  bind_arguments tenv params vals = SOME scope /\
  MEM (num_to_dec_string n, kt) params /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) (Type t) /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt (Type t)),st1) /\
  eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
    (initial_state am [scope]) = (res,st2) ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt strip_tac >>
  `?entry. FLOOKUP scope (string_to_num (num_to_dec_string n)) = SOME entry /\
           evaluate_type tenv kt = SOME entry.type /\ entry.assignable` by
    (qspecl_then [`tenv`, `params`, `vals`, `scope`, `num_to_dec_string n`, `kt`]
       mp_tac bind_arguments_scope_covers_params_getter >>
     simp[] >>
     (impl_tac >-
       (rpt strip_tac >>
        first_x_assum (qspecl_then [`num_to_dec_string n`, `kt`, `id'`, `typ'`] mp_tac) >>
        simp[])) >> simp[]) >>
  `st1 = initial_state am [scope]` by metis_tac[eval_expr_preserves_state] >>
  gvs[initial_state_def] >>
  qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, Once evaluate_def,
       get_scopes_def, lookup_scopes_val_def, bind_def, lift_option_def,
       lift_option_type_def, return_def, raise_def] >>
  Cases_on `entry.value` >> simp[bind_def, return_def, raise_def] >>
  simp[check_array_bounds_def, ignore_bind_def, lift_sum_def,
       evaluate_subscript_def, return_def, raise_def, LET_THM] >>
  rpt strip_tac >> gvs[return_def, raise_def, bind_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[return_def, raise_def, bind_def, check_value_type_def,
      assignable_type_def, well_formed_type_def] >>
  TRY (Cases_on `res'` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `y` >> gvs[return_def, raise_def, bind_def] >>
       Cases_on `read_storage_slot cx q r r' s''` >>
       Cases_on `q'` >> gvs[return_def, raise_def, bind_def]) >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL (v:value),s'') => (INL (Value v),s'')
                 | (INR (err:vyperState$exception),s'') => (INR err,s'')) = (res,st2)` mp_tac >>
  CASE_TAC >> CASE_TAC >>
  gvs[return_def, raise_def, bind_def, vyperStorageTheory.encode_hashmap_key_def] >>
  TRY (Cases_on `q` >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem generated_hashmap_getter_expr_materialisable_shape[local]:
  !e kt vt n args ret exp tenv params vals scope cx am
    is_transient slot st1 res st'.
  build_getter e kt vt n = (args,ret,exp) /\
  bind_arguments tenv params vals = SOME scope /\
  (!id typ. MEM (id,typ) args ==> MEM (id,typ) params) /\
  (!id typ id' typ'. MEM (id,typ) params /\ MEM (id',typ') params /\
      string_to_num id' = string_to_num id ==> typ' = typ) /\
  check_value_type (get_tenv cx) vt /\
  pure_expr e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME NoneTV /\
  eval_expr cx e (initial_state am [scope]) =
    (INL (HashMapRef is_transient slot kt vt),st1) /\
  eval_expr cx exp (initial_state am [scope]) = (res,st') ==>
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[]
  >- (Cases_on `vt` >> gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
                            assignable_type_def, well_formed_type_def,
                            evaluate_type_def, AllCaseEqs(), IS_SOME_EXISTS] >>
      Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
                  (initial_state am [scope])` >> gvs[] >>
      `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      `check_value_type (get_tenv cx) (Type (ArrayT t b))` by
        simp[check_value_type_def, assignable_type_def, well_formed_type_def,
             evaluate_type_def] >>
      `no_type_error_result q` by
        (drule_all generated_hashmap_subscript_step_no_type_error_params >> simp[]) >>
      irule (cj 2 generated_array_getter_expr_no_type_error_materialisable_ambient_aux) >>
      qexistsl [`params`,`am`,`args'`,`q`,`cx`,
                `Subscript NoneT e (Name NoneT (num_to_dec_string n))`,
                `tv`,`exp`,`SUC n`,`ret`,`scope`,`st'`,`r`,`tenv`,`vals`,`t`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      Cases_on `q` >> gvs[]
      >- (conj_tac >- metis_tac[] >>
          `MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_array_tail_subscript_typed_package >>
          simp[] >> metis_tac[]) >>
      metis_tac[]) 
  >- (drule_all generated_hashmap_subscript_step_materialisable_params >> simp[]) >>
  Cases_on `eval_expr cx (Subscript NoneT e (Name NoneT (num_to_dec_string n)))
              (initial_state am [scope])` >> gvs[]
  >- (Cases_on `q` >> gvs[]
      >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
          drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
          first_x_assum irule >>
          simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
          qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
          simp[check_value_type_def] >>
          conj_tac >- metis_tac[] >>
          qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
          simp[Once check_value_type_def]) >>
      drule_all build_getter_base_error_materialisable_shape >> simp[]) >>
  Cases_on `q` >> gvs[]
  >- (`MEM (num_to_dec_string n,kt) params` by metis_tac[] >>
      drule_all generated_hashmap_subscript_step_success_carrier >> strip_tac >> gvs[] >>
      first_x_assum irule >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def, check_value_type_def] >>
      qexistsl [`am`, `cx`, `is_transient`, `params`, `scope`, `slot'`, `st'`, `r`, `tenv`, `vals`] >>
      simp[check_value_type_def] >>
      conj_tac >- metis_tac[] >>
      qpat_x_assum `check_value_type _ (HashMapT _ _)` mp_tac >>
      simp[Once check_value_type_def]) >>
  drule_all build_getter_base_error_materialisable_shape >> simp[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (drule_all generated_public_hashmap_getter_expr_no_type_error >> simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_materialisable_shape >>
      qexistsl [`am`, `args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  drule_all build_getter_base_error_materialisable_shape >> simp[]
QED

Theorem selected_public_getter_expr_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule (cj 1 generated_public_array_getter_expr_no_type_error_materialisable) >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >> metis_tac[checked_scalar_public_getter_eval_no_type_error]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule generated_public_hashmap_getter_expr_no_type_error >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem selected_public_getter_expr_no_type_error_materialisable[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule selected_public_getter_expr_no_type_error >> metis_tac[]) >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule (cj 2 generated_public_array_getter_expr_no_type_error_materialisable) >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >>
      drule_all checked_scalar_public_getter_eval_no_type_error_materialisable >> simp[]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule (cj 2 generated_public_hashmap_getter_expr_no_type_error_materialisable) >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem generated_public_array_getter_args_num_unique[local]:
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type t) 0 =
    (args,ret,exp) ==>
  !id typ id' typ'.
    MEM (id,typ) args /\ MEM (id',typ') args /\
    string_to_num id' = string_to_num id ==> typ' = typ
Proof
  metis_tac[build_getter_args_num_unique]
QED

Theorem checked_public_array_TopLevelName_base_result_for_generated_getter_aux[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn (ArrayT t b) init) ts /\
  st.immutables = am.immutables /\ state_well_typed st /\
  evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME x /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (base_res,r) ==>
  no_type_error_result base_res /\
  (case base_res of
     INL tvl =>
       (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV x bd) (ArrayV av)) \/
       (?is_transient slot bd. tvl = ArrayRef is_transient slot x bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    `get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts` by
      simp[get_module_code_def, initial_evaluation_context_def] >>
    `FLOOKUP art.cta_toplevel_vtypes (src,string_to_num fn) = SOME (Type (ArrayT t b))` by
      (`toplevel_vtypes_complete art.cta_toplevel_vtypes
          (initial_evaluation_context am.sources am.layouts tx src)` by
         (irule check_contract_toplevel_vtypes_complete_initial >> simp[]) >>
       gvs[toplevel_vtypes_complete_def] >> metis_tac[]) >>
    `check_toplevel_decl am.layouts tx.target mods art src
       (VariableDecl Public mut fn (ArrayT t b) init)` by
      metis_tac[check_contract_toplevel_decl_MEM] >>
    `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
      (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
       gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
         return_def, raise_def, initial_evaluation_context_def] >>
    Cases_on `mut` >> gvs[check_toplevel_decl_def, assignable_type_def,
                          well_formed_type_def]
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Constant >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (expr_type e)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`expr_type e`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts = NONE` by
          (irule find_var_decl_by_num_NONE_Immutable >> simp[] >> metis_tac[]) >>
        `FLOOKUP art.cta_bare_globals (src,string_to_num fn) = SOME (ArrayT t b)` by
          (`bare_globals_complete art.cta_bare_globals
              (initial_evaluation_context am.sources am.layouts tx src)` by
             (irule check_contract_bare_globals_complete_initial >> simp[]) >>
           gvs[bare_globals_complete_def] >> metis_tac[]) >>
        gvs[immutables_ready_def] >>
        qpat_x_assum `∀src' id ty. FLOOKUP art.cta_bare_globals (src',id) = SOME ty ⇒ _`
          (qspecl_then [`src`,`string_to_num fn`,`ArrayT t b`] mp_tac) >>
        simp[initial_evaluation_context_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `ALOOKUP am.immutables tx.target` >>
        gvs[get_immutables_def, get_address_immutables_def, lift_option_def,
            bind_def, return_def, raise_def, get_source_immutables_def,
            AllCaseEqs()] >>
        rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
    >- (`find_var_decl_by_num (string_to_num fn) ts =
           SOME (StorageVarDecl T (ArrayT t b),fn)` by
          metis_tac[find_var_decl_by_num_SOME_storage_var_Transient,
                    contract_namespaces_ok_module_toplevel_vtype_keys,
                    ALOOKUP_MEM, check_contract_def] >>
        gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
            get_tenv_def, initial_evaluation_context_def] >>
        drule assignable_type_well_formed >> simp[well_formed_type_def] >>
        strip_tac >> gvs[IS_SOME_EXISTS] >>
        Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
        gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
        imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
        gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    `find_var_decl_by_num (string_to_num fn) ts =
       SOME (StorageVarDecl F (ArrayT t b),fn)` by
      metis_tac[find_var_decl_by_num_SOME_storage_var_Storage,
                contract_namespaces_ok_module_toplevel_vtype_keys,
                ALOOKUP_MEM, check_contract_def] >>
    gvs[lookup_var_slot_from_layout_def, lookup_var_slot_in_layouts_def,
        get_tenv_def, initial_evaluation_context_def] >>
    drule assignable_type_well_formed >> simp[well_formed_type_def] >>
    strip_tac >> gvs[IS_SOME_EXISTS] >>
    Cases_on `x'` >> simp[return_def, bind_def, vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    gvs[AllCaseEqs(), bind_def, return_def] >> rpt strip_tac >> gvs[] >>
    imp_res_tac vyperTypeExprSoundnessTheory.read_storage_slot_error >>
    gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  Cases_on `base_res` >> simp[] >>
  `0 < type_slot_size x /\ type_slot_size (ArrayTV x b) < dimword(:256)` by
    (`check_toplevel_decl am.layouts tx.target mods art src
        (VariableDecl Public mut fn (ArrayT t b) init)` by
       metis_tac[check_contract_toplevel_decl_MEM] >>
     Cases_on `mut` >>
     gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
         evaluate_type_def, get_tenv_def, initial_evaluation_context_def,
         IS_SOME_EXISTS]) >>
  irule checked_public_array_TopLevelName_typed_indexable_carrier_ArrayT_post_prefix_any_bd >>
  simp[] >>
  qexistsl [`am`,`art`,`b`,`fn`,`init`,`mods`,`mut`,`src`,`st`,`r`,`t`,`ts`,`tx`] >>
  gvs[]
QED

Theorem generated_public_array_getter_aux_premises_from_wrapper[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256))
    (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src)
    (TopLevelName NoneT (src,fn)) st = (base_res,st1) ==>
  ?elem_tv.
    no_type_error_result base_res /\
    (!id aty id' aty'. MEM (id,aty) args /\ MEM (id',aty') args /\
       string_to_num id' = string_to_num id ==> aty' = aty) /\
    pure_expr (TopLevelName NoneT (src,fn)) /\
    evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src))
      (expr_type (TopLevelName NoneT (src,fn))) = SOME NoneTV /\
    evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src))
      (ArrayT_type typ) = SOME elem_tv /\
    (case base_res of
       INL tvl =>
         (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
         (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd)
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `typ` >> gvs[is_ArrayT_def, ArrayT_type_def] >>
  rename1 `ArrayT t b` >>
  `check_toplevel_decl am.layouts tx.target mods art src
     (VariableDecl Public mut fn (ArrayT t b) init)` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `mut` >>
  gvs[check_toplevel_decl_def, assignable_type_def, well_formed_type_def,
      IS_SOME_EXISTS] >>
  Cases_on `evaluate_type (type_env_all_modules mods) t` >>
  gvs[evaluate_type_def] >>
  rename1 `evaluate_type (type_env_all_modules mods) t = SOME elem_tv` >>
  `evaluate_type (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) t = SOME elem_tv` by
    simp[get_tenv_def, initial_evaluation_context_def] >>
  qexists `elem_tv` >>
  `no_type_error_result base_res /\
   (case base_res of
      INL tvl =>
        (?av bd. tvl = Value (ArrayV av) /\ value_has_type (ArrayTV elem_tv bd) (ArrayV av)) \/
        (?is_transient slot bd. tvl = ArrayRef is_transient slot elem_tv bd)
    | INR _ => T)` by
    metis_tac[checked_public_array_TopLevelName_base_result_for_generated_getter_aux] >>
  simp[pure_expr_def, expr_type_def, evaluate_type_def,
       get_tenv_def, initial_evaluation_context_def] >>
  metis_tac[generated_public_array_getter_args_num_unique]
QED

Theorem generated_public_array_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\ MEM (VariableDecl Public mut fn typ init) ts /\
  is_ArrayT typ /\
  build_getter (TopLevelName NoneT (src,fn)) (BaseT (UintT 256)) (Type (ArrayT_type typ)) 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
   | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr (initial_evaluation_context am.sources am.layouts tx src)
              (TopLevelName NoneT (src,fn)) st` >>
  drule_all generated_public_array_getter_aux_premises_from_wrapper >>
  strip_tac >>
  qspecl_then
    [`ArrayT_type typ`, `TopLevelName NoneT (src,fn)`, `0`, `args`,
     `ret`, `exp`, `get_tenv (initial_evaluation_context am.sources am.layouts tx src)`,
     `vals`, `scope`, `q`, `st`, `r`, `res`, `st'`,
     `initial_evaluation_context am.sources am.layouts tx src`, `elem_tv`, `args`]
    mp_tac generated_array_getter_expr_no_type_error_materialisable_post_prefix_aux >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  simp[]
QED

Theorem generated_public_hashmap_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\ machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
    (initial_evaluation_context am.sources am.layouts tx src) am.immutables /\
  ALOOKUP mods src = SOME ts /\
  MEM (HashMapDecl Public is_transient id kt vt init) ts /\
  build_getter (TopLevelName NoneT (src,id)) kt vt 0 = (args,ret,exp) /\
  bind_arguments (get_tenv (initial_evaluation_context am.sources am.layouts tx src)) args vals = SOME scope /\
  st.scopes = [scope] /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (
    qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
    Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) st` >>
    Cases_on `q` >> gvs[]
    >- (`?slot. x = HashMapRef is_transient slot kt vt` by
          (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier_post_prefix]) >>
        gvs[] >>
        `check_value_type (get_tenv cx) vt` by
          (qunabbrev_tac `cx` >>
           `check_value_type (type_env_all_modules mods) vt` by
             metis_tac[checked_hashmap_decl_value_type_checked] >>
           gvs[get_tenv_def, initial_evaluation_context_def]) >>
        irule generated_hashmap_getter_expr_no_type_error_post_prefix >>
        qexistsl [`args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                  `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                  `st`, `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
        simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
        metis_tac[build_getter_args_num_unique]) >>
    `no_type_error_result (INR y)` by
      (qunabbrev_tac `cx` >>
       `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
         (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
          gvs[check_contract_def] >> metis_tac[ALOOKUP_MEM]) >>
       `find_var_decl_by_num (string_to_num id) ts =
          SOME (HashMapVarDecl is_transient kt vt,id)` by
         metis_tac[find_var_decl_by_num_SOME_hashmap] >>
       `check_toplevel_decl am.layouts tx.target mods art src
          (HashMapDecl Public is_transient id kt vt init)` by
         metis_tac[check_contract_toplevel_decl_MEM] >>
       qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, lookup_global_def, get_module_code_def,
            initial_evaluation_context_def, bind_def, lift_option_type_def,
            return_def, raise_def, lookup_var_slot_from_layout_def,
            lookup_var_slot_in_layouts_def,
            vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
       gvs[check_toplevel_decl_def, lookup_var_slot_in_layouts_def] >>
       rpt strip_tac >> gvs[IS_SOME_EXISTS, return_def, raise_def,
                            vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
    qspecl_then [`TopLevelName NoneT (src,id)`, `kt`, `vt`, `0`, `args`,
                 `ret`, `exp`, `cx`, `st`, `y`, `r`, `res`, `st'`]
      mp_tac build_getter_base_error_no_type_error_post_prefix >>
    simp[]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx (TopLevelName NoneT (src,id)) st` >>
  Cases_on `q` >> gvs[]
  >- (`?slot. x = HashMapRef is_transient slot kt vt` by
        (qunabbrev_tac `cx` >> metis_tac[checked_public_hashmap_TopLevelName_carrier_post_prefix]) >>
      gvs[] >>
      `check_value_type (get_tenv cx) vt` by
        (qunabbrev_tac `cx` >>
         `check_value_type (type_env_all_modules mods) vt` by
           metis_tac[checked_hashmap_decl_value_type_checked] >>
         gvs[get_tenv_def, initial_evaluation_context_def]) >>
      irule generated_hashmap_getter_expr_materialisable_shape_post_prefix >>
      qexistsl [`args`, `cx`, `TopLevelName NoneT (src,id)`, `exp`,
                `is_transient`, `kt`, `0`, `args`, `ret`, `scope`, `slot`,
                `st`, `st'`, `r`, `get_tenv cx`, `vals`, `vt`] >>
      simp[pure_expr_def, expr_type_def, evaluate_type_def] >>
      metis_tac[build_getter_args_num_unique]) >>
  qspecl_then [`TopLevelName NoneT (src,id)`, `kt`, `vt`, `0`, `args`,
               `ret`, `exp`, `cx`, `st`, `y`, `r`, `res`, `st'`]
    mp_tac build_getter_base_error_materialisable_shape_post_prefix >>
  simp[]
QED

Theorem selected_public_getter_expr_no_type_error_materialisable_post_prefix[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,[Return (SOME exp)]) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\ state_well_typed st /\
  eval_expr (initial_evaluation_context am.sources am.layouts tx src) exp st = (res,st') ==>
  no_type_error_result res /\
  (case res of INL tvl => (?v. tvl = Value v) \/
                           (?is_transient slot elem_tv bd. tvl = ArrayRef is_transient slot elem_tv bd)
             | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  `get_tenv cx = type_env_all_modules mods` by
    simp[Abbr `cx`, get_tenv_def, initial_evaluation_context_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables` by
    (qunabbrev_tac `cx` >> metis_tac[immutables_ready_initial_evaluation_context_source]) >>
  Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
          simp[external_getter_tuple_def, getter_def] >>
          Cases_on `build_getter (TopLevelName NoneT (src,s)) (BaseT (UintT 256))
                      (Type (ArrayT_type t)) 0` >>
          Cases_on `r` >> gvs[] >> strip_tac >> gvs[] >>
          gvs[is_public_getter_decl_def] >>
          irule generated_public_array_getter_expr_no_type_error_materialisable_post_prefix >>
          simp[] >> metis_tac[]) >>
      qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
      simp[external_getter_tuple_def] >> strip_tac >> gvs[is_public_getter_decl_def] >>
      qunabbrev_tac `cx` >>
      drule_all checked_scalar_public_getter_eval_no_type_error_materialisable_post_prefix >> simp[]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule generated_public_hashmap_getter_expr_no_type_error_materialisable_post_prefix >>
  simp[Abbr `cx`] >> metis_tac[]
QED

Theorem checked_public_getter_entry_no_type_error[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
    (initial_state am [scope]) = (res,st') ==>
  no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  `?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         qpat_x_assum `external_getter_tuple _ _ = _` mp_tac >>
         simp[external_getter_tuple_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  Cases_on `eval_expr cx exp (initial_state am [scope])` >>
  irule eval_stmts_single_Return_no_type_error >>
  qexistsl [`cx`, `exp`, `q`, `initial_state am [scope]`, `st'`, `r`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule materialise_getter_result_no_type_error >>
      qexistsl [`cx`, `r`, `st2`, `tv`] >> simp[] >>
      qunabbrev_tac `cx` >>
      drule_all selected_public_getter_expr_no_type_error_materialisable >>
      simp[] >> metis_tac[]) >>
  qunabbrev_tac `cx` >>
  irule (cj 1 selected_public_getter_expr_no_type_error_materialisable) >>
  metis_tac[]
QED

Theorem call_external_function_exact_selected_getter_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `nr = F /\ mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         gvs[external_getter_tuple_def]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
              (initial_state am [scope])` >>
  Cases_on `q` >> gvs[return_def, raise_def]
  >- (`no_type_error_result (FST (eval_stmts
          (initial_evaluation_context am.sources am.layouts tx src) [Return (SOME exp)] r))` by
        (`r = initial_state am [scope]` by
           (qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
            rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
               assert_def, return_def, raise_def] >>
            gvs[AllCaseEqs(), return_def, raise_def]) >>
         gvs[] >>
         Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                    [Return (SOME exp)] (initial_state am [scope])` >>
         drule_all checked_public_getter_entry_no_type_error >>
         simp[]) >>
      Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                  [Return (SOME exp)] r` >>
      Cases_on `q` >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      TRY (Cases_on `e`) >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >>
           gvs[initial_evaluation_context_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
      rpt strip_tac >> gvs[]) >>
  `no_type_error_eval
     (send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
        (initial_state am [scope]))` by simp[send_call_value_no_type_error_c53] >>
  gvs[initial_evaluation_context_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `y` >> gvs[] >>
  TRY (Cases_on `e`) >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >>
       gvs[return_def, raise_def,
           vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem bind_arguments_success_mem_zip_safe_cast[local]:
  !tenv params vals scope id ty raw.
    bind_arguments tenv params vals = SOME scope /\
    MEM ((id,ty),raw) (ZIP (params, vals)) ==>
    ?tv cast_v.
      evaluate_type tenv ty = SOME tv /\
      safe_cast tv raw = SOME cast_v
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem MEM_ZIP_FST[local]:
  !xs ys x y. MEM (x,y) (ZIP (xs,ys)) ==> MEM x xs
Proof
  Induct >> Cases_on `ys` >> rw[ZIP_def] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem bind_arguments_success_flookup_safe_cast[local]:
  !tenv params vals scope id ty raw sv.
    bind_arguments tenv params vals = SOME scope /\
    ALL_DISTINCT (MAP (string_to_num o FST) params) /\
    MEM ((id,ty),raw) (ZIP (params, vals)) /\
    FLOOKUP scope (string_to_num id) = SOME sv ==>
      sv.assignable /\
      ?tv.
        evaluate_type tenv ty = SOME tv /\
        safe_cast tv raw = SOME sv.value /\
        sv.type = tv
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE, MEM_MAP] >>
  gvs[] >>
  imp_res_tac MEM_ZIP_FST >>
  gvs[] >>
  first_x_assum drule >>
  disch_then (qspec_then `sv` mp_tac) >>
  simp[]
QED

Definition abi_cast_value_def:
  abi_cast_value tv v <=> ?raw. safe_cast tv raw = SOME v
End

Definition scope_abi_casts_def:
  scope_abi_casts tenv params vals scope <=>
    !id ty raw sv.
      MEM ((id,ty),raw) (ZIP (params,vals)) /\
      FLOOKUP scope (string_to_num id) = SOME sv ==>
        sv.assignable /\
        ?tv. evaluate_type tenv ty = SOME tv /\
             sv.type = tv /\ safe_cast tv raw = SOME sv.value
End

Theorem bind_arguments_scope_abi_casts[local]:
  bind_arguments tenv params vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) params) ==>
  scope_abi_casts tenv params vals scope
Proof
  rw[scope_abi_casts_def] >>
  drule_all bind_arguments_success_flookup_safe_cast >>
  rw[] >>
  qexists `tv` >> simp[]
QED

Theorem scope_abi_casts_flookup[local]:
  scope_abi_casts tenv params vals scope /\
  MEM ((id,ty),raw) (ZIP (params,vals)) /\
  FLOOKUP scope (string_to_num id) = SOME sv ==>
  sv.assignable /\
  ?tv. evaluate_type tenv ty = SOME tv /\
       sv.type = tv /\ safe_cast tv raw = SOME sv.value
Proof
  rw[scope_abi_casts_def] >>
  first_x_assum (qspecl_then [`id`, `ty`, `raw`, `sv`] mp_tac) >>
  simp[]
QED

Definition raw_abi_runtime_consistent_def:
  raw_abi_runtime_consistent tenv params vals scope env cx st <=>
    env_consistent env cx st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    st.scopes = [scope] /\
    LENGTH params = LENGTH vals /\
    scope_abi_casts tenv params vals scope /\
    EVERY (\(addr,imms). imms_well_typed imms) st.immutables
End

Theorem checked_explicit_external_raw_bind_env_package[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  st.scopes = [scope] /\ st.immutables = am.immutables ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_context_consistent env_body cx /\
    env_scopes_consistent env_body cx st /\
    env_immutables_consistent env_body cx st /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id)
Proof
  strip_tac >> gvs[] >>
  drule_all checked_explicit_external_body_typing_package >>
  strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  conj_tac
  >- (gvs[] >>
      irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >>
      simp[]) >>
  conj_tac
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def] >>
  rw[] >>
  qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
  simp[immutables_ready_def] >>
  strip_tac >>
  first_x_assum drule_all >>
  simp[]
QED


Theorem MEM_ZIP_FST_EXISTS[local]:
  LENGTH xs = LENGTH ys /\ MEM x xs ==> ?y. MEM (x,y) (ZIP (xs,ys))
Proof
  MAP_EVERY qid_spec_tac [`ys`, `x`] >>
  Induct_on `xs` >> Cases_on `ys` >> rw[ZIP_def] >> gvs[] >>
  metis_tac[]
QED

Theorem lookup_scopes_val_from_lookup_scopes[local]:
  lookup_scopes n scs = SOME sv ==> lookup_scopes_val n scs = SOME sv.value
Proof
  Induct_on `scs` >> rw[lookup_scopes_def, lookup_scopes_val_def] >>
  gvs[AllCaseEqs()]
QED

Theorem raw_abi_scope_lookup_safe_cast_origin[local]:
  raw_abi_runtime_consistent tenv params vals scope env cx st /\
  MEM (id,ty) params /\
  FLOOKUP env.var_types (string_to_num id) = SOME ty /\
  lookup_scopes (string_to_num id) st.scopes = SOME sv ==>
  ?tv raw.
    MEM ((id,ty),raw) (ZIP (params,vals)) /\
    evaluate_type tenv ty = SOME tv /\
    sv.type = tv /\ safe_cast tv raw = SOME sv.value
Proof
  strip_tac >>
  `?raw0. MEM ((id,ty),raw0) (ZIP (params,vals))` by
    metis_tac[raw_abi_runtime_consistent_def, MEM_ZIP_FST_EXISTS] >>
  gvs[raw_abi_runtime_consistent_def] >>
  `FLOOKUP scope (string_to_num id) = SOME sv` by
    gvs[lookup_scopes_def, AllCaseEqs()] >>
  drule_all scope_abi_casts_flookup >>
  rw[] >> qexists `raw0` >> simp[]
QED

Theorem raw_abi_env_lookup_safe_cast_origin[local]:
  raw_abi_runtime_consistent tenv params vals scope env cx st /\
  (!n ty. FLOOKUP env.var_types n = SOME ty ==>
          ?id. MEM (id,ty) params /\ n = string_to_num id) /\
  FLOOKUP env.var_types n = SOME ty /\
  lookup_scopes n st.scopes = SOME sv ==>
  ?id raw tv.
    MEM (id,ty) params /\ n = string_to_num id /\
    MEM ((id,ty),raw) (ZIP (params,vals)) /\
    evaluate_type tenv ty = SOME tv /\
    sv.type = tv /\ safe_cast tv raw = SOME sv.value
Proof
  strip_tac >>
  first_x_assum drule >>
  strip_tac >> gvs[] >>
  drule_all raw_abi_scope_lookup_safe_cast_origin >>
  rw[] >>
  qexistsl [`id`, `raw`] >> simp[]
QED
Definition raw_abi_formal_scope_ready_def:
  raw_abi_formal_scope_ready tenv params vals scope env cx st <=>
    raw_abi_runtime_consistent tenv params vals scope env cx st /\
    (!n ty. FLOOKUP env.var_types n = SOME ty ==>
            ?id. MEM (id,ty) params /\ n = string_to_num id)
End

Theorem raw_abi_formal_scope_ready_soundness_preconditions_weak[local]:
  raw_abi_formal_scope_ready tenv params vals scope env cx st ==>
  env_consistent env cx st /\ context_well_typed cx /\ accounts_well_typed st.accounts
Proof
  rw[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def]
QED


Theorem raw_abi_formal_lookup_safe_cast_origin[local]:
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  FLOOKUP env.var_types n = SOME ty /\
  lookup_scopes n st.scopes = SOME sv ==>
  ?id raw tv.
    MEM (id,ty) params /\ n = string_to_num id /\
    MEM ((id,ty),raw) (ZIP (params,vals)) /\
    evaluate_type tenv ty = SOME tv /\
    sv.type = tv /\ safe_cast tv raw = SOME sv.value
Proof
  rw[raw_abi_formal_scope_ready_def] >>
  drule_all raw_abi_env_lookup_safe_cast_origin >>
  rw[] >>
  qexistsl [`id`, `raw`, `tv`] >> simp[]
QED


Theorem raw_abi_eval_Name_no_type_error[local]:
  raw_abi_runtime_consistent tenv params vals scope env cx st /\
  MEM (id,ty) params /\
  FLOOKUP env.var_types (string_to_num id) = SOME ty /\
  lookup_scopes (string_to_num id) st.scopes = SOME sv ==>
  no_type_error_eval (eval_expr cx (Name ty id) st)
Proof
  strip_tac >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def, return_def,
     vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_abi_eval_Name_well_typed_no_type_error[local]:
  well_typed_expr env (Name ty id) /\
  raw_abi_runtime_consistent tenv params vals scope env cx st ==>
  no_type_error_eval (eval_expr cx (Name ty id) st)
Proof
  strip_tac >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv` by
    (gvs[well_typed_expr_def, raw_abi_runtime_consistent_def,
         env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
     metis_tac[]) >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def, return_def,
     vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_abi_formal_eval_Name_well_typed_no_type_error[local]:
  well_typed_expr env (Name ty id) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st ==>
  no_type_error_eval (eval_expr cx (Name ty id) st)
Proof
  rw[raw_abi_formal_scope_ready_def] >>
  irule raw_abi_eval_Name_well_typed_no_type_error >>
  metis_tac[]
QED

Theorem raw_abi_formal_eval_Name_safe_cast_origin[local]:
  well_typed_expr env (Name ty id) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  eval_expr cx (Name ty id) st = (INL (Value v),st') ==>
  ?id' raw tv.
    MEM (id',ty) params /\ string_to_num id = string_to_num id' /\
    MEM ((id',ty),raw) (ZIP (params,vals)) /\
    evaluate_type tenv ty = SOME tv /\
    safe_cast tv raw = SOME v /\ st' = st
Proof
  strip_tac >>
  `FLOOKUP env.var_types (string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv` by
    (gvs[well_typed_expr_def, raw_abi_formal_scope_ready_def,
         raw_abi_runtime_consistent_def, env_consistent_def,
         env_scopes_consistent_def, IS_SOME_EXISTS] >>
     metis_tac[]) >>
  drule_all raw_abi_formal_lookup_safe_cast_origin >>
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
     return_def] >>
  qexistsl [`id'`, `raw`] >> simp[]
QED
Definition raw_expr_value_ok_def:
  raw_expr_value_ok tenv ty tv <=>
    (?rt. evaluate_type tenv ty = SOME rt /\ toplevel_value_typed tv rt) \/
    (?rt raw v. tv = Value v /\ evaluate_type tenv ty = SOME rt /\
                safe_cast rt raw = SOME v)
End

Theorem raw_expr_value_ok_typed[local]:
  evaluate_type tenv ty = SOME rt /\
  toplevel_value_typed tv rt ==>
  raw_expr_value_ok tenv ty tv
Proof
  rw[raw_expr_value_ok_def] >> metis_tac[]
QED

Theorem expr_result_typed_raw_expr_value_ok[local]:
  well_typed_expr env e /\ expr_result_typed env e tv ==>
  raw_expr_value_ok env.type_defs (expr_type e) tv
Proof
  rw[expr_result_typed_def, vyperTypeExprSoundnessTheory.expr_runtime_typed_def] >>
  irule raw_expr_value_ok_typed >>
  metis_tac[]
QED

Definition raw_expr_values_ok_def:
  raw_expr_values_ok tenv es vs <=>
    LIST_REL (\e v. raw_expr_value_ok tenv (expr_type e) (Value v)) es vs
End

Theorem exprs_runtime_typed_raw_expr_values_ok[local]:
  well_typed_exprs env es /\ exprs_runtime_typed env es vs ==>
  raw_expr_values_ok env.type_defs es vs
Proof
  rw[raw_expr_values_ok_def, vyperTypeExprSoundnessTheory.exprs_runtime_typed_def] >>
  gvs[LIST_REL_EL_EQN] >>
  rw[] >>
  irule raw_expr_value_ok_typed >>
  gvs[toplevel_value_typed_Value] >>
  metis_tac[]
QED

Theorem raw_expr_value_ok_safe_cast[local]:
  evaluate_type tenv ty = SOME rt /\
  safe_cast rt raw = SOME v ==>
  raw_expr_value_ok tenv ty (Value v)
Proof
  rw[raw_expr_value_ok_def] >> metis_tac[]
QED
Definition raw_var_value_ok_def:
  raw_var_value_ok tenv ty sv <=>
    ?rt. evaluate_type tenv ty = SOME rt /\
         sv.type = rt /\
         raw_expr_value_ok tenv ty (Value sv.value)
End

Definition raw_scope_env_ok_def:
  raw_scope_env_ok tenv env st <=>
    !n ty. FLOOKUP env.var_types n = SOME ty ==>
      ?sv. lookup_scopes n st.scopes = SOME sv /\
           raw_var_value_ok tenv ty sv
End

Definition raw_exec_ready_def:
  raw_exec_ready tenv env cx st <=>
    env_context_consistent env cx /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    env_immutables_consistent env cx st /\
    EVERY (\(addr,imms). imms_well_typed imms) st.immutables /\
    raw_scope_env_ok tenv env st
End

Theorem raw_abi_formal_scope_ready_raw_exec_ready[local]:
  raw_abi_formal_scope_ready tenv params vals scope env cx st ==>
  raw_exec_ready tenv env cx st
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\
   accounts_well_typed st.accounts` by
    metis_tac[raw_abi_formal_scope_ready_soundness_preconditions_weak] >>
  rw[raw_exec_ready_def]
  >- gvs[env_consistent_def]
  >- gvs[env_consistent_def]
  >- gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def]
  >- (rw[raw_scope_env_ok_def, raw_var_value_ok_def] >>
      `?sv. lookup_scopes n st.scopes = SOME sv` by
        (gvs[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
         metis_tac[]) >>
      qexists `sv` >> simp[] >>
      drule_all raw_abi_formal_lookup_safe_cast_origin >>
      strip_tac >>
      simp[] >>
      irule raw_expr_value_ok_safe_cast >>
      qexists `raw` >> simp[])
QED


Theorem raw_exec_ready_type_defs[local]:
  raw_exec_ready (get_tenv cx) env cx st ==>
  env.type_defs = get_tenv cx
Proof
  rw[raw_exec_ready_def, env_context_consistent_def]
QED

Theorem raw_exec_ready_preserve_state_same_static[local]:
  raw_exec_ready tenv env cx st /\
  st'.accounts = st.accounts /\
  st'.immutables = st.immutables /\
  st'.scopes = st.scopes ==>
  raw_exec_ready tenv env cx st'
Proof
  rw[raw_exec_ready_def, env_immutables_consistent_def, raw_scope_env_ok_def] >>
  metis_tac[]
QED

Theorem env_context_consistent_extend_local_raw[local]:
  env_context_consistent env cx ==>
  env_context_consistent (extend_local env n ty a) cx
Proof
  rw[env_context_consistent_def, extend_local_def] >>
  metis_tac[]
QED

Theorem raw_exec_ready_extend_local_new_variable[local]:
  raw_exec_ready tenv env cx st /\
  evaluate_type tenv ty = SOME tv /\
  raw_expr_value_ok tenv ty (Value v) /\
  new_variable id tv v st = (INL u,st') ==>
  raw_exec_ready tenv (extend_local env (string_to_num id) ty T) cx st'
Proof
  strip_tac >>
  gvs[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, set_scopes_def, return_def, raise_def,
      AllCaseEqs(), list_CASE_rator] >>
  rw[raw_exec_ready_def]
  >- (irule env_context_consistent_extend_local_raw >> gvs[raw_exec_ready_def])
  >- gvs[raw_exec_ready_def]
  >- gvs[raw_exec_ready_def]
  >- (gvs[raw_exec_ready_def, env_immutables_consistent_def, extend_local_def] >>
      metis_tac[])
  >- gvs[raw_exec_ready_def]
  >- (gvs[raw_exec_ready_def, raw_scope_env_ok_def, raw_var_value_ok_def,
          extend_local_def, FLOOKUP_UPDATE] >>
      rw[] >> gvs[]
      >- (qexists `<|assignable := T; type := tv; value := v|>` >>
          simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
      first_x_assum drule >> rw[] >>
      qexists `sv` >> simp[] >>
      gvs[lookup_scopes_def, FLOOKUP_UPDATE])
QED


Theorem raw_exec_ready_new_variable_result_ok[local]:
  raw_exec_ready tenv env cx st /\
  st.scopes <> [] /\
  lookup_scopes (string_to_num id) st.scopes = NONE /\
  evaluate_type tenv ty = SOME tv /\
  raw_expr_value_ok tenv ty (Value v) /\
  new_variable id tv v st = (res,st') ==>
  no_type_error_result res /\
  (case res of
   | INL u => raw_exec_ready tenv (extend_local env (string_to_num id) ty T) cx st'
   | INR _ => T)
Proof
  strip_tac >>
  Cases_on `res`
  >- (conj_tac
      >- (qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
          simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
               type_check_def, assert_def, set_scopes_def, return_def, raise_def,
               vyperTypeExprSoundnessTheory.no_type_error_result_def,
               AllCaseEqs(), list_CASE_rator] >>
          Cases_on `st.scopes` >> gvs[]) >>
      drule_all raw_exec_ready_extend_local_new_variable >> simp[]) >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def,
       AllCaseEqs(), list_CASE_rator] >>
  Cases_on `st.scopes` >> gvs[]
QED

Definition raw_stmt_exec_ready_def:
  raw_stmt_exec_ready tenv env cx st <=>
    raw_exec_ready tenv env cx st /\
    st.scopes <> [] /\
    (!n. IS_SOME (lookup_scopes n st.scopes) <=> n IN FDOM env.var_types)
End

Theorem raw_stmt_exec_ready_raw_exec_ready[local]:
  raw_stmt_exec_ready tenv env cx st ==> raw_exec_ready tenv env cx st
Proof
  rw[raw_stmt_exec_ready_def]
QED

Theorem raw_stmt_exec_ready_scopes_nonempty[local]:
  raw_stmt_exec_ready tenv env cx st ==> st.scopes <> []
Proof
  rw[raw_stmt_exec_ready_def]
QED

Theorem raw_stmt_exec_ready_fresh_lookup[local]:
  raw_stmt_exec_ready tenv env cx st /\ id NOTIN FDOM env.var_types ==>
  lookup_scopes id st.scopes = NONE
Proof
  rw[raw_stmt_exec_ready_def] >>
  first_x_assum (qspec_then `id` mp_tac) >>
  Cases_on `lookup_scopes id st.scopes` >> gvs[]
QED

Theorem raw_stmt_exec_ready_new_variable_result_ok[local]:
  raw_stmt_exec_ready tenv env cx st /\
  string_to_num id NOTIN FDOM env.var_types /\
  evaluate_type tenv ty = SOME tv /\
  raw_expr_value_ok tenv ty (Value v) /\
  new_variable id tv v st = (res,st') ==>
  no_type_error_result res /\
  (case res of
   | INL u => raw_stmt_exec_ready tenv (extend_local env (string_to_num id) ty T) cx st'
   | INR _ => T)
Proof
  strip_tac >>
  `st.scopes <> []` by gvs[raw_stmt_exec_ready_def] >>
  `lookup_scopes (string_to_num id) st.scopes = NONE` by
    (irule raw_stmt_exec_ready_fresh_lookup >> metis_tac[]) >>
  `raw_exec_ready tenv env cx st` by gvs[raw_stmt_exec_ready_def] >>
  drule_all raw_exec_ready_new_variable_result_ok >> strip_tac >>
  conj_tac >- simp[] >>
  Cases_on `res` >> gvs[] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, set_scopes_def, return_def, raise_def,
       AllCaseEqs(), list_CASE_rator] >>
  Cases_on `st.scopes` >> gvs[] >>
  strip_tac >> gvs[raw_stmt_exec_ready_def, extend_local_def] >>
  rw[lookup_scopes_def, FLOOKUP_UPDATE, FDOM_FUPDATE] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  gvs[lookup_scopes_def]
QED

Theorem raw_abi_formal_scope_ready_raw_stmt_exec_ready[local]:
  raw_abi_formal_scope_ready tenv params vals scope env cx st ==>
  raw_stmt_exec_ready tenv env cx st
Proof
  strip_tac >>
  rw[raw_stmt_exec_ready_def]
  >- metis_tac[raw_abi_formal_scope_ready_raw_exec_ready]
  >- gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def,
          env_consistent_def, env_scopes_consistent_def]
  >- (gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def,
          env_consistent_def, env_scopes_consistent_def] >>
      eq_tac >> rw[]
      >- (Cases_on `lookup_scopes n st.scopes` >> gvs[] >>
          first_x_assum drule >> simp[FLOOKUP_DEF]) >>
      first_x_assum (qspecl_then [`n`, `env.var_types ' n`] mp_tac) >>
      simp[FLOOKUP_DEF])
QED

Theorem raw_exec_ready_assign_target_scoped_replace_value[local]:
  raw_exec_ready tenv env cx st /\
  FLOOKUP env.var_types (string_to_num id) = SOME ty /\
  evaluate_type tenv ty = SOME tv /\
  raw_expr_value_ok tenv ty (Value v) /\
  assign_target cx (BaseTargetV (ScopedVar id) []) (Replace v) st = (INL ar,st') ==>
  no_type_error_result (INL ar) /\ raw_exec_ready tenv env cx st'
Proof
  strip_tac >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv /\
        raw_var_value_ok tenv ty sv` by
    (gvs[raw_exec_ready_def, raw_scope_env_ok_def] >> metis_tac[]) >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, lift_option_def,
       lift_sum_def, type_check_def, assert_def, ignore_bind_def,
       set_scopes_def, assign_result_def, Once assign_subscripts_def, return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[]
  >- gvs[raise_def] >>
  PairCases_on `x` >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >> gvs[] >>
  gvs[raw_var_value_ok_def] >>
  Cases_on `sv.assignable` >>
  gvs[return_def, bind_def, ignore_bind_def, set_scopes_def, assert_def] >>
  strip_tac >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >> gvs[] >>
  rw[raw_exec_ready_def]
  >- gvs[raw_exec_ready_def]
  >- gvs[raw_exec_ready_def]
  >- gvs[raw_exec_ready_def]
  >- (gvs[raw_exec_ready_def, env_immutables_consistent_def] >> metis_tac[])
  >- gvs[raw_exec_ready_def]
  >- (gvs[raw_exec_ready_def, raw_scope_env_ok_def] >>
      rw[] >>
      Cases_on `n = string_to_num id` >> gvs[]
      >- (qexists `sv with value := v` >>
          gvs[raw_var_value_ok_def] >>
          simp[vyperLookupTheory.lookup_scopes_update]) >>
      first_x_assum drule >> rw[] >>
      qexists `sv'` >> simp[] >>
      qspecl_then [`x0`, `n`, `string_to_num id`, `x1`,
                   `sv with value := v`, `x3`] mp_tac
        vyperTypeEnvPreservationTheory.lookup_scopes_append_fupdate_other >>
      simp[] >>
      metis_tac[listTheory.APPEND, listTheory.APPEND_ASSOC])
QED

Theorem raw_stmt_exec_ready_assign_target_scoped_replace_value[local]:
  raw_stmt_exec_ready tenv env cx st /\
  FLOOKUP env.var_types (string_to_num id) = SOME ty /\
  evaluate_type tenv ty = SOME tv /\
  raw_expr_value_ok tenv ty (Value v) /\
  assign_target cx (BaseTargetV (ScopedVar id) []) (Replace v) st = (INL ar,st') ==>
  no_type_error_result (INL ar) /\ raw_stmt_exec_ready tenv env cx st'
Proof
  strip_tac >>
  `raw_exec_ready tenv env cx st` by gvs[raw_stmt_exec_ready_def] >>
  drule_all raw_exec_ready_assign_target_scoped_replace_value >> strip_tac >>
  conj_tac >- simp[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, lift_option_def,
       lift_sum_def, type_check_def, assert_def, ignore_bind_def,
       set_scopes_def, assign_result_def, Once assign_subscripts_def, return_def, raise_def] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[]
  >- gvs[raise_def] >>
  PairCases_on `x` >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >> gvs[] >>
  Cases_on `x2.assignable` >> gvs[return_def, bind_def, ignore_bind_def, set_scopes_def, assert_def] >>
  strip_tac >> gvs[] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >> gvs[] >>
  `!m. IS_SOME (lookup_scopes m st.scopes) <=> m IN FDOM env.var_types` by
    gvs[raw_stmt_exec_ready_def] >>
  rw[raw_stmt_exec_ready_def] >>
  qabbrev_tac `upd = x2 with value := v` >>
  qpat_x_assum `!m. IS_SOME (lookup_scopes m st.scopes) <=> _`
    (qspec_then `n` mp_tac) >>
  drule (Q.SPECL [`n`, `x0`, `x1`, `string_to_num id`, `upd`, `x3`]
           vyperLookupTheory.lookup_scopes_update_preserves) >>
  simp[Abbr `upd`] >>
  strip_tac >> strip_tac >>
  first_x_assum (qspecl_then [`x3`, `x0`, `x2 with value := v`, `n`] mp_tac) >>
  simp[]
QED

Theorem raw_exec_eval_Name_result_ok[local]:
  well_typed_expr env (Name ty id) /\
  raw_exec_ready tenv env cx st /\
  eval_expr cx (Name ty id) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok tenv (expr_type (Name ty id)) tv /\
                raw_exec_ready tenv env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `FLOOKUP env.var_types (string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv /\
        raw_var_value_ok tenv ty sv` by
    (gvs[raw_exec_ready_def, raw_scope_env_ok_def] >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
     return_def, vyperTypeExprSoundnessTheory.no_type_error_result_def,
     expr_type_def] >>
  gvs[raw_var_value_ok_def]
QED

Theorem raw_exec_BareGlobalName_lookup_ok[local]:
  well_typed_expr env (BareGlobalName ty id) /\
  raw_exec_ready (get_tenv cx) env cx st ==>
  ?rt v.
    FLOOKUP (get_source_immutables (current_module cx)
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
      (string_to_num id) = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ty = SOME rt /\
    value_has_type rt v
Proof
  strip_tac >>
  `FLOOKUP env.bare_globals (env.current_src,string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `env.current_src = current_module cx` by
    gvs[raw_exec_ready_def, env_context_consistent_def] >>
  `IS_SOME (FLOOKUP (get_source_immutables (current_module cx)
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
     (string_to_num id))` by
    (gvs[raw_exec_ready_def, env_immutables_consistent_def] >>
     first_x_assum drule >> simp[]) >>
  pop_assum mp_tac >> simp[IS_SOME_EXISTS] >>
  strip_tac >> PairCases_on `x` >> gvs[] >>
  `evaluate_type (get_tenv cx) ty = SOME x0` by
    (gvs[raw_exec_ready_def, env_immutables_consistent_def] >>
     first_x_assum drule_all >> simp[]) >>
  `imms_well_typed
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])` by
    (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
     gvs[raw_exec_ready_def]
     >- rw[imms_well_typed_def] >>
     rw[] >>
     gvs[EVERY_MEM, FORALL_PROD] >>
     first_x_assum irule >>
     imp_res_tac ALOOKUP_MEM >>
     goal_assum drule) >>
  drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >>
  rw[] >>
  qexistsl [`x0`, `x1`] >> simp[]
QED

Theorem raw_exec_eval_BareGlobalName_result_ok[local]:
  well_typed_expr env (BareGlobalName ty id) /\
  raw_exec_ready (get_tenv cx) env cx st /\
  eval_expr cx (BareGlobalName ty id) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (BareGlobalName ty id)) tv /\
                raw_exec_ready (get_tenv cx) env cx st'
    | INR _ => T
Proof
  strip_tac >>
  drule_all raw_exec_BareGlobalName_lookup_ok >>
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  rw[expr_type_def] >>
  gvs[] >>
  irule raw_expr_value_ok_typed >>
  qexists_tac `rt` >>
  simp[toplevel_value_typed_Value]
QED

Theorem raw_exec_read_storage_slot_result_ok[local]:
  evaluate_type tenv ty = SOME tv /\
  read_storage_slot cx is_transient slot tv st = (rr,st') ==>
    no_type_error_result rr /\
    case rr of
    | INL v => raw_expr_value_ok tenv ty (Value v) /\ st' = st
    | INR _ => T
Proof
  strip_tac >>
  Cases_on `rr` >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (conj_tac
      >- (irule raw_expr_value_ok_typed >>
          qexists `tv` >> simp[toplevel_value_typed_Value] >>
          drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
          strip_tac >>
          drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
          simp[])
      >- metis_tac[vyperStatePreservationTheory.read_storage_slot_state]) >>
  drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
  strip_tac >> gvs[]
QED

Theorem raw_exec_eval_TopLevelName_storage_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_exec_ready (get_tenv cx) env cx st /\
  functions_well_typed cx /\
  FLOOKUP env.bare_globals (src,string_to_num id) = NONE /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_num (string_to_num id) ts = SOME (StorageVarDecl is_transient ty,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tvl => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tvl /\
                 raw_exec_ready (get_tenv cx) env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  simp[] >>
  Cases_on `tv` >>
  gvs[return_def, bind_def, expr_type_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      irule raw_expr_value_ok_typed >>
      qexists `ArrayTV t b` >> simp[toplevel_value_typed_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL v,s'') => (INL (Value v),s'')
                 | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  strip_tac >> gvs[] >>
  drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
  Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_exec_eval_TopLevelName_immutable_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_exec_ready (get_tenv cx) env cx st /\
  functions_well_typed cx /\
  FLOOKUP env.bare_globals (src,string_to_num id) = SOME ty /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tvl => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tvl /\
                 raw_exec_ready (get_tenv cx) env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `?ts. get_module_code cx src = SOME ts /\
        FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty) /\
        is_bare_global_decl (string_to_num id) ts /\
        find_var_decl_by_num (string_to_num id) ts = NONE /\ ty <> NoneT` by
    (gvs[raw_exec_ready_def, env_context_consistent_def] >>
     drule_all env_context_consistent_bare_global_find_NONE >> rw[]) >>
  `IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
      (string_to_num id))` by
    (gvs[raw_exec_ready_def, env_immutables_consistent_def] >>
     first_x_assum drule >> simp[]) >>
  gvs[IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  `evaluate_type (get_tenv cx) ty = SOME x0` by
    (gvs[raw_exec_ready_def, env_immutables_consistent_def] >>
     first_x_assum drule_all >> simp[]) >>
  `imms_well_typed
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])` by
    (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
     gvs[raw_exec_ready_def]
     >- rw[imms_well_typed_def] >>
     rw[] >>
     gvs[EVERY_MEM, FORALL_PROD] >>
     first_x_assum irule >>
     imp_res_tac ALOOKUP_MEM >>
     goal_assum drule) >>
  `value_has_type x0 x1` by
    (drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once lookup_global_def, bind_def, lift_option_type_def,
       get_immutables_def, get_address_immutables_def, lift_option_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[get_source_immutables_def, return_def, raise_def] >>
  rw[expr_type_def] >>
  gvs[] >>
  irule raw_expr_value_ok_typed >>
  qexists `x0` >> simp[toplevel_value_typed_Value]
QED

Theorem raw_exec_bare_globals_agrees_toplevel_type[local]:
  raw_exec_ready (get_tenv cx) env cx st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  FLOOKUP env.bare_globals (src,id) = SOME ty' ==>
  ty' = ty
Proof
  rw[raw_exec_ready_def, env_context_consistent_def] >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> _`
    drule >>
  rw[] >> gvs[]
QED

Theorem raw_exec_eval_TopLevelName_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_exec_ready (get_tenv cx) env cx st /\
  functions_well_typed cx /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tv /\
                raw_exec_ready (get_tenv cx) env cx st'

    | INR _ => T
Proof
  strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)`
  >- (`?ts is_transient typ id_str.
         get_module_code cx src = SOME ts /\
         find_var_decl_by_num (string_to_num id) ts = SOME (StorageVarDecl is_transient typ,id_str) /\
         typ = ty /\
         IS_SOME (evaluate_type (get_tenv cx) typ) /\
         IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
        (gvs[raw_exec_ready_def, env_context_consistent_def] >>
         first_x_assum drule_all >> rw[]) >>
      gvs[IS_SOME_EXISTS] >>
      drule_all raw_exec_eval_TopLevelName_storage_result_ok >> simp[]) >>
  `x = ty` by
    (drule_all raw_exec_bare_globals_agrees_toplevel_type >> simp[]) >>
  gvs[] >>
  drule_all raw_exec_eval_TopLevelName_immutable_result_ok >> simp[]
QED

Theorem raw_exec_materialise_Value_result_ok[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  raw_exec_ready tenv env cx st /\
  materialise cx (Value v) st = (res,st') ==>
  no_type_error_result res /\
  (case res of
   | INL mv => st' = st /\ raw_exec_ready tenv env cx st'
   | INR _ => T)
Proof
  rw[materialise_def, return_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[]
QED

Theorem raw_expr_value_ok_non_None_materialise_result_ok[local]:
  raw_expr_value_ok tenv ty tv /\
  ty <> NoneT /\
  raw_exec_ready tenv env cx st /\
  materialise cx tv st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL v => raw_expr_value_ok tenv ty (Value v) /\ raw_exec_ready tenv env cx st'
  | INR _ => T
Proof
  rw[raw_expr_value_ok_def]
  >- (Cases_on `tv` >>
      gvs[materialise_def, bind_def, return_def, raise_def, toplevel_value_typed_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def]
      >- metis_tac[vyperTypeValuesTheory.evaluate_type_NoneTV_imp_NoneT] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL v,s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (Cases_on `tv` >>
      gvs[materialise_def, bind_def, return_def, raise_def, toplevel_value_typed_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL v,s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_exec_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >>
      gvs[raw_expr_value_ok_def, toplevel_value_typed_Value,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      metis_tac[]) >>
  gvs[materialise_def, return_def, raw_expr_value_ok_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  metis_tac[]
QED


Theorem raw_expr_value_ok_literal[local]:
  well_typed_literal ty lit /\
  evaluate_type tenv ty = SOME rt ==>
  raw_expr_value_ok tenv ty (Value (evaluate_literal lit))
Proof
  rw[raw_expr_value_ok_def] >>
  metis_tac[literal_toplevel_value_typed]
QED
Theorem raw_exec_eval_Literal_result_ok[local]:
  well_typed_expr env (Literal ty lit) /\
  raw_exec_ready (get_tenv cx) env cx st /\
  eval_expr cx (Literal ty lit) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (Literal ty lit)) tv /\
                raw_exec_ready (get_tenv cx) env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[raw_exec_ready_def, env_context_consistent_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rw[expr_type_def] >>
  gvs[well_typed_expr_def, well_formed_type_def, IS_SOME_EXISTS] >>
  drule_all raw_expr_value_ok_literal >> simp[]
QED

Definition raw_exec_expr_ok_def:
  raw_exec_expr_ok tenv env e <=>
    tenv = env.type_defs ==>
    !cx st res st'.
      raw_exec_ready tenv env cx st /\ functions_well_typed cx /\
      eval_expr cx e st = (res,st') ==>
      no_type_error_result res /\
      case res of
      | INL tv => raw_expr_value_ok tenv (expr_type e) tv /\
                  raw_exec_ready tenv env cx st'
      | INR _ => T
End

Definition raw_exec_place_expr_ok_def:
  raw_exec_place_expr_ok tenv env e <=>
    tenv = env.type_defs ==>
    !vt cx st.
      type_place_expr env e = SOME vt /\
      raw_exec_ready tenv env cx st /\ functions_well_typed cx ==>
      raw_exec_ready tenv env cx st
End

Definition raw_exec_place_target_ok_def:
  raw_exec_place_target_ok tenv env tgt <=>
    tenv = env.type_defs ==>
    !vt cx st.
      type_place_target env tgt = SOME vt /\
      raw_exec_ready tenv env cx st /\ functions_well_typed cx ==>
      raw_exec_ready tenv env cx st
End

Definition raw_exec_exprs_ok_def:
  raw_exec_exprs_ok tenv env es <=>
    tenv = env.type_defs ==>
    !cx st res st'.
      raw_exec_ready tenv env cx st /\ functions_well_typed cx /\
      eval_exprs cx es st = (res,st') ==>
      no_type_error_result res /\
      case res of
      | INL vs => raw_expr_values_ok tenv es vs /\
                  raw_exec_ready tenv env cx st'
      | INR _ => T
End

Theorem raw_exec_exprs_cons_non_None_ok[local]:
  raw_exec_expr_ok tenv env e /\
  raw_exec_exprs_ok tenv env es /\
  expr_type e <> NoneT ==>
  raw_exec_exprs_ok tenv env (e::es)
Proof
  rw[raw_exec_expr_ok_def, raw_exec_exprs_ok_def] >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  first_x_assum (qspecl_then [`cx`, `st`, `head_res`, `head_st`] mp_tac) >>
  simp[] >>
  strip_tac >>
  Cases_on `head_res`
  >- (rename1 `eval_expr cx e st = (INL tv,head_st)` >> gvs[] >>
      Cases_on `materialise cx tv head_st` >>
      rename1 `materialise cx tv head_st = (mat_res,mat_st)` >>
      drule_all raw_expr_value_ok_non_None_materialise_result_ok >> strip_tac >>
      Cases_on `mat_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
      >- (rename1 `materialise cx tv head_st = (INL v,mat_st)` >>
          Cases_on `eval_exprs cx es mat_st` >>
          rename1 `eval_exprs cx es mat_st = (tail_res,tail_st)` >>
          gvs[] >>
          first_x_assum (qspecl_then [`cx`, `mat_st`, `tail_res`, `tail_st`] mp_tac) >>
          simp[] >>
          strip_tac >>
          Cases_on `tail_res` >> gvs[raw_expr_values_ok_def] >>
          strip_tac >> gvs[]) >>
      strip_tac >> gvs[]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (strip_tac >> gvs[])
  >- (Cases_on `materialise cx x head_st` >>
      rename1 `materialise cx x head_st = (mat_res,mat_st)` >>
      drule_all raw_expr_value_ok_non_None_materialise_result_ok >> strip_tac >>
      Cases_on `mat_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
      >- (rename1 `materialise cx x head_st = (INL v,mat_st)` >>
          Cases_on `eval_exprs cx es mat_st` >>
          rename1 `eval_exprs cx es mat_st = (tail_res,tail_st)` >>
          gvs[] >>
          first_x_assum (qspecl_then [`cx`, `mat_st`, `tail_res`, `tail_st`] mp_tac) >>
          simp[] >> strip_tac >>
          Cases_on `tail_res` >> gvs[raw_expr_values_ok_def] >>
          strip_tac >> gvs[]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem raw_exec_exprs_all_non_None_ok[local]:
  EVERY (\e. raw_exec_expr_ok tenv env e) es /\
  EVERY (\e. expr_type e <> NoneT) es ==>
  raw_exec_exprs_ok tenv env es
Proof
  Induct_on `es` >> rw[]
  >- (rw[raw_exec_exprs_ok_def] >>
      qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, return_def,
           vyperTypeExprSoundnessTheory.no_type_error_result_def,
           raw_expr_values_ok_def] >>
      rw[] >> gvs[]) >>
  irule raw_exec_exprs_cons_non_None_ok >>
  simp[]
QED

Definition raw_exec_opt_ok_def:
  raw_exec_opt_ok tenv env opt <=>
    tenv = env.type_defs ==>
    case opt of
    | NONE => T
    | SOME e => raw_exec_expr_ok tenv env e
End

Definition raw_exec_named_exprs_ok_def:
  raw_exec_named_exprs_ok tenv env kes <=>
    tenv = env.type_defs ==>
    raw_exec_exprs_ok tenv env (MAP SND kes)
End

Theorem raw_exec_opt_ok_from_expr_ok[local]:
  (case opt of NONE => T | SOME e => raw_exec_expr_ok tenv env e) ==>
  raw_exec_opt_ok tenv env opt
Proof
  Cases_on `opt` >> rw[raw_exec_opt_ok_def]
QED

Theorem raw_exec_named_exprs_all_non_None_ok[local]:
  EVERY (\ke. raw_exec_expr_ok tenv env (SND ke)) kes /\
  EVERY (\ke. expr_type (SND ke) <> NoneT) kes ==>
  raw_exec_named_exprs_ok tenv env kes
Proof
  rw[raw_exec_named_exprs_ok_def] >>
  irule raw_exec_exprs_all_non_None_ok >>
  gvs[EVERY_MAP]
QED

Theorem raw_exec_ready_env_type_defs[local]:
  raw_exec_ready env.type_defs env cx st ==>
  env.type_defs = get_tenv cx
Proof
  rw[raw_exec_ready_def, env_context_consistent_def]
QED

Theorem raw_expr_value_ok_Bool_toplevel_value_typed[local]:
  raw_expr_value_ok tenv (BaseT BoolT) tv ==>
  toplevel_value_typed tv (BaseTV BoolT)
Proof
  rw[raw_expr_value_ok_def] >> gvs[Once evaluate_type_def] >>
  Cases_on `raw` >> gvs[Once vyperValueOperationTheory.safe_cast_def,
                         toplevel_value_typed_Value, vyperTypingTheory.value_has_type_def]
QED

Theorem raw_expr_value_ok_IfExp_true_branch_lift[local]:
  well_typed_expr env (IfExp ty cond e_true e_false) /\
  raw_expr_value_ok tenv (expr_type e_true) tv ==>
  raw_expr_value_ok tenv (expr_type (IfExp ty cond e_true e_false)) tv
Proof
  rw[well_typed_expr_def, expr_type_def] >> metis_tac[]
QED

Theorem raw_expr_value_ok_IfExp_false_branch_lift[local]:
  well_typed_expr env (IfExp ty cond e_true e_false) /\
  raw_expr_value_ok tenv (expr_type e_false) tv ==>
  raw_expr_value_ok tenv (expr_type (IfExp ty cond e_true e_false)) tv
Proof
  rw[well_typed_expr_def, expr_type_def] >> metis_tac[]
QED

Theorem raw_exec_IfExp_switch_BoolV_post[local]:
  well_typed_expr env (IfExp ty cond e_true e_false) /\
  raw_exec_expr_ok env.type_defs env e_true /\
  raw_exec_expr_ok env.type_defs env e_false /\
  raw_exec_ready env.type_defs env cx st /\
  functions_well_typed cx /\
  toplevel_value_typed cond_tv (BaseTV BoolT) /\
  switch_BoolV cond_tv (eval_expr cx e_true) (eval_expr cx e_false) st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL tv => raw_expr_value_ok env.type_defs (expr_type (IfExp ty cond e_true e_false)) tv /\
              raw_exec_ready env.type_defs env cx st'
  | INR _ => T
Proof
  rpt strip_tac >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  Cases_on `b` >> gvs[switch_BoolV_def] >>
  FIRST [
    qpat_assum `eval_expr cx e_true st = (res,st')` kall_tac >>
    qpat_x_assum `raw_exec_expr_ok _ _ e_true` mp_tac >>
    rw[raw_exec_expr_ok_def] >>
    first_x_assum (qspecl_then [`cx`, `st`, `res`, `st'`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    drule_all raw_expr_value_ok_IfExp_true_branch_lift >> simp[],
    qpat_assum `eval_expr cx e_false st = (res,st')` kall_tac >>
    qpat_x_assum `raw_exec_expr_ok _ _ e_false` mp_tac >>
    rw[raw_exec_expr_ok_def] >>
    first_x_assum (qspecl_then [`cx`, `st`, `res`, `st'`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
    drule_all raw_expr_value_ok_IfExp_false_branch_lift >> simp[]
  ]
QED
Theorem raw_exec_IfExp_branch_ok[local]:
  well_typed_expr env (IfExp ty cond e_true e_false) /\
  raw_exec_expr_ok tenv env cond /\
  raw_exec_expr_ok tenv env e_true /\
  raw_exec_expr_ok tenv env e_false ==>
  raw_exec_expr_ok tenv env (IfExp ty cond e_true e_false)
Proof
  rpt strip_tac >>
  simp[raw_exec_expr_ok_def] >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx cond st` >>
  rename1 `eval_expr cx cond st = (cond_res,cond_st)` >>
  qpat_x_assum `raw_exec_expr_ok _ _ cond` mp_tac >>
  simp[raw_exec_expr_ok_def] >>
  disch_then (qspec_then `cx` (qspec_then `st` (qspec_then `cond_res` (qspec_then `cond_st` mp_tac)))) >>
  simp[] >> strip_tac >>
  Cases_on `cond_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (gvs[well_typed_expr_def] >>
      `well_typed_expr env (IfExp (expr_type e_true) cond e_true e_false)` by
        simp[well_typed_expr_def] >>
      drule raw_expr_value_ok_Bool_toplevel_value_typed >> strip_tac >>
      strip_tac >>
      drule_all raw_exec_IfExp_switch_BoolV_post >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  rw[] >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem raw_exec_Name_branch_ok[local]:
  well_typed_expr env (Name ty id) ==>
  raw_exec_expr_ok tenv env (Name ty id)
Proof
  rw[raw_exec_expr_ok_def] >>
  drule_all raw_exec_eval_Name_result_ok >>
  simp[]
QED

Theorem raw_exec_Literal_branch_ok[local]:
  well_typed_expr env (Literal ty lit) ==>
  raw_exec_expr_ok tenv env (Literal ty lit)
Proof
  rw[raw_exec_expr_ok_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rw[expr_type_def] >>
  gvs[well_typed_expr_def, well_formed_type_def, IS_SOME_EXISTS,
      raw_exec_ready_def, env_context_consistent_def] >>
  conj_tac >-
    (irule raw_expr_value_ok_literal >> simp[]) >>
  gvs[]
QED

Theorem raw_exec_BareGlobalName_branch_ok[local]:
  well_typed_expr env (BareGlobalName ty id) ==>
  raw_exec_expr_ok tenv env (BareGlobalName ty id)
Proof
  rw[raw_exec_expr_ok_def] >>
  drule raw_exec_ready_env_type_defs >> strip_tac >> gvs[] >>
  drule_all raw_exec_eval_BareGlobalName_result_ok >>
  simp[]
QED

Theorem raw_exec_TopLevelName_branch_ok[local]:
  well_typed_expr env (TopLevelName ty sid_id) ==>
  raw_exec_expr_ok tenv env (TopLevelName ty sid_id)
Proof
  Cases_on `sid_id` >>
  rw[raw_exec_expr_ok_def] >>
  drule raw_exec_ready_env_type_defs >> strip_tac >> gvs[] >>
  drule_all raw_exec_eval_TopLevelName_result_ok >>
  simp[]
QED



Theorem raw_abi_eval_Literal_result_ok[local]:
  well_typed_expr env (Literal ty lit) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  eval_expr cx (Literal ty lit) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (Literal ty lit)) tv /\
                raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st` by
    gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rw[expr_type_def] >>
  gvs[well_typed_expr_def, well_formed_type_def, IS_SOME_EXISTS] >>
  drule_all raw_expr_value_ok_literal >> simp[]
QED

Theorem raw_abi_formal_Name_result_ok[local]:
  well_typed_expr env (Name ty id) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  eval_expr cx (Name ty id) st = (INL tv,st') ==>
  raw_expr_value_ok tenv ty tv /\ st' = st
Proof
  strip_tac >>
  `FLOOKUP env.var_types (string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv` by
    (gvs[well_typed_expr_def, raw_abi_formal_scope_ready_def,
         raw_abi_runtime_consistent_def, env_consistent_def,
         env_scopes_consistent_def, IS_SOME_EXISTS] >>
     metis_tac[]) >>
  drule_all raw_abi_formal_lookup_safe_cast_origin >>
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
     return_def, raw_expr_value_ok_def] >>
  disj2_tac >>
  qexists `raw` >> simp[]
QED
Theorem raw_abi_eval_Name_result_ok[local]:
  well_typed_expr env (Name ty id) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  eval_expr cx (Name ty id) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (Name ty id)) tv /\
                raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `FLOOKUP env.var_types (string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `?sv. lookup_scopes (string_to_num id) st.scopes = SOME sv` by
    (gvs[well_typed_expr_def, raw_abi_formal_scope_ready_def,
         raw_abi_runtime_consistent_def, env_consistent_def,
         env_scopes_consistent_def, IS_SOME_EXISTS] >>
     metis_tac[]) >>
  drule_all raw_abi_formal_lookup_safe_cast_origin >>
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  drule_all lookup_scopes_val_from_lookup_scopes >>
  rw[Once evaluate_def, bind_def, get_scopes_def, lift_option_type_def,
     return_def, vyperTypeExprSoundnessTheory.no_type_error_result_def,
     expr_type_def, raw_expr_value_ok_def] >>
  simp[] >>
  disj2_tac >> qexists `raw` >> simp[]
QED
Theorem raw_abi_BareGlobalName_lookup_ok[local]:
  well_typed_expr env (BareGlobalName ty id) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st ==>
  ?rt v.
    FLOOKUP (get_source_immutables (current_module cx)
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
      (string_to_num id) = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ty = SOME rt /\
    value_has_type rt v
Proof
  strip_tac >>
  `FLOOKUP env.bare_globals (env.current_src,string_to_num id) = SOME ty` by
    gvs[well_typed_expr_def] >>
  `env_consistent env cx st` by
    gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def] >>
  `env.current_src = current_module cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `IS_SOME (FLOOKUP (get_source_immutables (current_module cx)
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
     (string_to_num id))` by
    (gvs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum drule >> simp[]) >>
  pop_assum mp_tac >> simp[IS_SOME_EXISTS] >>
  strip_tac >> PairCases_on `x` >> gvs[] >>
  `evaluate_type (get_tenv cx) ty = SOME x0` by
    (gvs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum drule_all >> simp[]) >>
  `imms_well_typed
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])` by
    (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
     gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def]
     >- rw[imms_well_typed_def] >>
     rw[] >>
     gvs[EVERY_MEM, FORALL_PROD] >>
     first_x_assum irule >>
     imp_res_tac ALOOKUP_MEM >>
     goal_assum drule) >>
  drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >>
  rw[] >>
  qexistsl [`x0`, `x1`] >> simp[]
QED

Theorem raw_abi_eval_BareGlobalName_result_ok[local]:
  well_typed_expr env (BareGlobalName ty id) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  eval_expr cx (BareGlobalName ty id) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (BareGlobalName ty id)) tv /\
                raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  drule_all raw_abi_BareGlobalName_lookup_ok >>
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  rw[expr_type_def] >>
  gvs[] >>
  irule raw_expr_value_ok_typed >>
  qexists_tac `rt` >>
  simp[toplevel_value_typed_Value]
QED

Theorem raw_abi_read_storage_slot_result_ok[local]:
  evaluate_type tenv ty = SOME tv /\
  read_storage_slot cx is_transient slot tv st = (rr,st') ==>
    no_type_error_result rr /\
    case rr of
    | INL v => raw_expr_value_ok tenv ty (Value v) /\ st' = st
    | INR _ => T
Proof
  strip_tac >>
  Cases_on `rr` >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (conj_tac
      >- (irule raw_expr_value_ok_typed >>
          qexists `tv` >> simp[toplevel_value_typed_Value] >>
          drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
          strip_tac >>
          drule_all vyperTypeStatePreservationTheory.read_storage_slot_success_type >>
          simp[])
      >- metis_tac[vyperStatePreservationTheory.read_storage_slot_state]) >>
  drule vyperTypeExprSoundnessTheory.read_storage_slot_error >>
  strip_tac >> gvs[]
QED

Theorem raw_abi_eval_TopLevelName_storage_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  functions_well_typed cx /\
  FLOOKUP env.bare_globals (src,string_to_num id) = NONE /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_num (string_to_num id) ts = SOME (StorageVarDecl is_transient ty,id_str) /\
  lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tvl => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tvl /\
                 raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\ accounts_well_typed st.accounts` by
    gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def] >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  simp[] >>
  Cases_on `tv` >>
  gvs[return_def, bind_def, expr_type_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_abi_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_abi_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      irule raw_expr_value_ok_typed >>
      qexists `ArrayTV t b` >> simp[toplevel_value_typed_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_abi_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def])
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                       (INL v,s'') => (INL (Value v),s'')
                     | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
      BasicProvers.TOP_CASE_TAC >> gvs[] >>
      strip_tac >> gvs[] >>
      drule_all raw_abi_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `(case read_storage_slot _ _ _ _ _ of
                   (INL v,s'') => (INL (Value v),s'')
                 | (INR e,s'') => (INR e,s'')) = _` mp_tac >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  strip_tac >> gvs[] >>
  drule_all raw_abi_read_storage_slot_result_ok >> strip_tac >>
      Cases_on `q` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_abi_eval_TopLevelName_immutable_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  functions_well_typed cx /\
  FLOOKUP env.bare_globals (src,string_to_num id) = SOME ty /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tvl => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tvl /\
                 raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\ accounts_well_typed st.accounts` by
    gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  `?ts. get_module_code cx src = SOME ts /\
        FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty) /\
        is_bare_global_decl (string_to_num id) ts /\
        find_var_decl_by_num (string_to_num id) ts = NONE /\ ty <> NoneT` by
    (gvs[env_consistent_def] >>
     drule_all env_context_consistent_bare_global_find_NONE >> rw[]) >>
  `IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => []))
      (string_to_num id))` by
    (gvs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum drule >> simp[]) >>
  gvs[IS_SOME_EXISTS] >>
  PairCases_on `x` >>
  `evaluate_type (get_tenv cx) ty = SOME x0` by
    (gvs[env_consistent_def, env_immutables_consistent_def] >>
     first_x_assum drule_all >> simp[]) >>
  `imms_well_typed
     (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])` by
    (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
     gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def]
     >- rw[imms_well_typed_def] >>
     rw[] >>
     gvs[EVERY_MEM, FORALL_PROD] >>
     first_x_assum irule >>
     imp_res_tac ALOOKUP_MEM >>
     goal_assum drule) >>
  `value_has_type x0 x1` by
    (drule_all vyperTypeEnvTheory.imms_well_typed_get_source_immutables >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, Once lookup_global_def, bind_def, lift_option_type_def,
       get_immutables_def, get_address_immutables_def, lift_option_def,
       return_def, raise_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[get_source_immutables_def, return_def, raise_def] >>
  rw[expr_type_def] >>
  gvs[] >>
  irule raw_expr_value_ok_typed >>
  qexists `x0` >> simp[toplevel_value_typed_Value]
QED
Theorem safe_cast_list_length[local]:
  !rts raws acc out.
    safe_cast_list rts raws acc = SOME out ==>
    LENGTH out = LENGTH acc + LENGTH rts /\ LENGTH rts = LENGTH raws
Proof
  Induct >> Cases_on `raws` >>
  rw[Once vyperValueOperationTheory.safe_cast_def]
  >- simp[listTheory.LENGTH_REVERSE]
  >- (Cases_on `safe_cast h' h` >> gvs[] >> first_x_assum drule >> rw[])
  >- (Cases_on `safe_cast h' h` >> gvs[] >> first_x_assum drule >> rw[])
QED


Theorem bare_globals_agrees_toplevel_type[local]:
  env_consistent env cx st /\
  FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
  FLOOKUP env.bare_globals (src,id) = SOME ty' ==>
  ty' = ty
Proof
  rw[env_consistent_def] >>
  drule_all env_context_consistent_bare_global_find_NONE >> rw[] >> gvs[]
QED
Theorem raw_abi_eval_TopLevelName_result_ok[local]:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st /\
  functions_well_typed cx /\
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
    no_type_error_result res /\
    case res of
    | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type (TopLevelName ty (src,id))) tv /\
                raw_abi_formal_scope_ready (get_tenv cx) params vals scope env cx st'
    | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st` by
    gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def] >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)`
  >- (`?ts is_transient typ id_str.
         get_module_code cx src = SOME ts /\
         find_var_decl_by_num (string_to_num id) ts = SOME (StorageVarDecl is_transient typ,id_str) /\
         typ = ty /\
         IS_SOME (evaluate_type (get_tenv cx) typ) /\
         IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
        (gvs[env_consistent_def, env_context_consistent_def] >>
         first_x_assum drule_all >> rw[]) >>
      gvs[IS_SOME_EXISTS] >>
      drule_all raw_abi_eval_TopLevelName_storage_result_ok >> simp[]) >>
  drule_all bare_globals_agrees_toplevel_type >> strip_tac >> gvs[] >>
  drule_all raw_abi_eval_TopLevelName_immutable_result_ok >> simp[]
QED

Theorem safe_cast_idempotent[local]:
  (!rt raw v. safe_cast rt raw = SOME v ==> safe_cast rt v = SOME v) /\
  (!rts raws acc out.
     safe_cast_list rts raws acc = SOME out ==>
     ?suffix.
       out = REVERSE acc ++ suffix /\
       safe_cast_list rts suffix [] = SOME suffix /\
       !acc'. safe_cast_list rts suffix acc' = SOME (REVERSE acc' ++ suffix))
Proof
  ho_match_mp_tac vyperValueOperationTheory.safe_cast_ind >>
  rw[Once vyperValueOperationTheory.safe_cast_def]
  >- (Cases_on `rt` >> Cases_on `raw` >>
      gvs[Once vyperValueOperationTheory.safe_cast_def, AllCaseEqs()] >>
      simp[Once vyperValueOperationTheory.safe_cast_def, within_int_bound_def] >>
      qpat_assum `safe_cast_list _ _ [] = SOME _`
        (fn th => assume_tac (MATCH_MP safe_cast_list_length th)) >>
      rw[] >> gvs[MAP_ZIP] >> metis_tac[])
  >- (qexists `[]` >> gvs[vyperValueOperationTheory.safe_cast_def])
  >- (qpat_x_assum `safe_cast_list (rt::rts) (raw::raws) acc = SOME out` mp_tac >>
      once_rewrite_tac[vyperValueOperationTheory.safe_cast_def] >>
      Cases_on `safe_cast rt raw` >> gvs[] >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexists `x::suffix` >>
      simp[Once vyperValueOperationTheory.safe_cast_def, APPEND_ASSOC] >>
      rw[] >>
      first_x_assum (qspec_then `x::acc'` mp_tac) >>
      simp[Once vyperValueOperationTheory.safe_cast_def, APPEND_ASSOC])
  >- gvs[Once vyperValueOperationTheory.safe_cast_def]
QED

Theorem raw_expr_value_ok_Value_safe_cast[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  evaluate_type tenv ty = SOME rt ==>
  safe_cast rt v = SOME v
Proof
  rw[raw_expr_value_ok_def]
  >- (gvs[toplevel_value_typed_Value] >>
      drule vyperTypingTheory.safe_cast_well_typed >> simp[])
  >- (gvs[] >> drule (CONJUNCT1 safe_cast_idempotent) >> simp[])
QED

Theorem raw_expr_values_ok_safe_cast_list_acc[local]:
  raw_expr_values_ok tenv es vs /\
  LIST_REL (\e rt. evaluate_type tenv (expr_type e) = SOME rt) es rts ==>
  safe_cast_list rts vs acc = SOME (REVERSE acc ++ vs)
Proof
  qid_spec_tac `rts` >> qid_spec_tac `vs` >> qid_spec_tac `acc` >>
  Induct_on `es` >> rw[raw_expr_values_ok_def]
  >- simp[Once vyperValueOperationTheory.safe_cast_def] >>
  simp[Once vyperValueOperationTheory.safe_cast_def] >>
  drule_all raw_expr_value_ok_Value_safe_cast >> simp[] >>
  first_x_assum (qspecl_then [`v::acc`, `ys`, `ys'`] mp_tac) >>
  simp[raw_expr_values_ok_def, APPEND_ASSOC]
QED

Theorem raw_expr_values_ok_safe_cast_list[local]:
  raw_expr_values_ok tenv es vs /\
  LIST_REL (\e rt. evaluate_type tenv (expr_type e) = SOME rt) es rts ==>
  safe_cast_list rts vs [] = SOME vs
Proof
  rpt strip_tac >> drule_all raw_expr_values_ok_safe_cast_list_acc >> simp[]
QED

Theorem OPT_MMAP_evaluate_type_mono_raw[local]:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED

Theorem OPT_MMAP_evaluate_type_LIST_REL_raw[local]:
  OPT_MMAP (evaluate_type tenv) tys = SOME tvs ==>
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs
Proof
  qid_spec_tac `tvs` >> Induct_on `tys` >> rw[OPT_MMAP_def] >>
  Cases_on `evaluate_type tenv h` >> gvs[] >>
  Cases_on `OPT_MMAP (evaluate_type tenv) tys` >> gvs[]
QED

Theorem raw_expr_value_ok_StructLit[local]:
  well_typed_expr env (StructLit ty nsid kes) /\
  raw_expr_values_ok env.type_defs (MAP SND kes) vs ==>
  raw_expr_value_ok env.type_defs (expr_type (StructLit ty nsid kes))
    (Value (StructV (ZIP (MAP FST kes,vs))))
Proof
  rw[well_typed_expr_def, expr_type_def, raw_expr_value_ok_def] >>
  disj2_tac >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type _ _ = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[] >>
  qexists `StructV (ZIP (MAP FST kes,vs))` >>
  simp[Once vyperValueOperationTheory.safe_cast_def] >>
  gvs[raw_expr_values_ok_def] >>
  imp_res_tac LIST_REL_LENGTH >>
  `LENGTH tvs = LENGTH args` by
    (imp_res_tac vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  simp[MAP_ZIP] >>
  `LENGTH vs = LENGTH args` by
    (gvs[LENGTH_MAP] >> metis_tac[LENGTH_MAP]) >>
  conj_tac >- simp[MAP_ZIP] >>
  `MAP SND (ZIP (MAP FST args,vs)) = vs` by simp[MAP_ZIP] >>
  simp[] >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP SND args) = SOME tvs` by
    metis_tac[OPT_MMAP_evaluate_type_mono_raw] >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs` by
    gvs[] >>
  drule OPT_MMAP_evaluate_type_LIST_REL_raw >>
  strip_tac >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >>
  `raw_expr_values_ok env.type_defs (MAP SND kes) vs` by
    (rw[raw_expr_values_ok_def, LIST_REL_EL_EQN, EL_MAP]) >>
  `LIST_REL (\e rt. evaluate_type env.type_defs (expr_type e) = SOME rt)
     (MAP SND kes) tvs` by
    (rw[LIST_REL_EL_EQN, EL_MAP]) >>
  drule_all raw_expr_values_ok_safe_cast_list >>
  simp[]
QED

Theorem raw_exec_StructLit_eval_success[local]:
  (eval_exprs cx (MAP SND kes) st = (INL vs,st1)) ==>
  (eval_expr cx (StructLit ty nsid kes) st = (res,st')) ==>
  (res = INL (Value (StructV (ZIP (MAP FST kes,vs)))) /\ st' = st1)
Proof
  PairCases_on `nsid` >>
  ntac 2 strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  strip_tac >>
  qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
  asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM]
QED

Theorem raw_exec_StructLit_eval_error[local]:
  eval_exprs cx (MAP SND kes) st = (INR err,st1) ==>
  eval_expr cx (StructLit ty nsid kes) st = (res,st') ==>
  (res = INR err /\ st' = st1)
Proof
  PairCases_on `nsid` >>
  ntac 2 strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  strip_tac >>
  qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
  asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM]
QED

Theorem raw_exec_StructLit_branch_ok[local]:
  well_typed_expr env (StructLit ty nsid kes) /\
  raw_exec_named_exprs_ok tenv env kes ==>
  raw_exec_expr_ok tenv env (StructLit ty nsid kes)
Proof
  rpt strip_tac >>
  simp[raw_exec_expr_ok_def] >>
  strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, LET_THM] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,exprs_st)` >>
  qpat_x_assum `raw_exec_named_exprs_ok _ _ kes` mp_tac >>
  simp[raw_exec_named_exprs_ok_def, raw_exec_exprs_ok_def] >>
  disch_then (qspec_then `cx` (qspec_then `st` (qspec_then `exprs_res` (qspec_then `exprs_st` mp_tac)))) >>
  simp[] >> strip_tac >>
  Cases_on `exprs_res` >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
  >- (strip_tac >>
      drule_all raw_exec_StructLit_eval_success >> strip_tac >> gvs[] >>
      `raw_expr_value_ok env.type_defs (expr_type (StructLit ty nsid kes))
         (Value (StructV (ZIP (MAP FST kes,x))))` by
        (drule_all raw_expr_value_ok_StructLit >> simp[]) >>
      simp[vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  strip_tac >>
  drule_all raw_exec_StructLit_eval_error >> strip_tac >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_exec_place_expr_any_ok[local]:
  raw_exec_place_expr_ok tenv env e
Proof
  rw[raw_exec_place_expr_ok_def]
QED

Theorem raw_exec_place_target_any_ok[local]:
  raw_exec_place_target_ok tenv env tgt
Proof
  rw[raw_exec_place_target_ok_def]
QED


Theorem raw_exec_FlagMember_branch_ok[local]:
  well_typed_expr env (FlagMember ty nsid mid) ==>
  raw_exec_expr_ok tenv env (FlagMember ty nsid mid)
Proof
  simp[raw_exec_expr_ok_def] >> strip_tac >>
  rpt strip_tac >>
  imp_res_tac lookup_flag_mem_state >> gvs[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[] >>
  PairCases_on `nsid` >>
  gvs[raw_exec_ready_def, env_context_consistent_def, well_typed_expr_def] >>
  `?ts. get_module_code cx nsid0 = SOME ts /\
        lookup_flag nsid1 ts = SOME ls /\
        FLOOKUP (get_tenv cx) (type_key (nsid0,nsid1)) = SOME (FlagArgs (LENGTH ls))` by
    metis_tac[] >>
  gvs[] >>
  `LENGTH ls <= 256` by
    (gvs[well_formed_type_def, evaluate_type_def] >> decide_tac) >>
  qpat_x_assum `lookup_flag_mem _ _ _ _ = _` mp_tac >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  Cases_on `INDEX_OF mid ls` >> strip_tac >>
  gvs[return_def, vyperTypeExprSoundnessTheory.no_type_error_result_def,
      expr_type_def, raw_expr_value_ok_def, toplevel_value_typed_Value,
      evaluate_type_def, vyperTypingTheory.value_has_type_def,
      INDEX_OF_eq_NONE, INDEX_OF_eq_SOME] >>
  metis_tac[bitTheory.TWOEXP_MONO]
QED


Theorem raw_exec_expr_ok_result[local]:
  raw_exec_expr_ok (get_tenv cx) env e /\
  raw_exec_ready (get_tenv cx) env cx st /\
  functions_well_typed cx /\
  eval_expr cx e st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL tv => raw_expr_value_ok (get_tenv cx) (expr_type e) tv /\
              raw_exec_ready (get_tenv cx) env cx st'
  | INR _ => T
Proof
  strip_tac >>
  drule raw_exec_ready_type_defs >> strip_tac >> gvs[raw_exec_expr_ok_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem raw_exec_exprs_ok_result[local]:
  raw_exec_exprs_ok (get_tenv cx) env es /\
  raw_exec_ready (get_tenv cx) env cx st /\
  functions_well_typed cx /\
  eval_exprs cx es st = (res,st') ==>
  no_type_error_result res /\
  case res of
  | INL vs => raw_expr_values_ok (get_tenv cx) es vs /\
              raw_exec_ready (get_tenv cx) env cx st'
  | INR _ => T
Proof
  strip_tac >>
  drule raw_exec_ready_type_defs >> strip_tac >> gvs[raw_exec_exprs_ok_def] >>
  first_x_assum drule_all >> simp[]
QED


(* The previous blanket mutual theorem
   `well_typed_expr env e ==> raw_exec_expr_ok env.type_defs env e`
   is intentionally not stated here: arbitrary well-typed StructLit fields may
   have type NoneT, while expression-list materialisation requires explicit
   non-None side conditions.  Downstream generated-getter code uses the
   getter-scoped raw execution exports below instead. *)

Theorem lift_safe_cast_success_no_type_error[local]:
  safe_cast rt v = SOME v' /\
  lift_option_type (safe_cast rt v) msg st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >>
  gvs[lift_option_type_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED


Theorem raw_expr_value_ok_Value_return_safe_cast_no_type_error[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  evaluate_type tenv ty = SOME rt /\
  lift_option_type (safe_cast rt v) msg st = (res,st') ==>
  no_type_error_result res
Proof
  rw[raw_expr_value_ok_def]
  >- (gvs[toplevel_value_typed_Value] >>
      drule vyperTypingTheory.safe_cast_well_typed >> strip_tac >>
      metis_tac[lift_safe_cast_success_no_type_error])
  >- (drule (CONJUNCT1 safe_cast_idempotent) >> strip_tac >>
      gvs[] >>
      metis_tac[lift_safe_cast_success_no_type_error])
QED
Theorem raw_expr_value_ok_Value_materialise_no_type_error[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  materialise cx (Value v) st = (res,st') ==>
  no_type_error_result res
Proof
  rw[materialise_def, return_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem raw_expr_value_ok_Value_materialise_result_ok[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  materialise cx (Value v) st = (res,st') ==>
  no_type_error_result res /\
  (case res of
   | INL mv => st' = st /\ raw_abi_formal_scope_ready tenv params vals scope env cx st'
   | INR _ => T)
Proof
  rw[materialise_def, return_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[]
QED

Theorem raw_expr_value_ok_Value_materialise_success_ready[local]:
  raw_expr_value_ok tenv ty (Value v) /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  materialise cx (Value v) st = (INL mv,st') ==>
  st' = st /\ raw_abi_formal_scope_ready tenv params vals scope env cx st'
Proof
  rpt strip_tac >> gvs[materialise_def, return_def]
QED


Theorem checked_explicit_external_raw_abi_runtime_consistent[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  machine_well_typed am /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am.immutables /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  accounts_well_typed st.accounts ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    raw_abi_runtime_consistent
      (type_env_all_modules mods) args vals scope env_body cx st
Proof
  strip_tac >>
  drule_all checked_explicit_external_raw_bind_env_package >>
  gvs[] >> strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  gvs[raw_abi_runtime_consistent_def, env_consistent_def, machine_well_typed_def] >>
  metis_tac[bind_arguments_scope_abi_casts, bind_arguments_length_c53]
QED



Theorem eval_expr_type_sound_from_mutual[local]:
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_expr cx e st = (res,st') /\ well_typed_expr env e ==>
  state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  case res of
  | INL tv => expr_result_typed env e tv
  | INR _ => T
Proof
  metis_tac[cj 8 eval_all_type_sound_mutual]
QED

Theorem eval_exprs_type_sound_from_mutual[local]:
  well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_exprs cx es st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  case res of
  | INL vs => exprs_runtime_typed env es vs
  | INR _ => T
Proof
  metis_tac[cj 9 eval_all_type_sound_mutual]
QED

Theorem raw_abi_eval_expr_generic_result_ok[local]:
  well_typed_expr env e /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  state_well_typed st /\ functions_well_typed cx /\
  eval_expr cx e st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  case res of
  | INL tv => raw_expr_value_ok env.type_defs (expr_type e) tv
  | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\
   accounts_well_typed st.accounts` by
    metis_tac[raw_abi_formal_scope_ready_soundness_preconditions_weak] >>
  drule_all eval_expr_type_sound_from_mutual >>
  strip_tac >> simp[] >>
  Cases_on `res` >> gvs[] >>
  metis_tac[expr_result_typed_raw_expr_value_ok]
QED

Theorem raw_abi_eval_exprs_generic_result_ok[local]:
  well_typed_exprs env es /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  state_well_typed st /\ functions_well_typed cx /\
  eval_exprs cx es st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
  no_type_error_result res /\
  case res of
  | INL vs => raw_expr_values_ok env.type_defs es vs
  | INR _ => T
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\
   accounts_well_typed st.accounts` by
    metis_tac[raw_abi_formal_scope_ready_soundness_preconditions_weak] >>
  drule_all eval_exprs_type_sound_from_mutual >>
  strip_tac >> simp[] >>
  Cases_on `res` >> gvs[] >>
  metis_tac[exprs_runtime_typed_raw_expr_values_ok]
QED

Theorem checked_explicit_raw_body_no_type_error[local]:
  type_stmts env ret body = SOME env_after /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st /\
  state_well_typed st /\ functions_well_typed cx /\
  eval_stmts cx body st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >>
  `env_consistent env cx st /\ context_well_typed cx /\
   accounts_well_typed st.accounts` by
    metis_tac[raw_abi_formal_scope_ready_soundness_preconditions_weak] >>
  drule_all eval_stmts_no_type_error >>
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED


Theorem lookup_exported_function_current_lookup_function[local]:
  find_function_module am tx.target tx.function_name = src /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx src) am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  lookup_function src tx.function_name External ts = SOME (mut,nr,args,dflts,ret,body)
Proof
  rw[lookup_exported_function_def, find_function_module_def, get_self_code_def,
     initial_evaluation_context_def, get_module_code_def] >>
  gvs[AllCaseEqs()]
QED

Theorem lookup_exported_function_checked_cases_current[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx src) am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw.
     MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
  (?decl.
     MEM decl ts /\
     is_public_getter_decl tx.function_name decl /\
     external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  metis_tac[lookup_exported_function_checked_cases_selected]
QED


Theorem send_call_value_preserves_scopes[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem call_lock_action_preserves_scopes[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready[local]:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem acquire_nonreentrant_lock_accounts[local]:
  acquire_nonreentrant_lock target slot ro st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_send_prefix_raw_formals_ready[local]:
  machine_well_typed am /\
  raw_abi_formal_scope_ready tenv params vals scope env cx (initial_state am [scope]) /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (RuntimeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [scope]) = (INL (),st)) ==>
  st.scopes = [scope] /\
  st.immutables = am.immutables /\
  accounts_well_typed st.accounts /\
  raw_abi_formal_scope_ready tenv params vals scope env cx st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac call_lock_action_preserves_scopes >>
  imp_res_tac call_lock_action_preserves_immutables >>
  imp_res_tac call_lock_action_preserves_accounts_c53 >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac acquire_nonreentrant_lock_accounts >>
  imp_res_tac send_call_value_preserves_scopes >>
  imp_res_tac send_call_value_preserves_immutables >>
  imp_res_tac send_call_value_accounts_well_typed_c53 >>
  gvs[raw_abi_formal_scope_ready_def, raw_abi_runtime_consistent_def,
      env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def, initial_state_def] >>
  metis_tac[]
QED




Theorem checked_call_external_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external am tx = (res,am') ==>
  no_type_error_result res
Proof
  cheat
QED





Theorem safe_cast_unsorted_sarray_c26[local]:
  safe_cast (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)])) =
  SOME (ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)]))
Proof
  `safe_cast_list (REPLICATE 2 (BaseTV (UintT 256))) [IntV 1; IntV 2] [] =
     SOME [IntV 1; IntV 2]` by
    (irule vyperTypingTheory.safe_cast_list_identity_nil >>
     conj_tac >- metis_tac[vyperTypingTheory.safe_cast_well_typed] >>
     EVAL_TAC >> intLib.ARITH_TAC) >>
  simp[Once vyperValueOperationTheory.safe_cast_def, within_int_bound_def,
       listTheory.ZIP]
QED

Theorem not_value_has_type_unsorted_sarray_c26[local]:
  ~value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 3))
    (ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)]))
Proof
  simp[vyperTypingTheory.value_has_type_def, sortingTheory.SORTED_DEF]
QED

Theorem bind_arguments_success_not_scope_well_typed_c26_counterexample[local]:
  ?scope.
    bind_arguments FEMPTY
      [("x", ArrayT (BaseT (UintT 256)) (Fixed 3))]
      [ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)])] = SOME scope /\
    ~scope_well_typed scope
Proof
  qexists_tac `FEMPTY |+ (string_to_num "x",
    <| assignable := T; type := ArrayTV (BaseTV (UintT 256)) (Fixed 3);
       value := ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)]) |>)` >>
  conj_tac
  >- simp[Once bind_arguments_def, Once bind_arguments_def, evaluate_type_def,
          type_slot_size_def, safe_cast_unsorted_sarray_c26] >>
  rw[scope_well_typed_def, FLOOKUP_UPDATE] >>
  simp[not_value_has_type_unsorted_sarray_c26]
QED

Theorem checked_raw_arg_unsorted_sarray_subscript_no_TypeError_probe[local]:
  let mods =
    ([(NONE : num option,
       [FunctionDecl External Nonpayable F F "f"
         [("x", ArrayT (BaseT (UintT 256)) (Fixed 3))]
         [] (BaseT (UintT 256))
         [Return (SOME (Subscript (BaseT (UintT 256))
           (Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "x")
           (Literal (BaseT (UintT 256)) (IntL 0))))]])] :
      (num option # toplevel list) list) in
  let srcs =
    ([((0w:address), mods)] :
       (address # (num option # toplevel list) list) list) in
  let am = initial_machine_state with sources := srcs in
  let tx = empty_call_txn with <|
    function_name := "f";
    args := [ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)])]
  |> in
    FST (call_external am tx) = INL (IntV 2)
Proof
  EVAL_TAC
QED

Theorem checked_raw_arg_unsorted_sarray_return_array_no_TypeError_probe[local]:
  let mods =
    ([(NONE : num option,
       [FunctionDecl External Nonpayable F F "f"
         [("x", ArrayT (BaseT (UintT 256)) (Fixed 3))]
         [] (ArrayT (BaseT (UintT 256)) (Fixed 3))
         [Return (SOME (Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "x"))]])] :
      (num option # toplevel list) list) in
  let srcs =
    ([((0w:address), mods)] :
       (address # (num option # toplevel list) list) list) in
  let am = initial_machine_state with sources := srcs in
  let tx = empty_call_txn with <|
    function_name := "f";
    args := [ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)])]
  |> in
    FST (call_external am tx) =
      INL (ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)]))
Proof
  EVAL_TAC
QED

Theorem checked_raw_arg_unsorted_sarray_assign_subscript_no_TypeError_probe[local]:
  let mods =
    ([(NONE : num option,
       [FunctionDecl External Nonpayable F F "f"
         [("x", ArrayT (BaseT (UintT 256)) (Fixed 3))]
         [] (BaseT (UintT 256))
         [Assign
            (BaseTarget
              (SubscriptTarget (NameTarget "x")
                (Literal (BaseT (UintT 256)) (IntL 1))))
            (Literal (BaseT (UintT 256)) (IntL 7));
          Return (SOME (Subscript (BaseT (UintT 256))
            (Name (ArrayT (BaseT (UintT 256)) (Fixed 3)) "x")
            (Literal (BaseT (UintT 256)) (IntL 1))))]])] :
      (num option # toplevel list) list) in
  let srcs =
    ([((0w:address), mods)] :
       (address # (num option # toplevel list) list) list) in
  let am = initial_machine_state with sources := srcs in
  let tx = empty_call_txn with <|
    function_name := "f";
    args := [ArrayV (SArrayV [(2, IntV 1); (0, IntV 2)])]
  |> in
    FST (call_external am tx) = INL (IntV 7)
Proof
  EVAL_TAC
QED


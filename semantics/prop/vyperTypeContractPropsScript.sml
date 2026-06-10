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
  list rich_list arithmetic finite_map alist option pair
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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

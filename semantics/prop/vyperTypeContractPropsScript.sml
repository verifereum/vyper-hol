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

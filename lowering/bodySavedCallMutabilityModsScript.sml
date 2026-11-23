(* Relate the no-snapshot mutation test to the selected source declaration. *)
Theory bodySavedCallMutabilityMods
Ancestors
  bodyIntCallSource bodyInvCodeProps bodyInvSplit bodyCallSupport
  compileUnit compileEnv exprLowering linkedNsidProps vyperTypeContractContext
  vyperTypeContract alist list pair

Triviality mutability_src_absent:
  !tops src key rest_map.
    (!vis mut nr raw name args dflts ret ss.
       MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
       vis <> External ==> key <> nsid_to_string (src,name)) ==>
    build_func_mutability_src src tops rest_map key = rest_map key
Proof
  Induct >> simp[build_func_mutability_src_def] >> Cases >>
  simp[build_func_mutability_src_def, DISJ_IMP_THM, FORALL_AND_THM,
       RIGHT_AND_OVER_OR] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >>
  Cases_on `f = External` >> gvs[]
QED

Triviality mutability_src_decl:
  !tops src rest_map vis mut nr raw name args dflts ret ss.
    ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops)) /\
    MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
    vis <> External ==>
    build_func_mutability_src src tops rest_map (nsid_to_string (src,name)) = mut
Proof
  Induct >> simp[] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2
    (DISJ_CASES_THEN assume_tac) assume_tac)) >> gvs[build_func_mutability_src_def] >>
  Cases_on `h` >>
  gvs[build_func_mutability_src_def, self_member_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  first_x_assum drule_all >> strip_tac >> simp[] >>
  rpt (COND_CASES_TAC >> gvs[]) >>
  `name = s` by (Cases_on `src` >> fs[nsid_to_string_def, APPEND_11]) >>
  `F` suffices_by simp[] >>
  qpat_x_assum `~MEM _ (FLAT _)` mp_tac >> simp[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,s)]` >> simp[] >>
  qexists `FunctionDecl vis mut nr raw name args dflts ret ss` >>
  simp[self_member_keys_toplevel_def]
QED

Triviality mutability_mods_decl:
  !mods src tops vis mut nr raw name args dflts ret ss.
    ALL_DISTINCT (MAP FST mods) /\
    ALL_DISTINCT (contract_keys self_member_keys_toplevel mods) /\
    (!s ts v m n r f a d t b.
       MEM (s,ts) mods /\ MEM (FunctionDecl v m n r f a d t b) ts ==>
       ~MEM #"." f) /\
    MEM (src,tops) mods /\
    MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops /\
    vis <> External ==>
    build_func_mutability_mods mods (nsid_to_string (src,name)) = mut
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[build_func_mutability_mods_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (irule mutability_src_decl >> simp[] >> metis_tac[]) >>
  `build_func_mutability_mods mods (nsid_to_string (src,name)) = mut` by
    (first_x_assum irule >> simp[contract_keys_def] >> metis_tac[]) >>
  `build_func_mutability_src h0 h1 (build_func_mutability_mods mods)
       (nsid_to_string (src,name)) = build_func_mutability_mods mods (nsid_to_string (src,name))`
    suffices_by simp[] >>
  irule mutability_src_absent >> rpt strip_tac >>
  `(src,name) = (h0,name')` by
    (irule nsid_to_string_dot_free_injective >> simp[] >> metis_tac[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem saved_selected_call_mutability_mods:
  contract_inv mods exps ctx cenv cx /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  source_body_call_supported cx (src,name) /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  ~call_can_mutate cenv (IntCall (src,name)) ==>
  mut = View \/ mut = Pure
Proof
  strip_tac >>
  `?vis raw. vis <> External /\ MEM (FunctionDecl vis mut nr raw name args dflts ret ss) tops` by
    (Cases_on `src` >> gvs[source_body_call_supported_def]
     >- (fs[supported_linked_callee_def] >>
         drule_all_then strip_assume_tac supported_internal_callable >>
         qexistsl [`Internal`,`rr`] >> simp[]) >>
     qexistsl [`vis`,`raw`] >> Cases_on `vis` >> fs[include_fn_sig_def]) >>
  `MEM (src,tops) mods` by
    (drule_then (qspec_then `src` assume_tac) contract_inv_module_codes >>
     metis_tac[ALOOKUP_MEM]) >>
  drule check_contract_namespaces_ok >> strip_tac >>
  `ALL_DISTINCT (MAP FST mods) /\ ALL_DISTINCT (contract_keys self_member_keys_toplevel mods) /\
   !s ts v m n r f a d t b. MEM (s,ts) mods /\ MEM (FunctionDecl v m n r f a d t b) ts ==>
     ~MEM #"." f` by
    (gvs[contract_namespaces_ok_def, EVERY_MEM, FORALL_PROD] >>
     rpt strip_tac >>
     qpat_assum `!p q. MEM (p,q) mods ==> !tl. _` (drule_then drule) >> simp[]) >>
  drule_all mutability_mods_decl >> strip_tac >>
  `cenv.ce_func_mutability = build_func_mutability_mods mods` by
    fs[contract_inv_def, cenv_module_pins_mods_def] >>
  Cases_on `mut` >> gvs[call_can_mutate_def]
QED

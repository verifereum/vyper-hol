(* Match the linked custom-error descriptor with its compiler metadata. *)
Theory bodyCustomErrorCompilerPinsMods
Ancestors
  bodyFullPredsMods bodyInvMetadataProps bodyInvSplit bodySim
  allocLimits compileUnit compileEnv exprLowering linkedNsidProps
  vyperTypeContractContext vyperTypeContract vyperContext vyperEvent
  vyperAST vyperABI selectorDispatch arithmetic words list pair alist

Triviality custom_error_lookup_member:
  !tops name params. lookup_custom_error_args_in name tops = SOME params ==>
    MEM (ErrorDecl name params) tops
Proof
  Induct >> simp[lookup_custom_error_args_in_def] >> Cases >>
  simp[lookup_custom_error_args_in_def] >> rw[]
QED

Triviality custom_error_nsid_eq:
  ~MEM #"." name /\ ~MEM #"." err ==>
  (nsid_to_string (src,err) = nsid_to_string (owner,name) <=>
    src = owner /\ err = name)
Proof
  strip_tac >> eq_tac >> simp[] >> strip_tac >>
  `(src,err) = (owner,name)` by
    (irule nsid_to_string_dot_free_injective >> simp[]) >>
  gvs[]
QED

Triviality custom_error_lookup_src:
  !tops src owner name.
    ~MEM #"." name /\ (!err params. MEM (ErrorDecl err params) tops ==> ~MEM #"." err) ==>
    lookup_custom_error_args_src src (nsid_to_string (owner,name)) tops =
      if src = owner then lookup_custom_error_args_in name tops else NONE
Proof
  Induct >> simp[lookup_custom_error_args_src_def, lookup_custom_error_args_in_def] >>
  Cases >> rpt gen_tac >> strip_tac >>
  fs[lookup_custom_error_args_src_def, lookup_custom_error_args_in_def,
     DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_assum `!src owner name. _` (qspecl_then [`src`,`owner`,`name`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn th => simp[th, custom_error_nsid_eq]) >>
  Cases_on `src = owner` >> simp[]
QED

Triviality custom_error_lookup_mods:
  !mods owner name tops params.
    (!src ts err qs. MEM (src,ts) mods /\ MEM (ErrorDecl err qs) ts ==> ~MEM #"." err) /\
    ~MEM #"." name /\ ALOOKUP mods owner = SOME tops /\
    lookup_custom_error_args_in name tops = SOME params ==>
    lookup_custom_error_args_mods mods (nsid_to_string (owner,name)) = SOME params
Proof
  Induct >> simp[lookup_custom_error_args_mods_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `!err qs. MEM (ErrorDecl err qs) h1 ==> ~MEM #"." err` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!src ts err qs. (_ \/ _) /\ _ ==> _`
       (qspecl_then [`h0`,`h1`,`err`,`qs`] mp_tac) >> simp[]) >>
  `lookup_custom_error_args_src h0 (nsid_to_string (owner,name)) h1 =
     (if h0 = owner then lookup_custom_error_args_in name h1 else NONE)` by
    (irule custom_error_lookup_src >> conj_tac >> first_assum ACCEPT_TAC) >>
  simp[lookup_custom_error_args_mods_def] >>
  Cases_on `h0 = owner` >> gvs[ALOOKUP_def] >>
  qpat_assum `!owner name tops params. _` irule >>
  (conj_tac >- metis_tac[]) >> simp[] >> qexists_tac `tops` >> simp[]
QED

Triviality custom_error_table_lookup:
  contract_namespaces_ok deploy mods /\ ALOOKUP mods owner = SOME tops /\
  lookup_custom_error_args_in name tops = SOME params ==>
  lookup_custom_error_args_mods mods (nsid_to_string (owner,name)) = SOME params
Proof
  strip_tac >>
  `!src ts err qs. MEM (src,ts) mods /\ MEM (ErrorDecl err qs) ts ==> ~MEM #"." err` by
    (gvs[contract_namespaces_ok_def, EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     qpat_assum `!p q. MEM (p,q) mods ==> !tl. _` (drule_then drule) >> simp[]) >>
  `~MEM #"." name` by metis_tac[ALOOKUP_MEM, custom_error_lookup_member] >>
  irule custom_error_lookup_mods >> simp[] >> goal_assum drule >> simp[]
QED

Theorem custom_error_compiler_pins_mods:
  contract_inv mods exps ctx cenv cx /\
  body_const_cells_agree_mods mods cx env es /\
  stmt_exprs_ok cenv (Raise (RaiseCustomError (CustomError id pos kw))) /\
  ALOOKUP mods (FST id) = SOME error_tops /\
  lookup_custom_error_args_in (SND id) error_tops = SOME params /\
  args = custom_error_exprs (CustomError id pos kw) ==>
  cenv.ce_error_info (nsid_to_string id) = SOME params /\
  n2w (cenv.ce_method_id (SND id) (MAP SND params)) =
    calldata_method_id (function_selector (SND id)
      (vyper_to_abi_types (get_tenv cx) (MAP SND params))) /\
  (let n = abi_size_bound cenv.ce_struct_fields
                 (TupleT (MAP (lowered_value_type cenv) args)) + 32 in
     32 <= n /\ n < dimword (:256))
Proof
  PairCases_on `id` >> strip_tac >> gvs[] >>
  `contract_namespaces_ok cx.in_deploy mods` by
    (qpat_x_assum `body_const_cells_agree_mods _ _ _ _` mp_tac >>
     simp[body_const_cells_agree_mods_def] >>
     rpt strip_tac >> drule check_contract_namespaces_ok >> simp[]) >>
  drule_all_then assume_tac custom_error_table_lookup >>
  drule_then assume_tac contract_inv_type_env >>
  `cenv_module_pins_mods mods cenv` by fs[contract_inv_def] >>
  `cenv.ce_error_info (nsid_to_string (id0,id1)) = SOME params` by
    fs[cenv_module_pins_mods_def] >>
  `custom_error_alloc_ok cenv (CustomError (id0,id1) pos kw)` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  simp[] >>
  conj_tac
  >- fs[cenv_module_pins_mods_def] >>
  qpat_x_assum `custom_error_alloc_ok _ _` mp_tac >>
  simp[custom_error_alloc_ok_def, dimword_def] >> decide_tac
QED

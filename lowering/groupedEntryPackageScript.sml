(* Source parameters and selectors of grouped external entries. *)
Theory groupedEntryPackage
Ancestors
  compileVyper moduleLowering compileEnv selectorCompilerProps vyperABIEntries
  loweringShapeProps vyperTypeContractContext vyperTypeContract vyperTypeBindArguments
  publicGetterProps constSubst
  calldataSelectorProps entryDispatchProps mem2varBlockSimHelpers
  checkedSelectorTableProps dispatchedValueSelection constSubstCorrect defaultDispatchFacts
  list rich_list pair words arithmetic
Libs fcpLib

Theorem grouped_package_keyword_widths:
  fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,stmts) /\
  LENGTH dflts <= LENGTH args /\
  package_external_group tops target trans keys
    (mut,nr,rr,name,args,dflts,ret,stmts) =
      ExternalDefaults common entries specs off ==>
  EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs
Proof
  Cases_on `dflts = []` >> simp[package_external_group_def, NULL_EQ] >>
  simp[package_external_fn_def, set_external_package_target_def, LET_THM] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
    fn_allocs_ok_def, build_compile_env_ce_struct_fields, LET_THM] >>
  rpt strip_tac >> gvs[] >>
  (qmatch_asmsub_abbrev_tac `EVERY P args` >>
   qmatch_goalsub_abbrev_tac `type_memory_bytes cenv` >>
   qmatch_asmsub_abbrev_tac `alloc_limits_exprs size_env dflts` >>
   `type_memory_bytes cenv = type_memory_bytes size_env` by
     (irule type_memory_bytes_frame >>
      simp[Abbr `cenv`, Abbr `size_env`, build_compile_env_ce_struct_fields]) >>
   asm_rewrite_tac[] >>
   qpat_assum `EVERY P args` mp_tac >>
   simp[Abbr `P`, EVERY_MEM, MEM_MAP, MEM_ZIP, LENGTH_DROP, EL_DROP,
        pairTheory.EXISTS_PROD, pairTheory.FORALL_PROD] >>
   rpt strip_tac >> gvs[] >>
   irule arithmeticTheory.LESS_TRANS >>
   qexists_tac `2 ** 64` >>
   conj_tac
   >- (qpat_assum `EVERY _ args`
         (mp_tac o Q.SPEC
           `LENGTH (args : (string # type) list) - LENGTH (dflts : expr list)`
         o MATCH_MP EVERY_DROP) >>
       simp[EVERY_MEM, pairTheory.FORALL_PROD] >>
       disch_then irule >> qexists_tac `p_1` >>
       qpat_assum `(_,_) = EL n _` (fn th => REWRITE_TAC [th]) >>
       irule EL_MEM >> simp[LENGTH_DROP]) >>
   simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``])
QED

Theorem packaged_grouped_selector_width:
  EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors
    (MAP (package_external_group tops target trans keys) exts))
Proof
  `(\(sel,_,_). sel < dimword (:256)) =
    (\p : num # string # bool. FST p < dimword (:256))` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  `!tenv name tys. abi_method_id tenv name tys < dimword (:256)` by
    simp[abi_method_id_def, GSYM calldata_method_id_four_bytes, wordsTheory.w2n_lt] >>
  pure_rewrite_tac[grouped_selectors_def, EVERY_FLAT, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM] >> qx_gen_tac `ext` >> strip_tac >>
  PairCases_on `ext` >>
  qpat_assum `(\(sel,_,_). _) = _` SUBST1_TAC >>
  simp[pairTheory.FORALL_PROD] >> qx_genl_tac [`sel`,`lbl`,`tz`] >> strip_tac >>
  `MEM sel (MAP FST (external_group_selectors
    (package_external_group tops target trans keys (ext0,ext1,ext2,ext3,ext4,ext5,ext6,ext7))))` by
    (simp[MEM_MAP] >> qexists_tac `(sel,lbl,tz)` >> simp[]) >>
  pop_assum mp_tac >> pure_rewrite_tac[external_group_method_ids] >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  metis_tac[]
QED

Theorem find_distinct_selector[local]:
  !es key e P. ALL_DISTINCT (MAP key es) /\ MEM e es /\
    (!x. MEM x es ==> (P x <=> key x = key e)) ==>
    FIND P es = SOME e
Proof
  Induct >> simp[FIND_thm] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `h = e` >> gvs[] >>
  `key h <> key e` by (fs[MEM_MAP] >> metis_tac[]) >>
  `~P h` by metis_tac[] >> simp[] >> metis_tac[]
QED

Theorem grouped_selector_misses:
  EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors groups) /\
  ~MEM (w2n (m:bytes32)) (MAP FST (grouped_selectors groups)) ==>
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => m <> n2w sel
  | ExternalDefaults _ entries _ _ =>
      FIND (\(sel,_,_,_). m = n2w sel) entries = NONE) groups
Proof
  strip_tac >>
  `!g sel lbl tz. MEM g groups /\ MEM (sel,lbl,tz) (external_group_selectors g) ==>
    m <> n2w sel` by
    (qx_genl_tac [`g`,`sel`,`lbl`,`tz`] >> strip_tac >>
     `MEM (sel,lbl,tz) (grouped_selectors groups)` by
       (simp[grouped_selectors_def, MEM_FLAT, MEM_MAP] >>
        qexists_tac `external_group_selectors g` >> simp[] >>
        qexists_tac `g` >> simp[]) >>
     `sel < dimword (:256)` by
       (qpat_assum `EVERY _ (grouped_selectors groups)`
         (mp_tac o Q.SPEC `(sel,lbl,tz)` o REWRITE_RULE [EVERY_MEM]) >>
        simp[]) >>
     strip_tac >> gvs[wordsTheory.w2n_n2w] >>
     qpat_x_assum `~MEM sel _` mp_tac >> simp[MEM_MAP] >>
     qexists_tac `(sel,lbl,tz)` >> simp[]) >>
  simp[EVERY_MEM] >> Cases
  >- (rename1 `ExternalSingle selector package` >>
      PairCases_on `selector` >> strip_tac >>
      qpat_assum `!g sel lbl tz. _`
        (qspecl_then [`ExternalSingle (selector0,selector1,selector2) package`,
          `selector0`,`selector1`,`selector2`] mp_tac) >>
      simp[external_group_selectors_def]) >>
  simp[FIND_NONE_EVERY, combinTheory.o_DEF, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  rename1 `MEM (sel,lb,sz,nkw) entries` >>
  rename1 `MEM (ExternalDefaults common entries specs off) groups` >>
  qpat_assum `!g sel lbl tz. _`
    (qspecl_then [`ExternalDefaults common entries specs off`,`sel`,`lb`,
      `sel MOD 256 = 0`] mp_tac) >>
  simp[external_group_selectors_def, MEM_MAP] >>
  qexists_tac `(sel,lb,sz,nkw)` >> simp[]
QED

Theorem grouped_default_selector_route:
  ALL_DISTINCT (MAP FST (grouped_selectors
    (pre ++ ExternalDefaults common entries specs off::post))) /\
  EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors
    (pre ++ ExternalDefaults common entries specs off::post)) /\
  MEM (w2n (m:bytes32),lbl,mincd,k) entries ==>
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => m <> n2w sel
  | ExternalDefaults _ es _ _ => FIND (\(sel,_,_,_). m = n2w sel) es = NONE) pre /\
  FIND (\(sel,_,_,_). m = n2w sel) entries = SOME (w2n m,lbl,mincd,k)
Proof
  strip_tac >>
  `(\x. FST ((\(sel,lbl,_,_). (sel,lbl,sel MOD 256 = 0)) x)) =
    (FST : num # string # num # num -> num)` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  fs[grouped_selectors_def, external_group_selectors_def, MAP_APPEND,
    FLAT_APPEND, MAP_MAP_o, combinTheory.o_DEF, ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  `MEM (w2n m) (MAP FST entries)` by
    (simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  `~MEM (w2n m) (MAP FST (FLAT (MAP external_group_selectors pre)))` by
    metis_tac[] >>
  conj_tac
  >- (irule grouped_selector_misses >> simp[grouped_selectors_def]) >>
  MATCH_MP_TAC (Q.SPECL [`entries`,`FST : num # string # num # num -> num`,
    `(w2n m,lbl,mincd,k)`,`\(sel,_,_,_). (m:bytes32) = n2w sel`]
    (INST_TYPE [alpha |-> ``:num # string # num # num``, beta |-> ``:num``]
      find_distinct_selector)) >>
  asm_rewrite_tac[] >>
  simp[pairTheory.FORALL_PROD] >>
  qx_genl_tac [`sel`,`matched_lbl`,`matched_size`,`nkw`] >> strip_tac >>
  `sel < dimword (:256)` by
    (qpat_assum `EVERY _ (MAP _ entries)`
      (mp_tac o Q.SPEC `(sel,matched_lbl,matched_size,nkw)` o
        REWRITE_RULE [EVERY_MAP, combinTheory.o_DEF, EVERY_MEM]) >>
     simp[]) >>
  eq_tac >> simp[] >>
  disch_then (mp_tac o AP_TERM ``w2n : bytes32 -> num``) >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem checked_grouped_defaults_length:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (mut,nr,rr,name,args,dflts,ret,stmts) (FST (classify_functions tops)) ==>
  LENGTH dflts <= LENGTH args
Proof
  strip_tac >> drule classify_functions_external_source >>
  disch_then (qx_choosel_then [`raw_defaults`,`raw_stmts`] strip_assume_tac) >>
  fs[subst_consts_fn_def]
  >- (drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
      drule check_contract_runtime_function_body_MEM >> simp[] >>
      disch_then (qspecl_then [`External`,`ret`,`rr`,`nr`,`mut`,`name`,
        `raw_defaults`,`raw_stmts`,`args`] mp_tac) >>
      simp[check_function_body_def, LET_THM] >>
      metis_tac[intcall_defaults_map_param_types_length_le]) >>
  imp_res_tac public_getter_defaults >> gvs[]
QED

Theorem checked_grouped_package_keyword_widths:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\group. case group of
    ExternalSingle _ _ => T
  | ExternalDefaults common entries specs off =>
      EVERY (\(_,ty,_). type_memory_bytes common.ec_env ty < dimword (:256)) specs)
    (MAP (package_external_group tops target trans keys) exts)
Proof
  rpt strip_tac >> simp[EVERY_MAP, EVERY_MEM] >> qx_gen_tac `ext` >> strip_tac >>
  PairCases_on `ext` >>
  rename1 `MEM (mut,nr,rr,name,args,dflts,ret,stmts) exts` >>
  Cases_on `package_external_group tops target trans keys
    (mut,nr,rr,name,args,dflts,ret,stmts)` >> simp[] >>
  `fn_allocs_ok tops (mut,nr,rr,name,args,dflts,ret,stmts)` by
    metis_tac[lower_vyper_runtime_unit_allocs_ok] >>
  `MEM (mut,nr,rr,name,args,dflts,ret,stmts) (FST (classify_functions tops))` by
    simp[] >>
  `LENGTH dflts <= LENGTH args` by metis_tac[checked_grouped_defaults_length] >>
  pure_rewrite_tac[GSYM EVERY_MEM] >>
  metis_tac[grouped_package_keyword_widths]
QED

Theorem grouped_default_entry_member:
  package_external_group tops target trans keys (mut,nr,rr,name,args,dflts,ret,stmts) =
    ExternalDefaults common entries specs off /\
  MEM (prefix,k) (abi_entries args dflts) ==>
  MEM (abi_method_id (type_env tops) name (MAP SND prefix),external_prefix_label name k,
       min_calldata_size common.ec_env prefix 0,k) entries /\
  specs = MAP (\((n,ty),e). (n,ty,e))
    (ZIP (DROP (LENGTH args - LENGTH dflts) args,dflts)) /\
  common.ec_payable = (mut = Payable) /\
  off = min_calldata_size common.ec_env (TAKE (LENGTH args - LENGTH dflts) args) 0
Proof
  Cases_on `dflts = []` >> simp[package_external_group_def, NULL_EQ] >>
  simp[package_external_fn_def, set_external_package_target_def, LET_THM] >>
  Cases_on `ret = NoneT` >>
  simp[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
       LET_THM, compute_selector_method_id] >>
  rpt strip_tac >> gvs[min_calldata_size_def, MEM_MAP] >>
  qexists_tac `(prefix,k)` >> simp[]
QED

Theorem grouped_source_signature:
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (name,tys) (abi_external_signatures tops) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?pre post prefix k.
    FST (classify_functions tops) =
      pre ++ (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,name,args,
        subst_consts_exprs (module_consts_env tops []) dflts,ret,
        subst_consts_stmts (module_consts_env tops []) fbody)::post /\
    MEM (prefix,k) (abi_entries args dflts) /\
    tys = MAP SND prefix
Proof
  strip_tac >>
  `MEM (name,tys)
    (FLAT (MAP (\(m,n,r,f,a,d,t,b). abi_function_signatures f a d)
      (FST (classify_functions tops))))` by
    (rewrite_tac[classify_external_signatures] >>
     metis_tac[abi_signature_partition, sortingTheory.PERM_MEM_EQ]) >>
  pop_assum mp_tac >>
  simp[MEM_FLAT, MEM_MAP, pairTheory.EXISTS_PROD,
       abi_function_signatures_def, PULL_EXISTS] >>
  qx_genl_tac [`m'`,`n'`,`rr`,`a'`,`d'`,`t'`,`b'`,`prefix`,`k`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all classified_external_source_lookup >>
  strip_tac >> gvs[] >>
  qpat_assum `MEM (mut,nr,rr,name,args,_,ret,_) (FST (classify_functions tops))`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `lookup_raw_return_or_F (NONE:num option) name External tops = rr` by
    (drule classify_functions_external_source >> strip_tac >>
     gvs[constSubstTheory.subst_consts_fn_def]
     >- drule_all_then ACCEPT_TAC default_decl_raw_return >>
     `MEM (m',n',rr,name,a',rawdefaults,ret,rawbody) (public_getters tops)` by
       (simp[MEM_public_getters] >> qexists_tac `top` >> simp[]) >>
     drule_all_then ACCEPT_TAC default_selected_raw_return) >>
  qexistsl_tac [`l1`,`l2`,`prefix`,`k`] >>
  gvs[abi_entries_member, constSubstCorrectTheory.subst_consts_exprs_map]
QED

Theorem grouped_selector_from_source_miss:
  4 <= LENGTH cd /\
  FIND (\(name,tys). abi_method_id (type_env tops) name tys = cd_selector cd)
    (abi_external_signatures tops) = NONE /\
  groups = MAP (package_external_group tops target trans keys)
    (FST (classify_functions tops)) ==>
  EVERY (\group. case group of
    ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
  | ExternalDefaults common entries _ _ =>
      FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries = NONE) groups
Proof
  strip_tac >> irule grouped_selector_misses >>
  reverse conj_tac >- metis_tac[packaged_grouped_selector_width] >>
  drule cd_selector_method_id >> strip_tac >>
  qpat_x_assum `groups = _` SUBST1_TAC >>
  qpat_x_assum `FIND _ _ = NONE` mp_tac >>
  simp[FIND_NONE_EVERY, EVERY_MEM, combinTheory.o_DEF, pairTheory.FORALL_PROD] >>
  strip_tac >>
  `PERM (MAP FST (grouped_selectors
      (MAP (package_external_group tops target trans keys) (FST (classify_functions tops)))))
     (MAP (\(n,tys). abi_method_id (type_env tops) n tys)
       (abi_external_signatures tops))` by
    (`MAP FST (grouped_selectors
        (MAP (package_external_group tops target trans keys) (FST (classify_functions tops)))) =
      MAP (\(n,tys). abi_method_id (type_env tops) n tys)
       (FLAT (MAP abi_decl_signatures (FILTER explicit_external_decl tops)) ++
        FLAT (MAP abi_decl_signatures (FILTER (IS_SOME o public_getter) tops)))` by
       simp[grouped_selector_method_ids, MAP_APPEND, listTheory.MAP_FLAT,
         MAP_MAP_o, combinTheory.o_DEF] >>
     asm_rewrite_tac[] >> irule sortingTheory.PERM_MAP >>
     irule (GEN_ALL abi_signature_partition)) >>
  drule sortingTheory.PERM_MEM_EQ >>
  disch_then (qspec_then `w2n (calldata_method_id cd)` SUBST1_TAC) >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem grouped_selected_default_entry_shape:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  4 <= LENGTH cd /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME (name,tys) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\ dflts <> [] ==>
  ?pre post prefix k common entries specs off.
    MAP (package_external_group tops target trans keys) (FST (classify_functions tops)) =
      pre ++ ExternalDefaults common entries specs off::post /\
    EVERY (\group. case group of
      ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
    | ExternalDefaults _ es _ _ =>
        FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) es = NONE) pre /\
    FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) entries =
      SOME (cd_selector cd,external_prefix_label name k,
            min_calldata_size common.ec_env prefix 0,k) /\
    MEM (prefix,k) (abi_entries args dflts) /\ tys = MAP SND prefix /\
    specs = MAP (\((n,ty),e). (n,ty,e))
      (ZIP (DROP (LENGTH args - LENGTH dflts) args,
            subst_consts_exprs (module_consts_env tops []) dflts)) /\
    common.ec_payable = (mut = Payable) /\
    off = min_calldata_size common.ec_env (TAKE (LENGTH args - LENGTH dflts) args) 0 /\
    package_external_group tops target trans keys
      (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,name,args,
       subst_consts_exprs (module_consts_env tops []) dflts,ret,
       subst_consts_stmts (module_consts_env tops []) fbody) =
      ExternalDefaults common entries specs off
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (name,tys) (abi_external_signatures tops)` by
    metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all grouped_source_signature >>
  disch_then (qx_choosel_then [`before`,`after`,`prefix`,`k`] strip_assume_tac) >>
  qabbrev_tac `rr = lookup_raw_return_or_F (NONE:num option) name External tops` >>
  qabbrev_tac `spec_defaults = subst_consts_exprs (module_consts_env tops []) dflts` >>
  qabbrev_tac `spec_body = subst_consts_stmts (module_consts_env tops []) fbody` >>
  `spec_defaults <> []` by simp[Abbr `spec_defaults`, constSubstCorrectTheory.subst_consts_exprs_map] >>
  `?common entries specs off.
    package_external_group tops target trans keys (mut,nr,rr,name,args,spec_defaults,ret,spec_body) =
      ExternalDefaults common entries specs off` by
    (simp[package_external_group_def, LET_THM, NULL_EQ] >> pairarg_tac >> gvs[]) >>
  `MEM (prefix,k) (abi_entries args spec_defaults)` by
    fs[abi_entries_member, Abbr `spec_defaults`, constSubstCorrectTheory.subst_consts_exprs_map] >>
  drule_all grouped_default_entry_member >> strip_tac >>
  `abi_method_id (type_env tops) name (MAP SND prefix) = cd_selector cd` by
    (qpat_assum `FIND _ _ = SOME _` (mp_tac o MATCH_MP venomInstTheory.FIND_P) >>
     simp[pairTheory.FORALL_PROD]) >>
  drule cd_selector_method_id >> strip_tac >>
  qabbrev_tac `pack = package_external_group tops target trans keys` >>
  `MAP pack before ++ ExternalDefaults common entries specs off::MAP pack after =
    MAP pack (FST (classify_functions tops))` by
    (qpat_assum `FST (classify_functions tops) = _` SUBST1_TAC >>
     asm_simp_tac (srw_ss()) [MAP_APPEND, GSYM markerTheory.Abbrev_def]) >>
  `ALL_DISTINCT (MAP FST (grouped_selectors
       (MAP pack before ++ ExternalDefaults common entries specs off::MAP pack after))) /\
   EVERY (\(sel,_,_). sel < dimword (:256)) (grouped_selectors
       (MAP pack before ++ ExternalDefaults common entries specs off::MAP pack after))` by
    (qpat_assum `MAP pack before ++ ExternalDefaults common entries specs off::MAP pack after = _`
       (pure_rewrite_tac o single) >>
     simp[Abbr `pack`, packaged_grouped_selector_width] >>
     metis_tac[check_contract_grouped_selectors_distinct]) >>
  `MEM (w2n (calldata_method_id cd),external_prefix_label name k,
    min_calldata_size common.ec_env prefix 0,k) entries` by metis_tac[] >>
  drule_all grouped_default_selector_route >> strip_tac >>
  qexistsl_tac [`MAP pack before`,`MAP pack after`,`prefix`,`k`,`common`,`entries`,`specs`,`off`] >>
  fs[Abbr `spec_defaults`, Abbr `spec_body`, Abbr `rr`,
     constSubstCorrectTheory.subst_consts_exprs_map]
QED

Theorem grouped_package_common_environment:
  set_external_package_target target (package_external_fn tops trans keys
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pa,z,pay,guarded,key,ut,view,compiled,rt) /\
  package_external_group tops target trans keys
      (mut,nr,rr,name,args,dflts,ret,fbody) =
    ExternalDefaults common entries specs off ==>
  common.ec_env = ce /\ common.ec_payable = pay /\
  common.ec_nonreentrant = guarded /\ common.ec_nkey = key /\
  common.ec_transient = ut /\ common.ec_view = view /\
  common.ec_body = compiled /\ common.ec_return = rt /\
  common.ec_pos_args = build_positional_args ce (TAKE (LENGTH args - LENGTH dflts) args)
Proof
  Cases_on `dflts` >> simp[package_external_group_def, LET_THM] >>
  rpt strip_tac >> gvs[]
QED

Theorem grouped_package_external_defaults:
  package_external_fn tops trans keys
    (mut,nr,rr,name,args,subst_consts_exprs (module_consts_env tops []) dflts,ret,fbody) =
  package_external_fn tops trans keys (mut,nr,rr,name,args,dflts,ret,fbody)
Proof
  simp[package_external_fn_def, constSubstCorrectTheory.subst_consts_exprs_map]
QED

Theorem grouped_selected_legacy_entry_shape:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  4 <= LENGTH cd /\
  FIND (\(n,ts). abi_method_id (type_env tops) n ts = cd_selector cd)
    (abi_external_signatures tops) = SOME (name,tys) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  ?pre post lbl z pkg.
    MAP (package_external_group tops target trans keys) (FST (classify_functions tops)) =
      pre ++ ExternalSingle (cd_selector cd,lbl,z) pkg::post /\
    EVERY (\group. case group of
      ExternalSingle (sel,_,_) _ => calldata_method_id cd <> n2w sel
    | ExternalDefaults _ es _ _ =>
        FIND (\(sel,_,_,_). calldata_method_id cd = n2w sel) es = NONE) pre /\
    tys = MAP SND args /\ lbl = "fn_" ++ name /\
    pkg = set_external_package_target target (package_external_fn tops trans keys
      (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,name,args,([]:expr list),
       ret,subst_consts_stmts (module_consts_env tops []) fbody))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (name,tys) (abi_external_signatures tops)` by metis_tac[venomInstTheory.FIND_MEM] >>
  drule_all grouped_source_signature >>
  disch_then (qx_choosel_then [`before`,`after`,`prefix`,`k`]
    (map_every assume_tac o CONJUNCTS)) >>
  `prefix = args` by (fs[abi_entries_member] >> simp[TAKE_LENGTH_ID_rwt]) >>
  `abi_method_id (type_env tops) name (MAP SND args) = cd_selector cd` by
    (qpat_assum `FIND _ _ = SOME _` (mp_tac o MATCH_MP venomInstTheory.FIND_P) >>
     simp[pairTheory.FORALL_PROD]) >>
  drule cd_selector_method_id >> strip_tac >>
  qabbrev_tac `pack = package_external_group tops target trans keys` >>
  qabbrev_tac `pkg = set_external_package_target target (package_external_fn tops trans keys
    (mut,nr,lookup_raw_return_or_F (NONE:num option) name External tops,name,args,([]:expr list),
      ret,subst_consts_stmts (module_consts_env tops []) fbody))` >>
  `MAP pack (FST (classify_functions tops)) =
    MAP pack before ++ ExternalSingle (cd_selector cd,"fn_" ++ name,cd_selector cd MOD 256 = 0)
      pkg::MAP pack after` by
    (qpat_assum `FST (classify_functions tops) = _` SUBST1_TAC >>
     qpat_assum `abi_method_id _ _ _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [abi_method_id_def,
         GSYM calldata_method_id_four_bytes]) >>
     simp[Abbr `pack`, Abbr `pkg`, package_external_group_def, LET_THM,
       constSubstCorrectTheory.subst_consts_exprs_map, compute_selector_def,
       selector_has_trailing_zeroes_def]) >>
  `ALL_DISTINCT (MAP FST (grouped_selectors
    (MAP pack before ++ ExternalSingle (cd_selector cd,"fn_" ++ name,cd_selector cd MOD 256 = 0)
      pkg::MAP pack after))) /\
   EVERY (\(sel,_,_). sel < dimword (:256))
     (grouped_selectors (MAP pack before ++
      ExternalSingle (cd_selector cd,"fn_" ++ name,cd_selector cd MOD 256 = 0)
        pkg::MAP pack after))` by
    (qpat_assum `MAP pack (FST (classify_functions tops)) = _`
       (SUBST1_TAC o SYM) >>
     qunabbrev_tac `pack` >>
     conj_tac
     >- (irule check_contract_grouped_selectors_distinct >> goal_assum (drule_at Any)) >>
     MATCH_ACCEPT_TAC packaged_grouped_selector_width) >>
  qexistsl_tac [`MAP pack before`,`MAP pack after`,`"fn_" ++ name`,
    `cd_selector cd MOD 256 = 0`,`pkg`] >>
  asm_rewrite_tac[] >>
  irule grouped_selector_misses >>
  fs[grouped_selectors_def, external_group_selectors_def, MAP_APPEND, FLAT_APPEND,
     ALL_DISTINCT_APPEND, EVERY_APPEND] >>
  metis_tac[]
QED

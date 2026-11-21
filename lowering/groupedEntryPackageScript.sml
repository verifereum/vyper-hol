(* Source parameters and selectors of grouped external entries. *)
Theory groupedEntryPackage
Ancestors
  compileVyper moduleLowering compileEnv selectorCompilerProps vyperABIEntries
  loweringShapeProps vyperTypeContractContext vyperTypeContract vyperTypeBindArguments
  publicGetterProps constSubst
  calldataSelectorProps entryDispatchProps mem2varBlockSimHelpers
  checkedSelectorTableProps dispatchedValueSelection constSubstCorrect
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

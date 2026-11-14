(* Typed source-place frames and memory projection facts for array loops. *)
Theory whitelistForIterMem
Ancestors
  vyperTypeContract
  whitelistForIterDynFrag stmtSimForArrayFrame exprSimSubscriptMap exprSimDefs loweringPosts
  stmtSimDefs gasOutcome gasSummary supportedStmts supportedExprTraverse vyperTypeSystem vyperState context
  vyperInterpreter valueEncoding valueEncodingDefs valueEncodingProps valueEncodingProofs
  stmtLowering exprLowering venomState
  exprSimPopNestedLocalMemory vyperTargetPlaceWrite compileVyper vyperTypeInvariants vyperTypeContract vyperPureExpr abiEncoderMemory immutableValue immutableEncoding immutableEncodingProofs exprSimTopLevelImmutable gasSummary fragGasPath fragGasMode exprSimArrayIndex immutableCopyExecution varsExt freshWrites fragGasSeq fragGasSeqAbort exprOperandVar exprSimWordArgs exprBopSimProps bodySim targetPlaceSim targetPlaceSimCasesBase targetPlaceSimCases targetPlaceSimDefs exprSimHypsDefs exprSimDefs loweringPosts gasOutcome gasContext exprLowering exprLoweringProps compileEnv loweringStateRelDefs vyperAST vyperState vyperInterpreter vyperTypeSystem vyperTypeCallGraph venomState
  compileEnv loweringStateRelDefs exprLoweringProps list finite_map arithmetic words bodySimAugPlaceMemory

(* Moved from exprSimPopImmutableTarget, deleted on the combined head:
   a typed subscript path into a value in memory. *)
Theorem imm_typed_step_memory:
  !tv v sub d ptv pv b mem.
    value_has_type tv v /\ well_formed_type_value tv /\
    mem_path_offset tv [sub] = SOME (d,ptv) /\
    evaluate_subscripts tv v [sub] = INL pv /\
    val_in_memory tv v b mem ==>
    val_in_memory ptv pv (b+d) mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `sub`
  >- ((rename1 `ValueSubscript idx` >> Cases_on `idx` >>
       Cases_on `tv` >>
       gvs[mem_path_offset_def, mem_step_offset_def, AllCaseEqs()] >>
       Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
       rename1 `ArrayV av` >> Cases_on `av` >>
       gvs[vyperTypingTheory.value_has_type_def, evaluate_subscripts_def,
           vyperValueOperationTheory.array_index_def, AllCaseEqs()])
      >- (gvs[valueEncodingPropsTheory.val_in_memory_tuple] >>
          `LENGTH l' = LENGTH l` by
            metis_tac[vyperTypingTheory.values_have_types_length] >>
          `!xs. type_memory_size_list xs = SUM (MAP type_memory_size xs)` by
            (Induct >> simp[valueEncodingTheory.type_memory_size_def]) >>
          gvs[listTheory.oEL_EQ_EL] >>
          irule tupleMemoryLayoutTheory.tuple_in_memory_element >> simp[])
      >- (Cases_on `b'` >>
           gvs[vyperTypingTheory.value_has_type_def, mem_step_offset_def,
               valueEncodingPropsTheory.val_in_memory_dynarray,
               listTheory.oEL_EQ_EL] >>
           drule exprSimAggregateEncodingTheory.elems_in_memory_EL >>
           disch_then (qspec_then `Num i` mp_tac) >>
           simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM])
       >- (gvs[mem_step_offset_def,
               valueEncodingPropsTheory.val_in_memory_sarray]) >>
      gvs[mem_step_offset_def, valueEncodingPropsTheory.val_in_memory_sarray] >>
      metis_tac[valueEncodingProofsTheory.kvs_in_memory_lookup]) >>
  Cases_on `tv` >>
  gvs[mem_path_offset_def, mem_step_offset_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, evaluate_subscripts_def,
      valueEncodingPropsTheory.val_in_memory_struct, AllCaseEqs()] >>
  qpat_x_assum `well_formed_type_value _` kall_tac >>
  rpt (pop_assum mp_tac) >>
  map_every qid_spec_tac [`b`, `pv`, `ptv`, `d`, `s`, `l'`, `l`] >>
  Induct >> Cases_on `l'` >>
  simp[vyperTypingTheory.value_has_type_def, mem_field_offset_def] >>
  rpt gen_tac >> PairCases_on `h` >> PairCases_on `h'` >>
  simp[vyperTypingTheory.value_has_type_def, mem_field_offset_def,
       valueEncodingDefsTheory.val_in_memory_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h0 = s` >> gvs[AllCaseEqs()] >>
  rpt strip_tac >> PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem imm_typed_path_memory:
  !path tv v k ptv pv b mem.
    value_has_type tv v /\ well_formed_type_value tv /\
    mem_path_offset tv path = SOME (k,ptv) /\
    evaluate_subscripts tv v path = INL pv /\
    val_in_memory tv v b mem ==>
    val_in_memory ptv pv (b+k) mem
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), pairTheory.EXISTS_PROD] >>
  `mem_path_offset tv [h] = SOME (p_1,p_2)` by
    simp[mem_path_offset_def] >>
  drule exprSimPropsTheory.mem_path_offset_sound >>
  simp[vyperStateTheory.subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule vyperPlaceStatePreservationTheory.evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `v`] mp_tac) >>
  gvs[AllCaseEqs()] >> strip_tac >>
  `val_in_memory p_2 v' (b + p_1) mem` by
    (irule imm_typed_step_memory >> goal_assum (drule_at Any) >> simp[]) >>
  `value_has_type p_2 v' /\ well_formed_type_value p_2` by
    (metis_tac[vyperPlaceStatePreservationTheory.evaluate_subscripts_type,
       vyperPlaceStatePreservationTheory.subscripts_type_well_formed,
       exprSimPropsTheory.mem_path_offset_sound]) >>
  first_x_assum drule_all >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem type_place_target_attribute_prefix[local]:
  !attrs env tgt vt.
    type_place_target env
      (FOLDL (\t a. AttributeTarget t a) tgt attrs) = SOME vt ==>
    ?base. type_place_target env tgt = SOME base
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem attribute_type_fold_none[local]:
  !xs D. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) NONE xs = NONE
Proof
  Induct >> simp[]
QED

Theorem attribute_type_fold_append[local]:
  !xs ys D ot.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot (xs ++ ys) =
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a))
      (FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs) ys
Proof
  Induct >> simp[]
QED

Theorem attribute_type_fold_inert[local]:
  !xs ys D ot t u.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs = SOME t /\
    (!a. attribute_type D t a = NONE) /\
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot (xs ++ ys) = SOME u ==>
    ys = []
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ys` >> gvs[attribute_type_fold_append, attribute_type_fold_none]
QED

Theorem place_access_attribute_chain[local]:
  !xs r ys.
    (r = NameTarget root \/ (?n. r = TopLevelNameTarget n)) ==>
    place_access (FOLDL (\t a. AttributeTarget t a) r xs) ys = (r,xs ++ ys)
Proof
  Induct_on `xs` using SNOC_INDUCT
  >- (rpt strip_tac >> gvs[place_access_def]) >>
  simp[FOLDL_SNOC, place_access_def, SNOC_APPEND] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`r`, `x::ys`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem place_access_chain_or_reset[local]:
  !p. (!r xs. place_access p [] = (r,xs) ==>
    (p = FOLDL (\t a. AttributeTarget t a) r xs /\
     !ys. place_access p ys = (r,xs ++ ys)) \/
    (!ys. place_access p ys = (r,xs)))
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- simp[place_access_def]
  >- simp[place_access_def]
  >- (rpt strip_tac >> gvs[place_access_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `place_access p []` >>
  first_x_assum (qspecl_then [`q`, `r'`] mp_tac) >> simp[] >>
  strip_tac >> simp[place_access_def] >>
  strip_tac >> gvs[GSYM SNOC_APPEND, FOLDL_SNOC]
QED

Theorem type_place_expr_not_local[local]:
  !e env vt p root xs.
    type_place_expr env e = SOME vt /\ loop_iterator_place e = SOME p ==>
    place_access p [] <> (NameTarget root,xs)
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  simp[Once well_typed_expr_def, loop_iterator_place_def, supported_expr_exists_def, place_access_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[Once well_typed_expr_def, place_access_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem typed_expr_access_endpoint[local]:
  !e env p root xs.
    well_typed_expr env e /\ loop_iterator_place e = SOME p /\
    place_access p [] = (NameTarget root,xs) ==>
    ?t. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type env.type_defs ty a))
          (FLOOKUP env.var_types root) xs = SOME t /\
        ((p = FOLDL (\t a. AttributeTarget t a) (NameTarget root) xs /\
          t = expr_type e) \/ ((!a. attribute_type env.type_defs t a = NONE) /\
          (!ys. place_access p ys = (NameTarget root,xs))))
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[loop_iterator_place_def, supported_expr_exists_def, AllCaseEqs()]
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def,
                          vyperASTTheory.expr_type_def])
  >- (rpt strip_tac >> gvs[place_access_def])
  >- (rpt strip_tac >>
      gvs[Once well_typed_expr_def, place_access_def]
      >- (qpat_x_assum `!env'. well_typed_expr env' e ==> _`
            (qspec_then `env` mp_tac) >> simp[] >> strip_tac >>
          rename1 `FOLDL _ _ xs = SOME endpoint` >>
          qexists_tac `endpoint` >> simp[] >>
          Cases_on `expr_type e` >> gvs[subscript_type_ok_def, attribute_type_def]) >>
      metis_tac[type_place_expr_not_local]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def] >>
  Cases_on `place_access tgt []` >>
  drule place_access_chain_or_reset >> strip_tac >>
  gvs[]
  >- (`~(!ys:string list. ys = [])` by
        (strip_tac >> first_x_assum (qspec_then `[s]` mp_tac) >> simp[]) >>
      qpat_x_assum `!env'. _` (qspec_then `env` mp_tac) >> simp[] >>
      strip_tac >>
      gvs[attribute_type_fold_append, attribute_type_ok_def,
          GSYM SNOC_APPEND, FOLDL_SNOC, vyperASTTheory.expr_type_def]) >>
  qpat_x_assum `!env'. _` (qspec_then `env` mp_tac) >> simp[] >>
  strip_tac
  >- (qpat_x_assum `!ys. place_access _ ys = _`
        (qspec_then `[s]` mp_tac) >>
      simp[place_access_attribute_chain] >>
      disch_then (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[]) >>
  metis_tac[]
QED

Theorem typed_target_access_endpoint[local]:
  !w env vt root xs.
    type_place_target env w = SOME vt /\
    place_access w [] = (NameTarget root,xs) ==>
    ?t. FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type env.type_defs ty a))
          (FLOOKUP env.var_types root) xs = SOME t /\
        ((w = FOLDL (\t a. AttributeTarget t a) (NameTarget root) xs /\
          vt = Type t) \/ (!ys. place_access w ys = (NameTarget root,xs)))
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def, place_access_def,
                           AllCaseEqs()])
  >- (rpt strip_tac >> gvs[place_access_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once well_typed_expr_def, place_access_def, AllCaseEqs()] >>
      rpt strip_tac >> first_x_assum drule >> simp[] >>
      strip_tac >> metis_tac[place_access_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `place_access w []` >>
  drule place_access_chain_or_reset >> strip_tac >>
  gvs[place_access_def]
  >- (qpat_x_assum `!ys. place_access _ ys = _`
        (qspec_then `[s]` assume_tac) >> gvs[] >>
      `~(!ys:string list. ys = [])` by
        (strip_tac >> first_x_assum (qspec_then `[s]` mp_tac) >> simp[]) >>
      qpat_x_assum `!env' vt'. _` drule >> simp[] >> strip_tac >>
      gvs[attribute_type_fold_append, GSYM SNOC_APPEND, FOLDL_SNOC]) >>
  qpat_x_assum `!env' vt'. _` drule >> simp[] >> strip_tac >>
  metis_tac[]
QED

Theorem attribute_type_fold_separation[local]:
  !D ot xs ws t u.
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot xs = SOME t /\
    (!a. attribute_type D t a = NONE) /\
    FOLDL (\ot a. OPTION_BIND ot (\ty. attribute_type D ty a)) ot ws = SOME u /\
    ~isPREFIX ws xs ==> ~isPREFIX xs ws
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all attribute_type_fold_inert >> strip_tac >> gvs[]
QED

Theorem typed_place_write_separation[local]:
  !env e et bd p root xs envw w vt ws.
    well_typed_expr env e /\ expr_type e = ArrayT et bd /\
    loop_iterator_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    type_place_target envw w = SOME vt /\
    envw.type_defs = env.type_defs /\
    FLOOKUP envw.var_types root = FLOOKUP env.var_types root /\
    ~place_contains w p /\ place_access w [] = (NameTarget root,ws) ==>
    ~isPREFIX ws xs /\ ~isPREFIX xs ws
Proof
  rpt gen_tac >> strip_tac >>
  `~isPREFIX ws xs` by gvs[place_contains_def] >> simp[] >>
  drule_all typed_expr_access_endpoint >>
  disch_then (qx_choose_then `endpoint` strip_assume_tac) >>
  `!a. attribute_type env.type_defs endpoint a = NONE` by
    gvs[attribute_type_def] >>
  drule_all typed_target_access_endpoint >> strip_tac >>
  irule attribute_type_fold_separation >> simp[] >>
  qexistsl_tac [`env.type_defs`, `FLOOKUP env.var_types root`, `endpoint`] >>
  gvs[] >> metis_tac[]
QED

Theorem assign_subscripts_divergent_attrs[local]:
  !xs ws tv v tail ao v'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    assign_subscripts tv v (MAP AttrSubscript ws ++ tail) ao = INL v' ==>
    evaluate_subscripts tv v' (MAP AttrSubscript xs) =
    evaluate_subscripts tv v (MAP AttrSubscript xs)
Proof
  Induct >> simp[] >> Cases_on `ws` >> simp[] >>
  rpt gen_tac >> strip_tac >> Cases_on `v` >>
  gvs[assign_subscripts_def, AllCaseEqs()] >>
  Cases_on `h = h'`
  >- (gvs[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP] >>
      first_x_assum (qspec_then `t` mp_tac) >> simp[] >>
      disch_then drule >> simp[] >> disch_then (fn th => rewrite_tac[th])) >>
  `h' <> h` by metis_tac[] >>
  simp[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP] >>
  Cases_on `ALOOKUP l h'` >> simp[]
QED

Theorem replace_memory_entry_divergent_attrs[local]:
  !xs ws entry tail v entry'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    replace_memory_entry entry (MAP AttrSubscript ws ++ tail) v = INL entry' ==>
    entry'.type = entry.type /\
    evaluate_subscripts entry'.type entry'.value (MAP AttrSubscript xs) =
    evaluate_subscripts entry.type entry.value (MAP AttrSubscript xs)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[replace_memory_entry_def, AllCaseEqs()] >>
  simp[] >> metis_tac[assign_subscripts_divergent_attrs]
QED

Theorem write_place_divergent_attrs[local]:
  !cx root xs ws tail v es res es'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    write_place cx (MemoryPlace root (MAP AttrSubscript ws ++ tail)) v es = (res,es') ==>
    LENGTH es'.scopes = LENGTH es.scopes /\
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `find_containing_scope root es.scopes`
  >- gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
         return_def, raise_def] >>
  rename1 `find_containing_scope root es.scopes = SOME found` >>
  PairCases_on `found` >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  rename1 `FLOOKUP local root = SOME entry` >>
  Cases_on `replace_memory_entry entry (MAP AttrSubscript ws ++ tail) v` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs(), FLOOKUP_UPDATE] >>
  drule_all replace_memory_entry_divergent_attrs >> simp[]
QED

Theorem eval_base_place_attribute_prefix[local]:
  !target cx es root path es' pending xs.
    eval_base_place cx target es = (INL (PlaceR (MemoryPlace root path)),es') /\
    place_access target pending = (NameTarget root,xs) ==>
    ?tail. path ++ MAP AttrSubscript pending = MAP AttrSubscript xs ++ tail
Proof
  ho_match_mp_tac targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
          place_access_def])
  >- (rpt strip_tac >>
      gvs[place_access_def])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      drule bodySimAugPlaceMemoryTheory.aug_place_extend_memory_inversion >>
      strip_tac >> gvs[place_access_def] >>
      first_x_assum drule >> disch_then (qspec_then `[]` mp_tac) >>
      simp[] >> strip_tac >> simp[APPEND_ASSOC] >> metis_tac[APPEND_ASSOC]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule bodySimAugPlaceMemoryTheory.aug_place_extend_memory_inversion >>
  strip_tac >> gvs[place_access_def] >>
  first_x_assum drule >> disch_then (qspec_then `s::pending` mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem memory_iterator_source_path_prefix:
  !e cx es ee target root attrs pending path.
    loop_iterator_place e = SOME target /\
    place_access target pending = (NameTarget root, attrs) /\
    eval_expr cx e es = (INL (PlaceR (MemoryPlace root path)), ee) ==>
    ?tail. path ++ MAP AttrSubscript pending = MAP AttrSubscript attrs ++ tail
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[loop_iterator_place_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[place_access_def, Once evaluate_def, bind_def, ignore_bind_def,
      get_scopes_def, type_check_def, check_def, assert_def, return_def,
      raise_def, AllCaseEqs()] >>
  drule exprSimPropsTheory.select_result_memory_place >>
  disch_then (qspecl_then [`root`, `path`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  gvs[COND_RATOR, bind_def, return_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[MAP]
QED

Theorem eval_target_place_attribute_prefix[local]:
  !target cx es root path es'.
    eval_target_place cx target es = (INL (MemoryPlace root path),es') ==>
    ?xs tail. place_access target [] = (NameTarget root,xs) /\
              path = MAP AttrSubscript xs ++ tail
Proof
  rpt strip_tac >>
  drule eval_target_place_memory_root >> strip_tac >>
  Cases_on `place_access target []` >> gvs[] >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule eval_base_place_attribute_prefix >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem typed_memory_write_attribute_projection[local]:
  !env e et bd p root xs envw w vt cx es path evaluated mid v res es'.
    well_typed_expr env e /\ expr_type e = ArrayT et bd /\
    loop_iterator_place e = SOME p /\ place_access p [] = (NameTarget root,xs) /\
    type_place_target envw w = SOME vt /\
    envw.type_defs = env.type_defs /\
    FLOOKUP envw.var_types root = FLOOKUP env.var_types root /\
    ~place_contains w p /\
    eval_target_place cx w es = (INL (MemoryPlace root path),evaluated) /\
    write_place cx (MemoryPlace root path) v mid = (res,es') ==>
    LENGTH es'.scopes = LENGTH mid.scopes /\
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) mid.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule eval_target_place_attribute_prefix >> strip_tac >>
  drule_all typed_place_write_separation >> strip_tac >>
  gvs[] >> drule_all write_place_divergent_attrs >> simp[]
QED

Theorem scope_projection_observe[local]:
  !s t root f.
    MAP (\sc. FLOOKUP sc root) t.scopes = MAP (\sc. FLOOKUP sc root) s.scopes ==>
    MAP (\sc. f (FLOOKUP sc root)) t.scopes =
    MAP (\sc. f (FLOOKUP sc root)) s.scopes
Proof
  rpt strip_tac >>
  simp[GSYM combinTheory.o_DEF, GSYM MAP_MAP_o]
QED

Theorem type_stmt_reference_transport[local]:
  !env ret_ty stmt next ref root.
    type_stmt env ret_ty stmt = SOME next /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM ref.var_types ==>
    next.type_defs = ref.type_defs /\
    FLOOKUP next.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM next.var_types
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperTypeEnvExtensionTheory.type_stmt_preserve_nonlocal_fields >>
  strip_tac >> gvs[] >>
  Cases_on `FLOOKUP ref.var_types root`
  >- gvs[FLOOKUP_DEF] >>
  drule vyperTypeEnvExtensionTheory.type_stmt_var_types_preserve >>
  disch_then drule >> simp[] >> gvs[FLOOKUP_DEF]
QED

Theorem attribute_projection_length[local]:
  !f a b. MAP f a = MAP f b ==> LENGTH a = LENGTH b
Proof
  metis_tac[LENGTH_MAP]
QED

Theorem attribute_projection_and_length[local]:
  !f a b. MAP f a = MAP f b ==> MAP f a = MAP f b /\ LENGTH a = LENGTH b
Proof
  metis_tac[LENGTH_MAP]
QED

Theorem pop_place_divergent_attrs[local]:
  !cx root xs ws tail es res es'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    pop_place cx (MemoryPlace root (MAP AttrSubscript ws ++ tail)) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `find_containing_scope root es.scopes`
  >- gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
         return_def, raise_def] >>
  rename1 `find_containing_scope root es.scopes = SOME found` >>
  PairCases_on `found` >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  rename1 `FLOOKUP local root = SOME entry` >>
  gvs[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
      lift_option_type_def, lift_sum_def, type_check_def, assert_def,
      check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
  fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  gvs[] >>
  pairarg_tac >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, return_def, lift_sum_def,
      raise_def, AllCaseEqs(), FLOOKUP_UPDATE] >>
  Cases_on `evaluate_subscripts entry.type entry.value
              (MAP AttrSubscript ws ++ tail)` >>
  gvs[]
  >- (Cases_on `assign_subscripts entry.type entry.value
                  (MAP AttrSubscript ws ++ tail) (Replace shortened)` >>
      gvs[return_def, raise_def] >>
      imp_res_tac assign_subscripts_divergent_attrs >> gvs[]) >>
  Cases_on `replace_popped entry.type (MAP AttrSubscript ws ++ tail)
              shortened entry.popped` >>
  gvs[return_def, raise_def]
QED

(* The attribute instance of the evaluator frame: the projection reads only
   the scopes, so internal calls need no exclusion. *)
Theorem eval_attribute_frame[local]:
  (!cx e st res st'.
     expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) e /\
     eval_expr cx e st = (res,st') ==>
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st'.scopes =
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st.scopes) /\
  (!cx es st res st'.
     EVERY (expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)) es /\
     eval_exprs cx es st = (res,st') ==>
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st'.scopes =
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st.scopes) /\
  (!cx t st res st'.
     target_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) t /\
     eval_target_place cx t st = (res,st') ==>
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st'.scopes =
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) st.scopes)
Proof
  qspecl_then [`\c s. MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) s.scopes`,
               `(\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)`]
    mp_tac eval_observation_frame_mutual >>
  impl_tac
  >- (conj_tac >- simp[] >>
      rpt gen_tac >> BETA_TAC >> strip_tac >>
      Cases_on `?path. p = MemoryPlace root path`
      >- (gvs[] >> drule eval_target_place_attribute_prefix >> strip_tac >>
          gvs[] >> drule_all pop_place_divergent_attrs >> simp[]) >>
      `!r path. p = MemoryPlace r path ==> r <> root` by metis_tac[] >>
      drule_all pop_place_name_projection >> strip_tac >>
      irule scope_projection_observe >> simp[]) >>
  BETA_TAC >> strip_tac >>
  `!(c:evaluation_context) (s:evaluation_state) t. s.scopes = t.scopes ==>
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) s.scopes =
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) t.scopes` by simp[NoAsms] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem typed_attribute_writes_ok[local]:
  !ref arr_e et bd p root xs env.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root ==>
    (!w vt ws. type_place_target env w = SOME vt /\ ~place_contains w p /\
       place_access w [] = (NameTarget root,ws) ==>
       ~isPREFIX ws xs /\ ~isPREFIX xs ws) /\
    (!e. well_typed_expr env e /\ expr_writes_ok (\w. ~place_contains w p) e ==>
       expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) e) /\
    (!es. well_typed_exprs env es /\ EVERY (expr_writes_ok (\w. ~place_contains w p)) es ==>
       EVERY (expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)) es) /\
    (!t. IS_SOME (type_place_target env t) /\ target_writes_ok (\w. ~place_contains w p) t ==>
       target_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) t)
Proof
  rpt gen_tac >> strip_tac >>
  `!w vt ws. type_place_target env w = SOME vt /\ ~place_contains w p /\
     place_access w [] = (NameTarget root,ws) ==>
     ~isPREFIX ws xs /\ ~isPREFIX xs ws` by
    (rpt gen_tac >> strip_tac >>
     irule typed_place_write_separation >> simp[] >>
     goal_assum (drule_at (Pat `type_place_target _ _ = _`)) >>
     goal_assum (drule_at (Pat `well_typed_expr _ _`)) >> simp[]) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac
  >- (drule_then irule (cj 1 writes_ok_typed_mono) >>
      qexists_tac `(\w. ~place_contains w p)` >> simp[] >> metis_tac[])
  >- (drule_then irule (cj 4 writes_ok_typed_mono) >>
      qexists_tac `(\w. ~place_contains w p)` >> simp[] >> metis_tac[]) >>
  drule_then irule (cj 3 writes_ok_typed_mono) >>
  qexists_tac `(\w. ~place_contains w p)` >> simp[] >> metis_tac[]
QED

Theorem typed_expr_attribute[local]:
  !ref arr_e et bd p root xs env e cx st res st'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_expr env e /\ expr_writes_ok (\w. ~place_contains w p) e /\
    eval_expr cx e st = (res,st') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_attribute_writes_ok >> strip_tac >>
  `expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) e` by (first_x_assum irule >> simp[]) >>
  drule_all (cj 1 eval_attribute_frame) >> simp[]
QED

Theorem typed_exprs_attribute[local]:
  !ref arr_e et bd p root xs env es cx st res st'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_exprs env es /\ EVERY (expr_writes_ok (\w. ~place_contains w p)) es /\
    eval_exprs cx es st = (res,st') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_attribute_writes_ok >> strip_tac >>
  `EVERY (expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)) es` by (first_x_assum irule >> simp[]) >>
  drule_all (cj 2 eval_attribute_frame) >> simp[]
QED

Theorem typed_custom_error_attribute[local]:
  !ref arr_e et bd p root xs env err params es cx st res st'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_custom_error env err /\
    EVERY (expr_writes_ok (\w. ~place_contains w p)) (custom_error_exprs err) /\
    order_custom_error_args params err = SOME es /\
    eval_exprs cx es st = (res,st') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_attribute_writes_ok >> strip_tac >>
  `EVERY (expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)) (custom_error_exprs err)` by
    (first_x_assum irule >> gvs[well_typed_custom_error_def]) >>
  `EVERY (expr_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws)) es` by
    metis_tac[sortingTheory.PERM_EVERY, vyperASTTheory.order_custom_error_args_perm] >>
  drule_all (cj 2 eval_attribute_frame) >> simp[]
QED

Theorem typed_target_attribute[local]:
  !ref arr_e et bd p root xs env t vt cx st res st'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    type_place_target env t = SOME vt /\ target_writes_ok (\w. ~place_contains w p) t /\
    eval_target_place cx t st = (res,st') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  drule_all typed_attribute_writes_ok >> strip_tac >>
  `target_writes_ok (\w. !ws. place_access w [] = (NameTarget root,ws) ==>
         ~isPREFIX ws xs /\ ~isPREFIX xs ws) t` by (first_x_assum irule >> simp[]) >>
  drule_all (cj 3 eval_attribute_frame) >> simp[]
QED

Theorem typed_iterator_attribute[local]:
  !ref arr_e et bd p root xs env typ it cx st res st'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_iterator env typ it /\
    (case it of
     | Array e => expr_writes_ok (\w. ~place_contains w p) e
     | Range x y => expr_writes_ok (\w. ~place_contains w p) x /\ expr_writes_ok (\w. ~place_contains w p) y) /\
    eval_iterator cx it st = (res,st') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) st.scopes
Proof
  rpt gen_tac >> strip_tac >>
  `!e s r t. well_typed_expr env e /\ expr_writes_ok (\w. ~place_contains w p) e /\
     eval_expr cx e s = (r,t) ==>
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) t.scopes =
     MAP (\sc. OPTION_MAP
       (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
       (FLOOKUP sc root)) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  Cases_on `it` >> gvs[well_typed_iterator_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac array_iterator_results_state >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
  gvs[return_def, IgnAsm `!e s r t. _`] >> res_tac >> gvs[IgnAsm `!e s r t. _`]
QED

Theorem typed_target_write_attribute[local]:
  !ref arr_e et bd p root xs env w vt cx v es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    type_place_target env w = SOME vt /\ ~place_contains w p /\
    target_writes_ok (\w. ~place_contains w p) w /\
    (do dest <- eval_target_place cx w; write_place cx dest v od) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, AllCaseEqs(), raise_def] >>
  drule_all typed_target_attribute >> strip_tac >>
  TRY (metis_tac[attribute_projection_length]) >>
  rename1 `write_place cx dest v mid = (res,es')` >>
  `MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) mid.scopes` by
    (Cases_on `?path. dest = MemoryPlace root path`
     >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
     `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
     drule_all write_guarded_place_projection >> strip_tac >>
     irule scope_projection_observe >> simp[]) >>
  gvs[] >> metis_tac[attribute_projection_length]
QED

Theorem typed_assignment_attribute_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:eval_result list). T) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!cx target v. !ref arr_e et bd p root xs env ty es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\w. ~place_contains w p) target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!cx targets vs. !ref arr_e et bd p root xs env tys es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
    EVERY (atarget_writes_ok (\w. ~place_contains w p)) targets /\
    assign_tuple_target_list cx targets vs es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> rpt strip_tac
  >>~- ([`assign_tuple_targets _ (BaseTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      drule_at (Pat `_ = (res,es')`) typed_target_write_attribute >>
      disch_then (qspecl_then [`ref`,`arr_e`,`et`,`bd`,`p`,`root`,`xs`,
                               `env`,`Type ty`] mp_tac) >>
      simp[])
  >>~- ([`assign_tuple_targets _ (TupleTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, atarget_writes_ok_def, SF ETA_ss] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, raise_def, vyperValueTheory.value_CASE_rator,
           vyperValueTheory.array_value_CASE_rator, AllCaseEqs()] >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[LIST_REL_CONS1, SF ETA_ss] >> metis_tac[]
QED

Theorem annassign_attribute_frame[local]:
  !cx id typ rhs root xs es res es'.
    id <> root /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) t.scopes =
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) s.scopes) /\
    eval_stmt cx (AnnAssign id typ rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac
  >~ [`new_variable _ _ _ _ = _`]
  >- (rename1 `new_variable id tyv nv mid = (res,es')` >>
      drule_all new_variable_other_projection >> strip_tac >>
      `MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) es'.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) mid.scopes` by
        (irule scope_projection_observe >> simp[]) >>
      gvs[] >> metis_tac[attribute_projection_length]) >>
  metis_tac[attribute_projection_length]
QED

Theorem assign_attribute_frame[local]:
  !ref arr_e et bd p root xs env target ty rhs cx es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\w. ~place_contains w p) target /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) t.scopes =
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) s.scopes) /\
    eval_stmt cx (Assign target rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `target` >> rpt gen_tac >> strip_tac >>
  irule attribute_projection_and_length
  >~ [`eval_stmt _ (Assign (BaseTarget _) _) _ = _`]
  >- (rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
      gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
      qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      drule_all typed_target_attribute >> strip_tac >> gvs[] >>
      rename1 `write_place cx dest v mid = (res,es')` >>
      `MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) es'.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) mid.scopes` by
        (Cases_on `?path. dest = MemoryPlace root path`
         >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
         `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
         drule_all write_guarded_place_projection >> strip_tac >>
         irule scope_projection_observe >> simp[]) >>
      gvs[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)
    (cj 9 typed_assignment_attribute_mutual) >>
  disch_then drule_all >> strip_tac >> gvs[]
QED

Theorem augassign_attribute_frame[local]:
  !ref arr_e et bd p root xs env bt ty bop rhs cx es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    well_typed_target env bt ty /\ ~place_contains bt p /\
    target_writes_ok (\w. ~place_contains w p) bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) t.scopes =
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) s.scopes) /\
    eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule attribute_projection_and_length >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
  drule_all typed_target_attribute >> strip_tac >>
  gvs[IgnAsm `!s r t. _`] >>
  TRY (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _`
         (fn th => imp_res_tac th)) >>
  gvs[] >>
  rename1 `write_place cx dest value mid = (res,es')` >>
  `MAP (\sc. OPTION_MAP
     (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
     (FLOOKUP sc root)) es'.scopes =
   MAP (\sc. OPTION_MAP
     (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
     (FLOOKUP sc root)) mid.scopes` by
    (Cases_on `?path. dest = MemoryPlace root path`
     >- (gvs[] >> drule_all typed_memory_write_attribute_projection >> simp[]) >>
     `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
     drule_all write_guarded_place_projection >> strip_tac >>
     irule scope_projection_observe >> simp[]) >>
  gvs[]
QED

Theorem append_place_divergent_attrs[local]:
  !cx root xs ws tail v es res es'.
    ~isPREFIX xs ws /\ ~isPREFIX ws xs /\
    append_place cx (MemoryPlace root (MAP AttrSubscript ws ++ tail)) v es = (res,es') ==>
    LENGTH es'.scopes = LENGTH es.scopes /\
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[append_place_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  drule_all write_place_divergent_attrs >> simp[]
QED

Theorem append_attribute_frame[local]:
  !ref arr_e et bd p root xs env bt vt rhs cx es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    type_place_target env bt = SOME vt /\ ~place_contains bt p /\
    target_writes_ok (\w. ~place_contains w p) bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) t.scopes =
      MAP (\sc. OPTION_MAP
        (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
        (FLOOKUP sc root)) s.scopes) /\
    eval_stmt cx (Append bt rhs) es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule attribute_projection_and_length >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  imp_res_tac typed_target_attribute >>
  gvs[IgnAsm `!s r t. _`] >>
  TRY (qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _`
         (fn th => imp_res_tac th)) >>
  gvs[] >>
  rename1 `append_place cx dest value mid = (res,es')` >>
  `MAP (\sc. OPTION_MAP
     (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
     (FLOOKUP sc root)) es'.scopes =
   MAP (\sc. OPTION_MAP
     (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
     (FLOOKUP sc root)) mid.scopes` by
    (Cases_on `?path. dest = MemoryPlace root path`
     >- (gvs[] >> drule eval_target_place_attribute_prefix >> strip_tac >>
         gvs[] >> drule_all typed_attribute_writes_ok >> strip_tac >>
         `~isPREFIX xs' xs /\ ~isPREFIX xs xs'` by
           (first_x_assum irule >> metis_tac[]) >>
         drule_all append_place_divergent_attrs >> simp[]) >>
     `!r path. dest = MemoryPlace r path ==> r <> root` by metis_tac[] >>
     drule_all append_place_name_projection >> strip_tac >>
     irule scope_projection_observe >> simp[]) >>
  gvs[]
QED

Theorem finally_pop_scope_observation[local]:
  !f es res es' q.
    es.scopes <> [] /\ finally f pop_scope es = (res,es') /\
    (!r t. f es = (r,t) ==>
      MAP q t.scopes = MAP q es.scopes /\
      LENGTH t.scopes = LENGTH es.scopes) ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `f es` >> rename1 `f es = (outcome,after)` >> fs[] >>
  `MAP q (TL after.scopes) = MAP q (TL es.scopes)` by metis_tac[MAP_TL] >>
  Cases_on `after.scopes` >- gvs[] >>
  Cases_on `outcome` >>
  gvs[finally_def, pop_scope_def, ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem handled_loop_body_observation[local]:
  !cx body q es res es'.
    es.scopes <> [] /\
    (!r t. eval_stmts cx body es = (r,t) ==>
      MAP q t.scopes = MAP q es.scopes /\ LENGTH t.scopes = LENGTH es.scopes) /\
    try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception es =
      (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts es` >>
  Cases_on `eval_stmts cx stmts es` >>
  rename1 `eval_stmts cx stmts es = (outcome,after)` >> gvs[] >>
  Cases_on `outcome` >>
  gvs[try_def, ignore_bind_def, bind_def, return_def] >>
  rename1 `handle_loop_exception exc after = _` >>
  Cases_on `exc` >> gvs[handle_loop_exception_def, return_def, raise_def]
QED

Theorem balanced_loop_body_observation[local]:
  !cx stmts q es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    finally (try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception)
      pop_scope es = (res,es') ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:bool``] finally_pop_scope_observation) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception`,
            `res`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule handled_loop_body_observation >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem eval_for_observation_frame[local]:
  !vs cx tyv id body q es res es'.
    (!s r s'. s.scopes <> [] /\ eval_stmts cx body s = (r,s') ==>
      MAP q s'.scopes = MAP q s.scopes /\ LENGTH s'.scopes = LENGTH s.scopes) /\
    eval_for cx tyv id body vs es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  Induct_on `vs`
  >- simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `read_result cx h es` >>
  rename1 `read_result cx h es = (read_out,read_state)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `read_out`)
  >- (drule eval_for_cons_read_error >> disch_then (fn th => gvs[th])) >>
  drule eval_for_cons_read >> disch_then (fn th => fs[th]) >>
  qmatch_asmsub_abbrev_tac `finally action pop_scope` >>
  qpat_x_assum `ignore_bind _ _ es = _` mp_tac >>
  pure_rewrite_tac [push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  strip_tac >> FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  qmatch_asmsub_abbrev_tac `bind (finally action pop_scope) continuation pushed` >>
  Cases_on `finally action pop_scope pushed` >>
  rename1 `finally action pop_scope pushed = (outcome,after)` >> fs[Abbr `action`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_loop_body_observation >>
  disch_then (qspec_then `q` mp_tac) >>
  (impl_tac >- (simp[Abbr `pushed`] >> metis_tac[])) >> strip_tac >>
  fs[IgnAsm `!cx tyv id body q es res es'. _`, Abbr `pushed`] >>
  Cases_on `outcome` >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac [bind_def, pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  simp[Abbr `continuation`, return_def] >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` kall_tac
  >~ [`(if broke then _ else _) _ = _`]
  >- (Cases_on `broke`
      >- (qpat_x_assum `!cx tyv id body q es res es'. _` kall_tac >>
          gvs[return_def]) >>
      FULL_SIMP_TAC std_ss [] >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!cx tyv id body q es res es'. _` kall_tac >> gvs[]
QED

Theorem balanced_conditional_observation[local]:
  !cx tv ss1 ss2 q es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    finally (switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2))
      pop_scope es = (res,es') ==>
    MAP q es'.scopes = MAP q (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:unit``] finally_pop_scope_observation) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2)`,`res`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) es = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >> gvs[raise_def] >>
  first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem if_observation_frame[local]:
  !cx e ss1 ss2 q es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==> MAP q t.scopes = MAP q s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (If e ss1 ss2) es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       get_scopes_def, set_scopes_def, return_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> strip_tac >> imp_res_tac attribute_projection_length
  >~ [`v = INR exc`]
  >- gvs[IgnAsm `!s r t. _`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_conditional_observation >>
  disch_then (qspec_then `q` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem for_observation_frame[local]:
  !cx id typ it n stmts q es res es'.
    (!s r t. eval_iterator cx it s = (r,t) ==> MAP q t.scopes = MAP q s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP q t.scopes = MAP q s.scopes /\ LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (For id typ it n stmts) es = (res,es') ==>
    MAP q es'.scopes = MAP q es.scopes /\ LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  imp_res_tac vyperStatePreservationTheory.check_state >>
  gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_iterator _ _ _ = _ ==> _` drule >> strip_tac >>
  imp_res_tac attribute_projection_length
  >~ [`eval_for _ _ _ _ _ _ = _`]
  >- (drule_at (Pat `eval_for _ _ _ _ _ _ = _`) eval_for_observation_frame >>
      disch_then (qspec_then `q` mp_tac) >>
      (impl_tac >- metis_tac[]) >> simp[]) >>
  gvs[IgnAsm `!s r t. _`]
QED

Theorem typed_attribute_frames_mutual:
  (!env ret_ty stmt env' ref arr_e et bd p root xs cx es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM ref.var_types /\
    type_stmt env ret_ty stmt = SOME env' /\
    stmt_writes_ok (\w. ~place_contains w p) stmt /\
    es.scopes <> [] /\ eval_stmt cx stmt es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!env ret_ty stmts env' ref arr_e et bd p root xs cx es res es'.
    place_access p [] = (NameTarget root,xs) /\ loop_iterator_place arr_e = SOME p /\
    well_typed_expr ref arr_e /\ expr_type arr_e = ArrayT et bd /\
    env.type_defs = ref.type_defs /\
    FLOOKUP env.var_types root = FLOOKUP ref.var_types root /\
    root IN FDOM ref.var_types /\
    type_stmts env ret_ty stmts = SOME env' /\
    stmts_writes_ok (\w. ~place_contains w p) stmts /\
    es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es'.scopes =
    MAP (\sc. OPTION_MAP
      (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
      (FLOOKUP sc root)) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >~ [`eval_stmt _ Pass _ = _`]
  >- (qpat_x_assum `eval_stmt _ Pass _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ Break _ = _`]
  >- (qpat_x_assum `eval_stmt _ Break _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ Continue _ = _`]
  >- (qpat_x_assum `eval_stmt _ Continue _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Return NONE) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Return NONE) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Raise RaiseBare) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Raise RaiseBare) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Raise RaiseUnreachable) _ = _`]
  >- (qpat_x_assum `eval_stmt _ (Raise RaiseUnreachable) _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmts _ [] _ = _`]
  >- (qpat_x_assum `eval_stmts _ [] _ = _` mp_tac >>
      simp[Once evaluate_def, return_def, raise_def] >> rw[] >> simp[])
  >~ [`eval_stmt _ (Expr _) _ = _`] >- suspend "expr"
  >~ [`eval_stmt _ (Return (SOME _)) _ = _`] >- suspend "return"
  >~ [`eval_stmt _ (Raise (RaiseReason _)) _ = _`] >- suspend "raise_reason"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _)) _ = _`] >- suspend "raise_custom"
  >~ [`eval_stmt _ (Assert _ AssertBare) _ = _`] >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable) _ = _`]
  >- suspend "assert_unreachable"
  >~ [`eval_stmt _ (Assert _ (AssertReason _)) _ = _`] >- suspend "assert_reason"
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _)) _ = _`]
  >- suspend "assert_custom"
  >~ [`eval_stmt _ (Log _ _) _ = _`] >- suspend "log"
  >~ [`eval_stmt _ (AnnAssign _ _ _) _ = _`] >- suspend "annassign"
  >~ [`eval_stmt _ (Append _ _) _ = _`] >- suspend "append"
  >~ [`eval_stmt _ (Assign _ _) _ = _`] >- suspend "assign"
  >~ [`eval_stmt _ (AugAssign _ _ _ _) _ = _`] >- suspend "augassign"
  >~ [`eval_stmt _ (If _ _ _) _ = _`] >- suspend "if"
  >~ [`eval_stmt _ (For _ _ _ _ _) _ = _`] >- suspend "for"
  >~ [`eval_stmts _ (_::_) _ = _`] >- suspend "cons"
QED

Resume typed_attribute_frames_mutual[expr]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  drule_all typed_expr_attribute >> strip_tac >> gvs[] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[return]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  drule_all typed_expr_attribute >> strip_tac >> gvs[] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[raise_reason]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  drule_all typed_expr_attribute >> strip_tac >> gvs[] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[raise_custom]:
  rename1 `Raise (RaiseCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >> strip_tac >>
  gvs[] >> imp_res_tac vyperStatePreservationTheory.lift_option_state >>
  drule_all typed_custom_error_attribute >> strip_tac >> gvs[] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[assert_bare]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_attribute >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[assert_unreachable]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_attribute >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[assert_reason]:
  rename1 `Assert cond (AssertReason msg)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `(!s r t. eval_expr cx msg s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_attribute >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`, return_def, raise_def, COND_RATOR, bind_def,
      AllCaseEqs()] >>
  imp_res_tac read_result_state >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
  res_tac >> gvs[] >> metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[assert_custom]:
  rename1 `Assert cond (AssertCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_attribute >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, bind_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac vyperStatePreservationTheory.lift_option_state >> gvs[]
  >>~- ([`eval_exprs _ _ _ = _`],
        drule_all typed_custom_error_attribute >> strip_tac >>
        imp_res_tac attribute_projection_length >> gvs[]) >>
  imp_res_tac attribute_projection_length >> gvs[]
QED

Resume typed_attribute_frames_mutual[log]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_exprs_attribute >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.lift_option_state >>
  imp_res_tac vyperScopePreservationTheory.push_log_scopes >>
  gvs[] >> metis_tac[attribute_projection_length]
QED

Resume typed_attribute_frames_mutual[annassign]:
  rename1 `eval_stmt cx (AnnAssign id typ rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `id <> root` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  `(!s r t. eval_expr cx rhs s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  drule_all annassign_attribute_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[append]:
  rename1 `eval_stmt cx (Append bt rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `(!s r t. eval_expr cx rhs s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  drule_all append_attribute_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[assign]:
  rename1 `eval_stmt cx (Assign target rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  drule vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >>
  impl_tac >- simp[] >> strip_tac >>
  `(!s r t. eval_expr cx rhs s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  drule_all assign_attribute_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[augassign]:
  rename1 `eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `(!s r t. eval_expr cx rhs s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  drule_all augassign_attribute_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[if]:
  rename1 `eval_stmt cx (If e ss1 ss2) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  `(!s r t. eval_expr cx e s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_expr_attribute >> simp[]) >>
  `(!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes /\
       LENGTH t.scopes = LENGTH s.scopes)` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     disch_then (qspecl_then [`ref`,`arr_e`,`et`,`bd`,`p`,`root`,`xs`] mp_tac) >>
     simp[]) >>
  `(!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes /\
       LENGTH t.scopes = LENGTH s.scopes)` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     disch_then (qspecl_then [`ref`,`arr_e`,`et`,`bd`,`p`,`root`,`xs`] mp_tac) >>
     simp[]) >>
  drule_all if_observation_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[for]:
  rename1 `eval_stmt cx (For id typ it n stmts) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  `id <> root` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  `(extend_local env id typ F).type_defs = ref.type_defs /\
   FLOOKUP (extend_local env id typ F).var_types root =
     FLOOKUP ref.var_types root` by
    simp[extend_local_def, FLOOKUP_UPDATE] >>
  `(!s r t. eval_iterator cx it s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes)` by
    (rpt strip_tac >> drule_all typed_iterator_attribute >> simp[]) >>
  `(!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) t.scopes =
       MAP (\sc. OPTION_MAP
         (\e. (e.type, evaluate_subscripts e.type e.value (MAP AttrSubscript xs)))
         (FLOOKUP sc root)) s.scopes /\
       LENGTH t.scopes = LENGTH s.scopes)` by
    (rpt gen_tac >> strip_tac >>
     first_x_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     disch_then (qspecl_then [`ref`,`arr_e`,`et`,`bd`,`p`,`root`,`xs`] mp_tac) >>
     simp[]) >>
  drule_all for_observation_frame >> simp[]
QED

Resume typed_attribute_frames_mutual[cons]:
  rename1 `eval_stmts cx (s::ss) es = (res,es')` >>
  qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `stmts_writes_ok _ (_::_)` mp_tac >>
  simp[stmt_writes_ok_def] >> strip_tac >>
  drule_all type_stmt_reference_transport >> strip_tac >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac
  >~ [`eval_stmts _ ss _ = _`]
  >- (rename1 `eval_stmts cx ss mid = _` >>
      `mid.scopes <> []` by (Cases_on `mid.scopes` >> gvs[]) >>
      first_x_assum drule_all >> strip_tac >> gvs[]) >>
  gvs[]
QED

Finalise typed_attribute_frames_mutual

Theorem typed_stmts_place_frame:
  type_stmts env ret_ty stmts = SOME env' /\
  well_typed_expr env arr_e /\ expr_type arr_e = ArrayT et bd /\
  loop_iterator_place arr_e = SOME p /\ place_access p [] = (NameTarget root, attrs) /\
  root IN FDOM env.var_types /\
  stmts_writes_ok (\w. ~place_contains w p) stmts /\
  es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
  LENGTH es'.scopes = LENGTH es.scopes /\
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es'.scopes =
  MAP (\sc. OPTION_MAP
          (\e. (e.type, evaluate_subscripts e.type e.value
                           (MAP AttrSubscript attrs)))
          (FLOOKUP sc root)) es.scopes
Proof
  strip_tac >>
  qspecl_then [`env`,`ret_ty`,`stmts`,`env'`,`env`,`arr_e`,`et`,`bd`,`p`,`root`,
               `attrs`,`cx`,`es`,`res`,`es'`]
    mp_tac (cj 2 typed_attribute_frames_mutual) >>
  simp[]
QED

(* A projection of one name's entries that two scope lists agree on
   gives the same projection of its lookup. *)
Theorem scope_projection_lookup_map:
  !a b n f.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) b ==>
    OPTION_MAP f (lookup_scopes n a) = OPTION_MAP f (lookup_scopes n b)
Proof
  Induct >- (Cases >> simp[lookup_scopes_def]) >>
  rpt gen_tac >> Cases_on `b` >> simp[lookup_scopes_def] >> strip_tac >>
  Cases_on `FLOOKUP h n` >> Cases_on `FLOOKUP h' n` >> gvs[]
QED

(* The same, for a name bound below the top scope. *)
Theorem scope_projection_lookup_below:
  !a sc0 rest0 n f e.
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) a =
    MAP (\sc. OPTION_MAP f (FLOOKUP sc n)) (sc0 :: rest0) /\
    n NOTIN FDOM sc0 /\ lookup_scopes n rest0 = SOME e ==>
    ?sc rest e'. a = sc :: rest /\ lookup_scopes n rest = SOME e' /\
      lookup_scopes n a = SOME e' /\ f e' = f e
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >> gvs[] >>
  `FLOOKUP sc0 n = NONE` by gvs[flookup_thm] >>
  `FLOOKUP h n = NONE` by gvs[] >>
  drule scope_projection_lookup_map >> simp[] >>
  Cases_on `lookup_scopes n t` >> simp[lookup_scopes_def]
QED

(* A path read that succeeds reads its prefix. *)
Theorem evaluate_subscripts_append_prefix:
  !p tv a sfx r.
    evaluate_subscripts tv a (p ++ sfx) = INL r ==>
    ?x. evaluate_subscripts tv a p = INL x
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED

(* Two values with the same sub-value at a path read the same below it:
   the types a read passes through depend on the path alone. *)
Theorem sum_case_id[local]:
  !X. (case X of INL vj => INL vj | INR err => INR err) = X
Proof
  Cases >> simp[]
QED

Theorem evaluate_subscripts_prefix_agree:
  !p tv a b sfx x.
    evaluate_subscripts tv a p = INL x /\
    evaluate_subscripts tv b p = INL x ==>
    evaluate_subscripts tv a (p ++ sfx) = evaluate_subscripts tv b (p ++ sfx)
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (Cases_on `v` >> simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def] >>
      Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
      rpt strip_tac >>
      Cases_on `array_index tv a i` >> Cases_on `array_index tv a' i` >>
      gvs[] >> metis_tac[]) >>
  Cases_on `a` >> simp[evaluate_subscripts_def] >>
  Cases_on `b` >> simp[evaluate_subscripts_def, sum_case_id] >>
  rpt strip_tac >> BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

Theorem memory_iterator_source_current_path:
  !e cx es ee target root path.
    loop_iterator_place e = SOME target /\
    target_root target = NameTarget root /\
    expr_writes_ok (\_. F) e /\
    eval_expr cx e es = (INL (PlaceR (MemoryPlace root path)), ee) ==>
    ?entry value.
      lookup_scopes root ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL value
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[loop_iterator_place_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[target_root_def, Once evaluate_def, expr_writes_ok_def,
      bind_def, ignore_bind_def, get_scopes_def, type_check_def,
      check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >- (Cases_on `lookup_scopes root ee.scopes` >>
      gvs[evaluate_subscripts_def]) >>
  drule exprSimPropsTheory.select_result_memory_place >>
  disch_then (qspecl_then [`root`, `path`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >~ [`select_result cx (expr_type obj) _ (AttrSubscript fld) mid = _`]
  >- (rename1 `eval_expr cx obj es =
                 (INL (PlaceR (MemoryPlace root prior)), mid)` >>
      qpat_x_assum `!cx' es' ee' path'. _`
        (qspecl_then [`cx`, `es`, `mid`, `prior`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[select_result_def, extend_place_def, place_type_value_def,
          read_place_def, get_scopes_def, bind_def, ignore_bind_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def,
          read_memory_path_def, AllCaseEqs()] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
      drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
      simp[] >> metis_tac[]) >>
  rename1 `subscript_reads_base cx obj index` >>
  Cases_on `subscript_reads_base cx obj index` >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `eval_expr cx obj es =
    (INL (PlaceR (MemoryPlace root prior)), base_end)` >>
  rename1 `eval_expr cx index base_end = (INL idx, index_end)` >>
  qpat_x_assum `!cx' es' ee' path'. _`
    (qspecl_then [`cx`, `es`, `base_end`, `prior`] mp_tac) >>
  simp[] >> strip_tac >>
  qspecl_then
    [`\(c:evaluation_context) (s:evaluation_state). OPTION_MAP (\entry. (entry.type,entry.value))
                (lookup_scopes root s.scopes)`, `\w. F`]
    mp_tac eval_observation_frame_mutual >> simp[] >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspecl_then [`cx`, `index`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`base_end`, `INL idx`, `index_end`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `lookup_scopes root index_end.scopes` >> gvs[] >>
  gvs[select_result_def, extend_place_def, place_type_value_def,
      read_place_def, get_scopes_def, bind_def, ignore_bind_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def,
      read_memory_path_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  simp[] >> metis_tac[]
QED

Theorem memory_iterator_place_observation:
  vv_post ctx func cenv cx e es sa sb s0 mid
    (PlaceR (MemoryPlace name path)) vv t /\
  post_value_type cenv e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  read_result cx (PlaceR (MemoryPlace name path)) mid = (INL (ArrayV av),mid) /\
  vv_location vv = SOME LocMemory /\
  eval_operand (vv_operand vv) t = SOME array_base /\
  local_ptrs_reserved cenv sb /\
  (!ei. P ei ==> expr_sim_inv cenv cx env ei /\
    ?entry. lookup_scopes name ei.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) ==>
  !ei s. P ei /\ stmt_state_rel ctx func cenv cx ei s /\
    array_caller_frame sb t s /\ alloca_frame cenv mid sb t cenv ei s ==>
    val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n array_base) s.vs_memory
Proof
  strip_tac >>
  `vv_holds cenv cx (ArrayT et bd) (PlaceR (MemoryPlace name path)) vv mid t /\
   vv_at cenv cx (ArrayT et bd) sa sb mid
     (PlaceR (MemoryPlace name path)) vv t` by fs[vv_post_def] >>
  `val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n array_base) t.vs_memory` by
    (qpat_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `vv_location vv = SOME LocMemory` mp_tac >>
     qpat_assum `eval_operand (vv_operand vv) t = SOME array_base` mp_tac >>
     qpat_assum `read_result cx (PlaceR (MemoryPlace name path)) _ = _` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) (ArrayT et bd) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `vv` >>
     simp[vv_holds_def, vv_location_def, vv_operand_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `val_wf (ArrayTV tv bd) (ArrayV av) /\
   ((?aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\
      aid < sb.cs_next_id /\ off <= w2n array_base /\
      w2n array_base + val_footprint (ArrayTV tv bd) (ArrayV av) <= off + sz /\
      (!name b size. local_region cenv mid.scopes t name b size ==>
        off + sz <= b \/ b + size <= off)) \/
    (?off sz t0 tv0. local_region cenv mid.scopes t name off sz /\
      off <= w2n array_base /\ cenv.ce_var_type name = SOME t0 /\
      evaluate_type (get_tenv cx) t0 = SOME tv0 /\
      mem_path_offset tv0 path = SOME (w2n array_base - off, ArrayTV tv bd)) \/
    val_footprint (ArrayTV tv bd) (ArrayV av) = 0)` ASSUME_TAC
  >- (qpat_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_assum `vv_location vv = SOME LocMemory` mp_tac >>
      qpat_assum `eval_operand (vv_operand vv) t = SOME array_base` mp_tac >>
      qpat_assum `read_result cx (PlaceR (MemoryPlace name path)) _ = _` mp_tac >>
      qpat_assum `evaluate_type (get_tenv cx) (ArrayT et bd) = _` mp_tac >>
      rpt (pop_assum kall_tac) >> Cases_on `vv` >>
      simp[vv_at_def, vv_location_def, vv_operand_def] >> rpt strip_tac >>
      gvs[local_place_at_def] >> metis_tac[]) >>
  suspend "frames"
QED

Resume memory_iterator_place_observation[frames]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `val_wf _ _ /\ _` (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qpat_x_assum `(?aid off sz. FLOOKUP t.vs_allocas aid = SOME (off,sz) /\ _) \/ _`
    strip_assume_tac
  >- (qpat_assum `alloca_frame cenv mid sb t cenv ei s` mp_tac >>
      qpat_assum `FLOOKUP t.vs_allocas aid = SOME (off,sz)` mp_tac >>
      qpat_assum `aid < sb.cs_next_id` mp_tac >>
      qpat_assum `off <= w2n array_base` mp_tac >>
      qpat_assum `w2n array_base + val_footprint (ArrayTV tv bd) (ArrayV av) <= off + sz`
        mp_tac >>
      qpat_assum `!name b size. local_region cenv mid.scopes t name b size ==> _` mp_tac >>
      qpat_assum `val_wf (ArrayTV tv bd) (ArrayV av)` mp_tac >>
      qpat_assum `val_in_memory (ArrayTV tv bd) (ArrayV av)
        (w2n array_base) t.vs_memory` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz t.vs_memory` by
        (qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
           (mp_tac o Q.SPECL [`aid`, `off`, `sz`] o
            REWRITE_RULE [alloca_frame_def]) >> simp[] >> metis_tac[]) >>
      `mem_bytes_at (w2n array_base) (val_footprint (ArrayTV tv bd) (ArrayV av))
          t.vs_memory =
       mem_bytes_at (w2n array_base) (val_footprint (ArrayTV tv bd) (ArrayV av))
          s.vs_memory` by
        (qpat_assum `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz t.vs_memory`
           (mp_tac o Q.SPECL [`w2n (array_base:bytes32)`,
              `val_footprint (ArrayTV tv bd) (ArrayV av)`] o CONJUNCT1 o
            MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
         simp[arithmeticTheory.ADD_COMM]) >>
      irule exprSimPropsTheory.val_in_memory_footprint_agree >>
      simp[] >> qexists_tac `t.vs_memory` >> simp[])
  >- suspend "local" >>
  irule exprSimPropsTheory.val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `t.vs_memory` >> simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Resume memory_iterator_place_observation[local]:
  `expr_sim_inv cenv cx env ei /\
   ?live_entry. lookup_scopes name ei.scopes = SOME live_entry /\
     evaluate_subscripts live_entry.type live_entry.value path = INL (ArrayV av)` by
    metis_tac[] >>
  `?old_entry dp w. lookup_scopes name mid.scopes = SOME old_entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var dp) sz) /\
    lookup_var dp t = SOME w /\ off = w2n w` by fs[local_region_def] >>
  `not_fresh_at sb dp` by metis_tac[local_ptrs_reserved_def] >>
  `lookup_var dp s = SOME w` by
    metis_tac[stmtSimForArrayLoopTheory.array_caller_frame_def] >>
  `?decl_ty. FLOOKUP env.var_types name = SOME decl_ty /\
    evaluate_type (get_tenv cx) decl_ty = SOME live_entry.type /\
    cenv.ce_var_type name = SOME decl_ty` by
    (qpat_assum `expr_sim_inv cenv cx env ei` mp_tac >>
     qpat_assum `lookup_scopes name ei.scopes = SOME live_entry` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     rpt strip_tac >>
     `IS_SOME (FLOOKUP env.var_types name)` by metis_tac[] >>
     Cases_on `FLOOKUP env.var_types name` >> gvs[] >> metis_tac[]) >>
  `live_entry.type = tv0` by
    (qpat_assum `cenv.ce_var_type name = SOME t0` mp_tac >>
     qpat_assum `cenv.ce_var_type name = SOME decl_ty` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) t0 = SOME tv0` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) decl_ty = SOME live_entry.type` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `value_has_type live_entry.type live_entry.value /\ well_formed_type_value live_entry.type` by
    (qpat_assum `expr_sim_inv cenv cx env ei` mp_tac >>
     qpat_assum `lookup_scopes name ei.scopes = SOME live_entry` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_sim_inv_def, state_well_typed_def] >> rpt strip_tac >>
     metis_tac[vyperTypeStatePreservationTheory.lookup_scopes_well_typed_value_has_type,
       vyperPlaceTypingTheory.lookup_scopes_well_typed_type]) >>
  `local_ptrs_rel func cenv ei.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [local_ptrs_rel_def]) >>
  disch_then (qspecl_then [`name`, `live_entry`, `dp`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  `val_in_memory live_entry.type live_entry.value off s.vs_memory` by
    metis_tac[memoryValueEncodingTheory.memory_value_rel_val_in_memory] >>
  mp_tac (Q.SPECL [`path`, `live_entry.type`, `live_entry.value`,
    `w2n (array_base:bytes32) - off`, `ArrayTV tv bd`, `ArrayV av`,
    `off`, `s.vs_memory`] imm_typed_path_memory) >>
  simp[] >> `off + (w2n array_base - off) = w2n array_base` by decide_tac >> gvs[]
QED
Finalise memory_iterator_place_observation

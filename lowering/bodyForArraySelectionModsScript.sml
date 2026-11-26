(* Reached Array iterator selection, before any length or item instructions. *)
Theory bodyForArraySelectionMods
Ancestors
  bodyForArrayRouteMods bodyFullForArray whitelistForIter
  bodyInvCodeProps exprBodyPreProps exprBodyPreTypingProps
  exprBodyPreCallSafetyProps vyperTypeEvalStoragePreservation
  vyperStoragePlaceProvenance vyperBareGlobalName
  loweringPosts vyperTypeSystem vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeValues vyperState vyperInterpreter vyperAST targetPlaceSim list
  compileEnv bodyFullPostsMods context exprSimHypsDefs bodyPtrDefs vyperTyping
  vyperPlaceTyping exprSimProps reasonSourceProps forNestedArrayCapture
  vyperValue exprSimAttribute vyperTypeEvalSoundness
  vyperTypeContract[qualified,ignore_grammar]
Libs
  monadsyntax

Theorem array_selection_type[local]:
  expr_body_pre_mods mods c cx env e start /\
  well_typed_iterator env ty (Array e) /\ expr_type e = ArrayT ty bd /\
  eval_expr cx e start = (INL raw,em) ==>
  ?et. evaluate_type (get_tenv cx) ty = SOME et /\
       evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
       post_value_type c e = ArrayT ty bd /\
       eval_result_typed (env,cx,em) raw (Type (ArrayT ty bd))
Proof
  strip_tac >>
  `post_value_type c e = expr_type e` by
    (irule post_value_type_not_int_call >> rpt strip_tac >>
     fs[well_typed_iterator_def, call_result_expr_def]) >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def,env_consistent_def,env_context_consistent_def] >>
  qpat_assum `eval_result_typed _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [eval_result_typed_def]) >>
  rename1 `evaluate_type env.type_defs (expr_type e) = SOME tv` >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME tv` by
    (qpat_x_assum `evaluate_type env.type_defs _ = SOME tv` mp_tac >> simp[]) >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  qexists_tac `elem_tv` >> simp[] >>
  qpat_x_assum `eval_result_typed _ _ _` mp_tac >> simp[]
QED

Theorem array_select_immutable_pre[local]:
  select_result cx ty raw sb s = (INL (PlaceR (ImmutablePlace src id path)),t) ==>
  ?pre. raw = PlaceR (ImmutablePlace src id pre) /\ path = pre ++ [sb]
Proof
  Cases_on `raw` >>
  simp[select_result_def,bind_def,lift_option_type_def,lift_sum_def,
       return_def,raise_def,AllCaseEqs()] >> strip_tac >>
  drule extend_place_immutable_root >> simp[]
QED

Theorem array_subscript_select_step[local]:
  eval_expr cx (Subscript ann obj idx) es = (INL r,ee) ==>
  ?base mid raw v u. eval_expr cx obj es = (INL base,mid) /\
    (raw = base \/ (?w. raw = Value w)) /\
    select_result cx (expr_type obj) raw (ValueSubscript v) u = (INL r,ee)
Proof
  simp[Once evaluate_def,bind_def,AllCaseEqs()] >> rpt strip_tac >>
  qpat_x_assum `(if subscript_reads_base _ _ _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def,return_def,AllCaseEqs()] >> metis_tac[]
QED

Theorem array_iterator_global_code[local]:
  !e tgt key cx es r ee.
    loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget key /\
    eval_expr cx e es = (INL r,ee) ==>
    ?tops. get_module_code cx (FST key) = SOME tops
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def,target_root_def,AllCaseEqs()] >>
  rpt strip_tac
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rename1 `TopLevelName ann key` >> PairCases_on `key` >>
      Cases_on `get_module_code cx key0` >> simp[] >>
      fs[Once evaluate_def,Once lookup_global_def,bind_def,lift_option_type_def,
         raise_def])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (gvs[Once evaluate_def,bind_def,AllCaseEqs()] >>
      qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
      first_x_assum (qspec_then `obj` mp_tac) >> fs[expr_size_def,target_root_def] >>
      metis_tac[])
  >> drule array_subscript_select_step >> strip_tac >> gvs[target_root_def] >>
  qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
  first_x_assum (qspec_then `obj` mp_tac) >> fs[expr_size_def,target_root_def] >>
  metis_tac[]
QED

(* The static attributes stop at the first index. The remaining path is the
   one captured by this run, including the actual index value. *)
Theorem array_immutable_selection_path[local]:
  !e tgt cx es src id path em.
    loop_iterator_place e = SOME tgt /\
    eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),em) ==>
    ?attrs tail. target_root tgt = TopLevelNameTarget (src,id) /\
      path = MAP AttrSubscript attrs ++ tail /\
      (tail = [] \/ ?ix rest. tail = ValueSubscript ix :: rest) /\
      !extra. place_access tgt extra =
        (TopLevelNameTarget (src,id), if tail = [] then attrs ++ extra else attrs)
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[vyperTypeContractTheory.loop_iterator_place_def, AllCaseEqs()] >>
  rpt strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- gvs[Once evaluate_def,bind_def,ignore_bind_def,type_check_def,check_def,
         assert_def,raise_def,return_def,AllCaseEqs()]
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rename1 `TopLevelName ann key` >> PairCases_on `key` >>
      gvs[Once evaluate_def] >> drule lookup_global_immutable_root >> strip_tac >>
      qexistsl [`[]`,`[]`] >> simp[place_access_def,target_root_def])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (gvs[Once evaluate_def,bind_def,AllCaseEqs()] >>
      drule array_select_immutable_pre >> strip_tac >> gvs[] >>
      qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
      first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
      disch_then drule_all >> strip_tac >> gvs[] >>
      rename1 `target_root (AttributeTarget sub attr)`
      >- (qexistsl [`attrs ++ [attr]`,`[]`] >>
          simp[place_access_def, target_root_def, MAP_APPEND, APPEND_ASSOC]) >>
      qexistsl [`attrs`,`ValueSubscript ix :: (rest ++ [AttrSubscript attr])`] >>
      simp[place_access_def, target_root_def, APPEND_ASSOC]) >>
  drule array_subscript_select_step >> strip_tac >>
  drule array_select_immutable_pre >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `eval_expr _ obj _` >>
  first_x_assum (qspec_then `obj` mp_tac) >> simp[expr_size_def] >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `ValueSubscript ixnew :: []`
  >- (qexistsl [`attrs`,`[ValueSubscript ixnew]`] >> simp[place_access_def,target_root_def]) >>
  qexistsl [`attrs`,`ValueSubscript ix :: (rest ++ [ValueSubscript ixnew])`] >>
  simp[place_access_def,target_root_def,APPEND_ASSOC]
QED

Theorem array_selection_attr_prefix[local]:
  !attrs tv a tail av.
    evaluate_subscripts tv a (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
    (tail = [] \/ ?ix rest. tail = ValueSubscript ix :: rest) ==>
    ?pav. evaluate_subscripts tv a (MAP AttrSubscript attrs) = INL (ArrayV pav)
Proof
  Induct >> rpt gen_tac
  >- (simp[] >> rpt strip_tac
      >- gvs[evaluate_subscripts_def] >>
      Cases_on `ix` >> Cases_on `a` >> gvs[evaluate_subscripts_def]) >>
  Cases_on `a` >> simp[Once evaluate_subscripts_def] >> rpt strip_tac >>
  gvs[Once evaluate_subscripts_def,AllCaseEqs()] >> metis_tac[]
QED

Theorem array_selection_global_target[local]:
  expr_writes_ok (\_. F) e /\ eval_expr cx e start = (INL raw,em) /\
  (!v. raw <> Value v) /\ (!id path. raw <> PlaceR (MemoryPlace id path)) ==>
  ?tgt src name. loop_iterator_place e = SOME tgt /\
                 target_root tgt = TopLevelNameTarget (src,name)
Proof
  strip_tac >> CCONTR_TAC >> fs[] >>
  `!tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
    (rpt strip_tac >> PairCases_on `nid` >> metis_tac[]) >>
  drule_all_then strip_assume_tac memory_iterator_source_classify >> gvs[]
QED

Theorem array_selection_storage_root[local]:
  get_module_code cx src = SOME tops /\
  eval_expr cx (TopLevelName ann (src,name)) start =
    (INL (PlaceR (StoragePlace tr w tv)),em) ==>
  ?ty key off. find_var_decl_by_name name tops = SOME (StorageVarDecl tr ty,key) /\
    lookup_var_slot_from_layout cx tr src key = SOME off /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ w = n2w off /\
    MEM (StorageRoot tr off tv) em.storage_trace
Proof
  simp[Once evaluate_def,Once lookup_global_def,bind_def,lift_option_type_def,
       vyperMiscTheory.option_CASE_rator] >> strip_tac >>
  Cases_on `find_var_decl_by_name name tops`
  >- gvs[bind_def,return_def,raise_def,AllCaseEqs()] >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_def,ignore_bind_def,record_storage_event_def,lift_option_type_def,
      return_def,raise_def,AllCaseEqs(),MEM_APPEND] >>
  Cases_on `lookup_var_slot_from_layout cx b src x1` >>
  gvs[return_def,raise_def] >> Cases_on `evaluate_type (get_tenv cx) t` >>
  gvs[return_def,raise_def]
QED

Theorem array_selection_pre_gas_obs[local,simp]:
  expr_body_pre_mods mods c cx env e (es with gas_obs := obs) <=>
  expr_body_pre_mods mods c cx env e es
Proof
  simp[expr_body_pre_mods_def,expr_sim_inv_mods_def]
QED

(* Separate the machine operand from the syntactic root and the runtime
   result. In particular the Value arm also covers copied global selections. *)
Theorem for_array_reached_selection_mods:
  contract_inv mods exps ctx c cx /\
  expr_body_pre_mods mods c cx env e es /\
  well_typed_iterator env ty (Array e) /\ expr_type e = ArrayT ty bd /\
  em.gas_obs = [] /\
  (!tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
          (INL raw,em with gas_obs := tail)) /\
  vv_post_mods H ctx func c cx e es sa sb s0 em raw vv s /\
  ptr_vv_ok cx (post_value_type c e) raw vv em G tn s /\
  (!v. raw = Value v /\ ~is_word_type (post_value_type c e) /\
       ~is_bytestring_type (post_value_type c e) ==>
       vv_own c cx (post_value_type c e) sa sb em raw vv s /\
       (!ann p. vv = LocatedValue ann p ==> p.ptr_location = LocMemory)) ==>
  ?et. evaluate_type (get_tenv cx) ty = SOME et /\
    evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV et bd) /\
    post_value_type c e = ArrayT ty bd /\
    ((?tr slot p tgt src name tops.
        raw = PlaceR (StoragePlace tr slot (ArrayTV et bd)) /\
        vv = LocatedValue (ArrayT ty bd) p /\
        p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot /\
        op_taint tn p.ptr_operand = {} /\
        loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget (src,name) /\
        ALOOKUP mods src = SOME tops /\
        (e = TopLevelName (ArrayT ty bd) (src,name) ==>
         ?rt key off. find_var_decl_by_name name tops = SOME (StorageVarDecl tr rt,key) /\
           lookup_var_slot_from_layout cx tr src key = SOME off /\
           evaluate_type (get_tenv cx) rt = SOME (ArrayTV et bd) /\
           slot = n2w off /\ MEM (StorageRoot tr off (ArrayTV et bd)) em.storage_trace)) \/
     (?src name path tgt attrs tail tops off rt root delta av pav p.
        raw = PlaceR (ImmutablePlace src name path) /\
        vv = LocatedValue (ArrayT ty bd) p /\ p.ptr_location = LocCode /\
        ALOOKUP mods src = SOME tops /\
        FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
        lookup_immutable cx em src name = SOME (rt,root) /\
        mem_path_offset rt path = SOME (delta,ArrayTV et bd) /\
        eval_operand p.ptr_operand s = SOME (n2w (off + delta)) /\
        loop_iterator_place e = SOME tgt /\ place_access tgt [] = (TopLevelNameTarget (src,name),attrs) /\
        path = MAP AttrSubscript attrs ++ tail /\
        evaluate_subscripts rt root (MAP AttrSubscript attrs) = INL (ArrayV pav) /\
        evaluate_subscripts rt root path = INL (ArrayV av)) \/
     (?id path p tgt attrs tail.
        raw = PlaceR (MemoryPlace id path) /\
        vv = LocatedValue (ArrayT ty bd) p /\ p.ptr_location = LocMemory /\
        MEM tgt (expr_places e) /\ place_access tgt [] = (NameTarget id,attrs) /\
        path = MAP AttrSubscript attrs ++ tail) \/
     (?av. raw = Value (ArrayV av) /\ value_has_type (ArrayTV et bd) (ArrayV av) /\
           vv_own c cx (ArrayT ty bd) sa sb em raw vv s /\
           (vv_location vv = NONE \/ vv_location vv = SOME LocMemory)))
Proof
  strip_tac >> qabbrev_tac `start = es with gas_obs := obs` >>
  `em with gas_obs := [] = em` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e start = (INL raw,em)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[Abbr `start`]) >>
  `expr_body_pre_mods mods c cx env e start` by simp[Abbr `start`] >>
  drule_all_then strip_assume_tac array_selection_type >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  `~is_word_type (post_value_type c e) /\ ~is_bytestring_type (post_value_type c e)` by
    simp[is_word_type_def,is_bytestring_type_def] >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by
    (qpat_assum `post_value_type _ _ = _` (fn eq =>
       qpat_assum `evaluate_type _ (post_value_type _ _) = _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qexists_tac `et` >> asm_rewrite_tac [] >>
  `expr_writes_ok (\_. F) e` by fs[well_typed_iterator_def] >>
  Cases_on `raw`
  >- suspend "value"
  >- (rename1 `PlaceR pl` >> Cases_on `pl`
      >- suspend "slot"
      >- suspend "memory" >> suspend "immutable") >>
  fs[eval_result_typed_def]
QED

Resume for_array_reached_selection_mods[value]:
  rename1 `eval_result_typed _ (Value v) _` >>
  `value_has_type (ArrayTV et bd) v` by
    fs[eval_result_typed_def] >>
  `?av. v = ArrayV av` by (Cases_on `v` >> gvs[value_has_type_inv]) >>
  gvs[] >>
  Cases_on `vv` >> simp[vv_location_def]
QED

Resume for_array_reached_selection_mods[slot]:
  rename1 `eval_result_typed _ (PlaceR (StoragePlace tr slot tv)) _` >>
  `tv = ArrayTV et bd` by
    fs[eval_result_typed_def,runtime_place_typed_def,place_type_value_def,return_def,
       evaluate_type_def] >>
  pop_assum SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac for_array_slot_operand_mods >>
  `?tgt src name. loop_iterator_place e = SOME tgt /\
                  target_root tgt = TopLevelNameTarget (src,name)` by
    (irule array_selection_global_target >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all_then strip_assume_tac array_iterator_global_code >>
  `get_module_code cx src = SOME tops` by fs[] >>
  drule_then (qspec_then `src` assume_tac) contract_inv_module_codes >>
  `ALOOKUP mods src = SOME tops` by fs[] >>
  disj1_tac >> qexistsl [`tr`,`slot`,`p`,`tgt`,`src`,`name`,`tops`] >> simp[] >>
  disch_tac >> qpat_x_assum `e = TopLevelName _ _` SUBST_ALL_TAC >>
  drule_all_then ACCEPT_TAC array_selection_storage_root
QED

Resume for_array_reached_selection_mods[memory]:
  rename1 `eval_result_typed _ (PlaceR (MemoryPlace id path)) _` >>
  drule_all eval_iterator_memory_place_access >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  disj2_tac >> disj2_tac >> disj1_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  Cases_on `vv` >> gvs[vv_at_def,vv_place_ptr_mods_def,vv_place_ptr_def,vv_holds_mods_def] >>
  rename1 `p.ptr_location = LocMemory` >> gvs[vv_holds_def,is_bytestring_type_def] >>
  qexistsl [`target`,`attrs`] >> simp[]
QED

Resume for_array_reached_selection_mods[immutable]:
  rename1 `eval_result_typed _ (PlaceR (ImmutablePlace src name path)) _` >>
  drule_all_then strip_assume_tac for_array_immutable_operand_mods >>
  `?tgt. loop_iterator_place e = SOME tgt` by
    (qpat_assum `eval_expr _ _ start = _`
       (mp_then (Pat `eval_expr`) mp_tac array_selection_global_target) >>
     simp[] >> strip_tac >> goal_assum (drule_at Any)) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `subscripts_type itv path = SOME (ArrayTV et bd)` by
    (Cases_on `ALOOKUP em.immutables cx.txn.target` >>
     gvs[eval_result_typed_def,runtime_place_typed_immutable,
         lookup_immutable_def,get_immutables_def,get_address_immutables_def,
         bind_def,lift_option_type_def,return_def,raise_def]) >>
  `tv = ArrayTV et bd` by (drule mem_path_offset_sound >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  `?v. read_result cx (PlaceR (ImmutablePlace src name path)) em = (INL v,em)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
     fs[vv_holds_mods_def,immutable_holds_mods_def] >>
     qpat_assum `p.ptr_location = LocCode` (fn h =>
       qpat_x_assum `(if p.ptr_location = LocCode then _ else _)`
         (strip_assume_tac o REWRITE_RULE [h])) >>
     drule immutable_holds_read >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) start = (INL v,em)` by simp[bind_def] >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  qpat_assum `bind _ _ _ = _`
    (mp_then Any mp_tac (REWRITE_RULE [ETA_THM] eval_expr_read_type_sound)) >>
  disch_then (qspec_then `env` mp_tac) >> fs[runtime_consistent_def] >> strip_tac >>
  `value_has_type (ArrayTV et bd) v` by gvs[value_runtime_typed_def] >>
  `?av. v = ArrayV av` by (Cases_on `v` >> fs[value_has_type_inv]) >>
  `evaluate_subscripts itv iv path = INL (ArrayV av)` by
    gvs[read_result_immutable_place] >>
  drule_all_then
    (qx_choosel_then [`attrs`,`tail`] (map_every assume_tac o CONJUNCTS))
    array_immutable_selection_path >>
  `?pav. evaluate_subscripts itv iv (MAP AttrSubscript attrs) = INL (ArrayV pav)` by
    (irule array_selection_attr_prefix >> qexistsl [`av`,`tail`] >> gvs[]) >>
  qexistsl [`attrs`,`tail`,`delta`,`av`,`pav`] >>
  qpat_assum `!extra. place_access _ extra = _` (qspec_then `[]` mp_tac) >>
  gvs[]
QED

Finalise for_array_reached_selection_mods

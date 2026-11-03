(* Compiler boundary for subscript assignment places. *)
Theory targetSubscriptSim
Ancestors
  targetPlaceSim exprNoPopScopes exprLowering emitHelper compileEnv
  vyperAST pair exprSimOps exprSim exprLoweringProps loweringShapeDefs fragExec
  vyperState vyperInterpreter vyperStorageBackend exprSimHyps vyperTypeSystem
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  exprSimAggregateEncoding tupleMemoryLayout exprSimAttributeFields
  vyperTyping valueEncoding arithmetic vyperValueOperation valueEncodingProofs list
  vyperPlaceStatePreservation vyperPlaceTyping vyperTypeStatePreservation
  words finite_map option exprSimArrayIndex valueEncodingProps accountsRelProps
  venomState venomMemDefs
Libs
  pairLib

Theorem stmt_state_rel_sstore_dead_right:
  !ctx func cenv cx es s k v.
    stmt_state_rel ctx func cenv cx es s /\
    s.vs_call_ctx.cc_address = cx.txn.target /\
    (!b. b < 32 ==> storage_dead cx F
      (lookup_account cx.txn.target es.accounts).storage (w2n k) b) ==>
    stmt_state_rel ctx func cenv cx es (sstore k v s)
Proof
  rpt strip_tac >>
  `accounts_rel cx es (sstore k v s)` by
    (irule accounts_rel_sstore_dead_right >>
     gvs[stmt_state_rel_def, state_rel_def]) >>
  `storage_rel cx cx.txn.target es (sstore k v s) /\
   transient_rel cx cx.txn.target es (sstore k v s)` by
    (drule accounts_rel_storage_transient >> simp[sstore_def]) >>
  gvs[stmt_state_rel_def, state_rel_def, sstore_def,
      local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
      immutables_rel_def, logs_rel_def, alloca_inv_def, alloca_room_def,
      pending_alloca_size_def, immutable_alloca_sep_def,
      allocas_non_overlapping_def, alloca_next_valid_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem expr_post_sstore_dead_right:
  !ctx func cenv cx e es sa sb s0 es' val op s k v.
    expr_post ctx func cenv cx e es sa sb s0 es' val op s /\
    s.vs_call_ctx.cc_address = cx.txn.target /\
    (!b. b < 32 ==> storage_dead cx F
      (lookup_account cx.txn.target es'.accounts).storage (w2n k) b) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' val op (sstore k v s)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es' (sstore k v s)` by
    (irule stmt_state_rel_sstore_dead_right >> gvs[expr_post_def]) >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      locals_kept_def, local_region_def, lookup_var_def,
      eval_operand_def, sstore_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED


Theorem vv_holds_sstore:
  !cenv cx t tv vv es s k v.
    vv_holds cenv cx t tv vv es (sstore k v s) =
    vv_holds cenv cx t tv vv es s
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[vv_holds_def, expr_val_rel_def, local_place_at_def,
       eval_operand_def, lookup_var_def, sstore_def]
QED

Theorem vv_post_sstore_dead_right:
  !ctx func cenv cx e es sa sb s0 es' tv vv s k v.
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv s /\
    s.vs_call_ctx.cc_address = cx.txn.target /\
    (!b. b < 32 ==> storage_dead cx F
      (lookup_account cx.txn.target es'.accounts).storage (w2n k) b) ==>
    vv_post ctx func cenv cx e es sa sb s0 es' tv vv (sstore k v s)
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es' (sstore k v s)` by
    (irule stmt_state_rel_sstore_dead_right >> gvs[vv_post_def]) >>
  gvs[vv_post_def, vv_holds_sstore] >>
  Cases_on `vv` >>
  gvs[vv_at_def, expr_val_at_def, locals_kept_def,
      local_region_def, lookup_var_def, eval_operand_def, sstore_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
(* Current representation follows a typed field offset, independently of
   the compiler's syntactic field-layout table. *)
Theorem fields_in_memory_mem_field_offset:
  !vals fs off mem id fv k ftv.
    struct_has_type fs vals /\ fields_in_memory vals fs off mem /\
    ALOOKUP vals id = SOME fv /\ mem_field_offset fs id = SOME (k,ftv) ==>
    val_in_memory ftv fv (off + k) mem
Proof
  Induct >> Cases_on `fs` >> simp[value_has_type_def] >>
  PairCases_on `h` >> Cases >>
  rename1 `struct_has_type ((fname,fty)::fts) ((vname,vval)::vrest)` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `fname = id` >> gvs[AllCaseEqs()] >>
  rename1 `mem_field_offset fts id = SOME child_offset` >>
  PairCases_on `child_offset` >> gvs[] >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem array_index_in_memory:
  !tv av off mem i v k etv.
    value_has_type tv (ArrayV av) /\
    val_in_memory tv (ArrayV av) off mem /\
    array_index tv av i = SOME v /\
    mem_step_offset tv (ValueSubscript (IntV i)) = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `av` >>
  gvs[value_has_type_def] >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  simp[val_in_memory_def, array_index_def, mem_step_offset_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[oEL_THM, AllCaseEqs()]
  >- (drule values_have_types_length >> strip_tac >>
      drule_all tuple_in_memory_element >> simp[GSYM type_memory_size_list_sum])
  >- (drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem mem_step_offset_current_value:
  !tv a sb v off mem k etv.
    value_has_type tv a /\ val_in_memory tv a off mem /\
    evaluate_subscripts tv a [sb] = INL v /\
    mem_step_offset tv sb = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      rpt strip_tac >> drule_all array_index_in_memory >> simp[]) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[evaluate_subscripts_def, mem_step_offset_def, value_has_type_def,
       val_in_memory_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all fields_in_memory_mem_field_offset >> simp[]
QED

(* Unlike read_memory_path, this boundary requires a live path, so a
   historical popped value cannot be mistaken for current memory. *)
Theorem mem_path_offset_current_value:
  !path tv a v off mem k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\
    evaluate_subscripts tv a path = INL v /\
    mem_path_offset tv path = SOME (k,ptv) ==>
    val_in_memory ptv v (off + k) mem
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rename1 `mem_step_offset tv sb = SOME (delta,etv)` >>
  `mem_path_offset tv [sb] = SOME (delta,etv)` by
    simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `a`] assume_tac) >>
  qpat_x_assum `evaluate_subscripts tv a (sb::path) = INL v` mp_tac >>
  once_asm_rewrite_tac[] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `evaluate_subscripts tv a [sb] = INL child` >>
  `value_has_type etv child` by
    (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
     simp[subscripts_type_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  drule_all mem_step_offset_current_value >> strip_tac >>
  first_x_assum drule_all >> simp[NoAsms, AC ADD_ASSOC ADD_COMM]
QED

Theorem place_ptr_rel_memory_current:
  !ctx func cenv cx env es s id path entry v w loc ty tv.
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    val_in_memory tv v (w2n w) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[IS_SOME_EXISTS]) >>
  `cenv.ce_var_type id = SOME ety /\
   evaluate_type (get_tenv cx) ety = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[lookup_scopes_well_typed_value_has_type, lookup_scopes_well_typed_type]) >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  qpat_x_assum `!name entry p sz. _ ==> _` drule_all >> strip_tac >> gvs[] >>
  drule_all mem_path_offset_current_value >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  drule alloca_room_next_lt >> strip_tac >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `k < dimword (:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, LESS_MOD] >> fs[ADD_COMM]
QED

Theorem array_len_ok_memory_current:
  !ctx func cenv cx env es s id path entry vs w loc ty etv cap ptr cnt.
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
    evaluate_type (get_tenv cx) ty = SOME (ArrayTV etv (Dynamic cap)) /\
    eval_operand ptr s = SOME w ==>
    array_len_ok T cnt
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory)
      ptr s (n2w (LENGTH vs))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all place_ptr_rel_memory_current >>
  simp[val_in_memory_def] >> strip_tac >>
  drule array_len_ok_MLOAD >>
  disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
  simp[GSYM mem_word_at_eq_mload]
QED

Theorem compile_get_target_ptr_subscript:
  !cfn cenv bt idx sa r sb.
    compile_get_target_ptr cfn cenv (SubscriptTarget bt idx) sa = (r,sb) ==>
    ?rb sm ix sn.
      compile_get_target_ptr cfn cenv bt sa = (rb,sm) /\
      lower_value cfn cenv (expr_type idx) idx sm = (ix,sn) /\
      (case SND (SND rb) of
         SOME (MapPT kt vt) =>
           ?kh sk dst.
             (if is_bytestring_type kt then compile_keccak256_key ix F
              else comp_return ix) sn = (kh,sk) /\
             compile_mapping_subscript (FST rb) kh sk = (dst,sb) /\
             r = (dst,FST (SND rb),SOME (value_type_place vt))
       | _ =>
           let loc = case FST (SND rb) of SOME l => l | NONE => LocMemory in
           let dyn = case SND (SND rb) of
                       SOME (ValPT (ArrayT _ (Dynamic _))) => T | _ => F in
           let ety = case SND (SND rb) of
                       SOME (ValPT (ArrayT t _)) => t | _ => BaseT (UintT 256) in
           let count = case SND (SND rb) of
                       SOME (ValPT (ArrayT _ (Fixed n))) => n | _ => 0 in
           ?dst.
             compile_array_subscript (FST rb) ix dyn count (word_scale loc)
               (elem_size_in_location cenv loc ety) (is_signed_type (expr_type idx))
               (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) sn = (dst,sb) /\
             r = (dst,FST (SND rb),SOME (ValPT ety)))
Proof
  rpt gen_tac >>
  simp[Once compile_get_target_ptr_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_get_target_ptr cfn cenv bt sa = (rb,sm)` >>
  Cases_on `SND (SND rb)`
  >- (gvs[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  rename1 `SND (SND rb) = SOME pt` >> Cases_on `pt` >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED

(* The index keeps the captured base pointer and composes its memory frame. *)
Theorem target_post_index_frame:
  !ctx func cenv cx es sa sm sn s0 es1 es2 pv vt rb t e v ix u.
    target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
    expr_post ctx func cenv cx e es1 sm sn t es2 v ix u /\
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    es2.scopes = es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
    target_post ctx func cenv cx es sa sn s0 es2 pv vt rb u
Proof
  rpt gen_tac >> simp[target_post_def, expr_post_def] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  simp[] >> rpt conj_tac
  >- (qexists_tac `w` >> conj_tac
      >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
      irule place_ptr_rel_vars_frame >> qexistsl_tac [`t`, `sm`] >> simp[]) 
  >- (irule place_readable_scopes_frame >> qexists_tac `es1` >> simp[])
  >- (rpt strip_tac >>
      `local_ptrs_rel func cenv es.scopes s0` by
        fs[stmt_state_rel_def, state_rel_def] >>
      `!n b sz'. local_region cenv es1.scopes t n b sz' ==>
                  off + sz <= b \/ b + sz' <= off` by
        (rpt strip_tac >>
         qpat_x_assum `!n b sz'. local_region cenv es.scopes s0 _ _ _ ==> _` irule >>
         qexists_tac `n` >> irule local_region_frame >>
         conj_tac >- (qexists_tac `func` >> simp[]) >>
         qexistsl_tac [`sa`, `es1.scopes`, `t`] >> simp[]) >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `aid < sm.cs_next_id` by decide_tac >>
      metis_tac[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >> simp[]
QED

Theorem target_index_frag:
  !ctx func cenv cx es sa sm sn s0 es1 es2 pv vt rb t e v ix.
    target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
    expr_sim ctx func cenv cx (expr_type e) e es1 /\
    lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
    (do raw <- eval_expr cx e; read_result cx raw od) es1 = (INL v,es2) /\
    fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    es2.scopes = es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
    frag_exec ctx sm sn (\s. s = t)
      (\s. target_post ctx func cenv cx es sa sn s0 es2 pv vt rb s /\
           expr_post ctx func cenv cx e es1 sm sn t es2 v ix s)
      (expr_exit (INL v : value + exception))
Proof
  rpt strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`, `sn`, `ix`, `INL v`, `es2`, `t`] mp_tac) >>
  simp[expr_res_ok_def] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[target_post_def] >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >>
  simp[] >> rpt strip_tac >>
  drule_all target_post_index_frame >> simp[]
QED

Theorem target_base_index_prefix:
  !ctx func cenv cx es sa sm sn s0 es1 es2 pv vt rb e v ix.
    frag_exec ctx sa sm
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. target_post ctx func cenv cx es sa sm s0 es1 pv vt rb s)
      (expr_exit (INL v : value + exception)) /\
    expr_sim ctx func cenv cx (expr_type e) e es1 /\
    lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
    (do raw <- eval_expr cx e; read_result cx raw od) es1 = (INL v,es2) /\
    fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\ es2.scopes = es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) /\
    cs_extends sa sm /\ cs_extends sm sn ==>
    frag_exec ctx sa sn
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. target_post ctx func cenv cx es sa sn s0 es2 pv vt rb s /\
           ?t. expr_post ctx func cenv cx e es1 sm sn t es2 v ix s)
      (expr_exit (INL v : value + exception))
Proof
  rpt strip_tac >>
  qpat_assum `frag_exec _ sa sm _ _ _` (mp_then Any irule frag_exec_then) >>
  simp[] >> rpt strip_tac >>
  drule_all target_index_frag >> strip_tac >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >>
  simp[] >> metis_tac[]
QED

(* An exceptional index exits before either pointer suffix is reached. *)
Theorem target_index_exception_frag:
  !ctx func cenv cx es sm sn ix exc es2 t.
    expr_sim ctx func cenv cx (expr_type ix) ix es /\
    lower_value compile_expr cenv (expr_type ix) ix sm = (t,sn) /\
    (do raw <- eval_expr cx ix; read_result cx raw od) es = (INR exc,es2) /\
    expr_res_ok (INR exc : value + exception) /\
    fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm ==>
    frag_exec ctx sm sn (stmt_state_rel ctx func cenv cx es)
      (\s. F) (expr_exit (INR exc : value + exception))
Proof
  rpt strip_tac >> irule frag_exec_pointwise >> rpt strip_tac >>
  rename1 `stmt_state_rel ctx func cenv cx es s0` >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE std_ss [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`, `sn`, `t`, `INR exc`, `es2`, `s0`] mp_tac) >>
  simp[] >> strip_tac >>
  irule frag_exec_conseq >> first_assum (irule_at Any) >> simp[]
QED

(* Exact source bounds classification; the dynamic length is read now. *)
Theorem extend_place_storage_array_index:
  !cx tr slot et bd i es.
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
      (ValueSubscript (IntV i)) es =
    (case bd of
       Fixed n =>
         if 0 <= i /\ Num i < n then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array fixed oob")), es)
     | Dynamic n =>
         if ~(0 <= i /\ Num i < n) then
           (INR (Error (RuntimeError "array dynamic capacity oob")), es)
         else if Num i < w2n (lookup_storage slot (get_storage cx es tr)) then
           (INL (PlaceR (StoragePlace tr
             (slot + n2w (1 + Num i * type_slot_size et)) et)), es)
         else (INR (Error (RuntimeError "array dynamic length oob")), es))
Proof
  rpt gen_tac >> Cases_on `et` >> Cases_on `bd` >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def,
       raise_def, get_storage_backend_eq, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[return_def, raise_def, bind_def, ignore_bind_def]
QED

(* Diagnostic: the unchanged index consumer supplies constructor typing. *)
Theorem target_mapping_index_typing_probe[local]:
  !cenv cx env bt e es es' kv kt vt outvt.
    expr_body_pre cenv cx env e es /\
    type_place_target env bt = SOME (HashMapT kt vt) /\
    type_place_target env (SubscriptTarget bt e) = SOME outvt /\
    (do raw <- eval_expr cx e; read_result cx raw od) es = (INL kv,es') ==>
    expr_type e = kt /\ hashmap_key_type kt /\
    ?tv. evaluate_type env.type_defs kt = SOME tv /\ value_has_type tv kv
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_body_pre_eval >> strip_tac >>
  gvs[Once well_typed_expr_def, subscript_vtype_def, AllCaseEqs()] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED

Theorem extend_place_memory_live:
  !cx id path sb es es' entry v pv.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    extend_place cx (PlaceR (MemoryPlace id path)) sb es = (INL pv,es') ==>
    es' = es /\ pv = PlaceR (MemoryPlace id (path ++ [sb])) /\
    ?w. evaluate_subscripts entry.type entry.value (path ++ [sb]) = INL w
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, read_memory_path_def,
       extend_memory_place_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `subscripts_type entry.type path` >>
  gvs[return_def, raise_def] >>
  rename1 `subscripts_type entry.type path = SOME ptv` >>
  Cases_on `evaluate_subscripts ptv v [sb]` >>
  gvs[return_def, raise_def] >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` mp_tac) >> simp[]
QED

Theorem extend_place_memory_input[local]:
  !cx pv sb es es' id path.
    extend_place cx pv sb es = (INL (PlaceR (MemoryPlace id path)),es') ==>
    ?prefix. pv = PlaceR (MemoryPlace id prefix)
Proof
  rpt gen_tac >> Cases_on `pv` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  all_tac >~ [`?prefix. p = MemoryPlace id prefix`]
  >- (Cases_on `p` >>
      gvs[bind_def, ignore_bind_def, return_def, extend_memory_place_def,
          AllCaseEqs()] >>
      rename1 `extend_storage_place cx tr slot tv sb _ = _` >>
      Cases_on `sb`
      >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
          gvs[extend_storage_place_def, raise_def, bind_def, ignore_bind_def,
              return_def, lift_option_type_def, AllCaseEqs()] >>
          rpt (pairarg_tac >> gvs[return_def]) >>
          gvs[return_def, AllCaseEqs()]) >>
      Cases_on `tv` >>
      gvs[extend_storage_place_def, raise_def, bind_def, ignore_bind_def,
          return_def, lift_option_type_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[return_def]) >>
          gvs[return_def, AllCaseEqs()]) >>
  Cases_on `sb` >> gvs[raise_def] >>
  pop_assum mp_tac >>
  simp[value_type_CASE_rator, bind_def, lift_option_type_def,
       return_def, raise_def, AllCaseEqs()]
QED

Theorem eval_base_place_memory_live:
  !bt cx es es1 id path.
    ~target_has_pop bt /\
    eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),es1) ==>
    ?entry v. lookup_scopes id es1.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, check_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
      gvs[optionTheory.IS_SOME_EXISTS] >>
      simp[evaluate_subscripts_def])
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_global_def, bind_def,
           lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          var_decl_info_CASE_rator, bind_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()])
  >- (rename1 `SubscriptTarget bt idx` >>
      simp[target_has_pop_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      drule extend_place_memory_input >> strip_tac >> gvs[] >>
      `~target_has_pop bt /\ ~expr_has_pop idx` by
        gvs[target_has_pop_def, expr_has_pop_def,
            supportedExprTraverseTheory.supported_expr_exists_def] >>
      drule_all eval_expr_nopop_scopes >> strip_tac >>
      drule read_result_state >> strip_tac >> gvs[] >>
      first_x_assum (qspec_then `bt` mp_tac) >>
      simp[expr_size_def] >>
      disch_then drule_all >> strip_tac >>
      drule_at (Pat `extend_place _ _ _ _ = _`) extend_place_memory_live >>
      simp[] >> disch_then drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `AttributeTarget bt fld` >>
  simp[target_has_pop_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule extend_place_memory_input >> strip_tac >> gvs[] >>
  `~target_has_pop bt` by
    gvs[target_has_pop_def, supportedExprTraverseTheory.supported_expr_exists_def] >>
  first_x_assum (qspec_then `bt` mp_tac) >> simp[expr_size_def] >>
  disch_then drule_all >> strip_tac >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem eval_base_place_memory_live_scopes_frame:
  !bt cx es es1 es2 id path.
    ~target_has_pop bt /\
    eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),es1) /\
    es2.scopes = es1.scopes ==>
    ?entry v. lookup_scopes id es2.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt strip_tac >> drule_all eval_base_place_memory_live >> simp[]
QED

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
  venomState venomMemDefs vyperArith integer integer_word exprNoEffectStorage
  exprSimMappingHash stmtLoweringMono
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
    val_in_memory tv v (w2n w) s.vs_memory /\
    value_has_type tv v /\ well_formed_type_value tv /\
    subscripts_type entry.type path = SOME tv
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
  simp[w2n_add_2, w2n_n2w, LESS_MOD] >> fs[ADD_COMM] >>
  conj_tac
  >- (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all subscripts_type_well_formed >> simp[]
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

(* Intermediate code states are monotone before the semantic suffix is known. *)
Theorem compile_get_target_ptr_subscript_mono:
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_compile_expr_sa, SND] >>
  simp[] >>
  drule compile_get_target_ptr_subscript >> strip_tac >> gvs[] >>
  qpat_x_assum `case SND (SND rb) of NONE => _ | SOME _ => _` mp_tac >>
  Cases_on `SND (SND rb)` >> simp[]
  >- (strip_tac >> gvs[] >>
      metis_tac[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load, SND]) >>
  rename1 `SND (SND rb) = SOME pt` >> reverse (Cases_on `pt`) >> simp[]
  >- (rpt strip_tac >> gvs[] >>
      metis_tac[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load, SND]) >>
  rpt strip_tac >> rename1 `SND (SND rb) = SOME (MapPT kt mvt)` >>
  `ci_mono sk sb` by metis_tac[ci_mono_compile_mapping_subscript, SND] >>
  `ci_mono sn sk` by
    (Cases_on `is_bytestring_type kt` >> gvs[comp_return_def, ci_mono_refl] >>
     metis_tac[ci_mono_compile_keccak256_key, SND]) >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
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

(* Scalar integer representation, as used by expr_val_rel/vv_holds. *)
Theorem idx_in_range_typed_int:
  !bt bits i iw n.
    (bt = IntT bits \/ bt = UintT bits) /\ bits <= 256 /\
    value_has_type (BaseTV bt) (IntV i) /\
    iw = typed_val_to_w256 (BaseTV bt) (IntV i) /\
    n < dimword (:256) ==>
    (idx_in_range (is_signed_type (BaseT bt)) iw (n2w n) <=>
     0 <= i /\ Num i < n)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[typed_val_to_w256_def, val_to_w256_def, is_signed_type_def,
      value_has_type_def]
  >- (`w2i (i2w i : bytes32) = i` by
        (irule w2i_i2w_within_signed >> qexists_tac `bits` >> simp[]) >>
      Cases_on `i < 0`
      >- simp[idx_in_range_def, WORD_LTi, word_0_w2i,
              INT_NOT_LE, w2n_n2w] >>
      gvs[idx_in_range_def, WORD_LTi, word_0_w2i, w2n_n2w] >>
      `~word_msb (i2w i : bytes32)` by simp[word_msb_neg, GSYM w2i_lt_0] >>
      gvs[w2i_def] >>
      `Num i = w2n (i2w i : bytes32)` by metis_tac[NUM_OF_INT] >>
      simp[GSYM INT_NOT_LT]) >>
  `Num i < dimword (:256)` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** bits` >>
     simp[dimword_def]) >>
  `i = &Num i` by simp[INT_OF_NUM] >>
  pop_assum SUBST1_TAC >>
  simp[idx_in_range_def, i2w_pos, w2n_n2w]
QED

Theorem array_bounds_capacity:
  !i len cap.
    len <= cap ==>
    ((0 <= i /\ Num i < len) <=>
     ((0 <= i /\ Num i < cap) /\ Num i < len))
Proof
  rpt strip_tac >> eq_tac >> simp[]
QED

(* A read-only pointer suffix keeps the complete target frame, not just
   the state relation.  The new place itself is supplied by the source step. *)
Theorem target_post_suffix_frame:
  !ctx func cenv cx es sa sm sb s0 es' pv vt rb t u pv' vt' dst loc.
    target_post ctx func cenv cx es sa sm s0 es' pv vt rb t /\
    sa.cs_next_var <= sm.cs_next_var /\
    stmt_state_rel ctx func cenv cx es' u /\
    (?w. eval_operand dst u = SOME w /\
         place_ptr_rel cenv cx u pv' w loc vt') /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    place_readable cx es' pv' /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    target_post ctx func cenv cx es sa sb s0 es' pv' vt'
      (dst,loc,SOME (value_type_place vt')) u
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es s0 u` by
    (irule locals_kept_mem_tail >> qexists_tac `t` >>
     gvs[target_post_def]) >>
  gvs[target_post_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

(* Memory address extension depends on the declared layout, not on the
   current value; bounds and current readability are established separately. *)
Theorem place_ptr_rel_memory_step:
  !cenv cx s id path w loc ty tv sb k ety etv.
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    mem_step_offset tv sb = SOME (k,etv) /\
    evaluate_type (get_tenv cx) ety = SOME etv ==>
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id (path ++ [sb])))
      (w + n2w k) loc (Type ety)
Proof
  rpt gen_tac >> simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  simp[place_ptr_rel_def, AC WORD_ADD_ASSOC WORD_ADD_COMM,
       word_add_n2w, ADD_COMM]
QED

Theorem extend_place_memory_live_result:
  !cx id path sb es entry v tv.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    subscripts_type entry.type path = SOME tv ==>
    extend_place cx (PlaceR (MemoryPlace id path)) sb es =
      (case evaluate_subscripts tv v [sb] of
       | INL w => (INL (PlaceR (MemoryPlace id (path ++ [sb]))),es)
       | INR err => (INR (Error err),es))
Proof
  rpt strip_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, read_memory_path_def,
       extend_memory_place_def] >>
  Cases_on `evaluate_subscripts tv v [sb]` >>
  simp[lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem place_readable_memory_live:
  !cx es id path entry v.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v ==>
    place_readable cx es (PlaceR (MemoryPlace id path))
Proof
  rpt strip_tac >>
  simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, read_memory_path_def]
QED

(* Success half of the memory suffix: assemble the source live-path step,
   declared address offset, and machine read-only frame at one boundary. *)
Theorem target_post_memory_step:
  !ctx func cenv cx es sa sm sb s0 es2 es3 id path ty tv
   rb t u entry v sub k ety etv dst w pv'.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (MemoryPlace id path)) (Type ty) rb t /\
    lookup_scopes id es2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    extend_place cx (PlaceR (MemoryPlace id path)) sub es2 = (INL pv',es3) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    mem_step_offset tv sub = SOME (k,etv) /\
    evaluate_type (get_tenv cx) ety = SOME etv /\
    eval_operand (FST rb) t = SOME w /\
    eval_operand dst u = SOME (w + n2w k) /\
    stmt_state_rel ctx func cenv cx es2 u /\
    local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    (!x z. not_fresh_at sm x /\ lookup_var x t = SOME z ==>
           lookup_var x u = SOME z) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    target_post ctx func cenv cx es sa sb s0 es3 pv' (Type ety)
      (dst,SOME LocMemory,SOME (ValPT ety)) u
Proof
  rpt gen_tac >> strip_tac >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type ty)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  `place_ptr_rel cenv cx t
     (PlaceR (MemoryPlace id (path ++ [sub]))) (w + n2w k)
     (SOME LocMemory) (Type ety)` by
    (irule place_ptr_rel_memory_step >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `place_ptr_rel cenv cx u
     (PlaceR (MemoryPlace id (path ++ [sub]))) (w + n2w k)
     (SOME LocMemory) (Type ety)` by
    (irule place_ptr_rel_vars_frame >> qexistsl_tac [`t`, `sm`] >>
     gvs[target_post_def]) >>
  once_rewrite_tac[GSYM value_type_place_def] >>
  drule_then irule target_post_suffix_frame >> simp[] >>
  irule place_readable_memory_live >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extend_place_memory_array_index:
  !cx id path es entry et bd av i.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    subscripts_type entry.type path = SOME (ArrayTV et bd) /\
    value_has_type (ArrayTV et bd) (ArrayV av) ==>
    extend_place cx (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) es =
    (if 0 <= i /\ Num i < array_length (ArrayTV et bd) av
     then (INL (PlaceR (MemoryPlace id
                  (path ++ [ValueSubscript (IntV i)]))),es)
     else (INR (Error (RuntimeError "evaluate_subscripts array_index")),es))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all extend_place_memory_live_result >>
  disch_then (qspecl_then [`cx`, `ValueSubscript (IntV i)`] mp_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, evaluate_subscripts_def, array_length_def,
      array_index_def, oEL_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  qmatch_goalsub_rename_tac `ALOOKUP sparse (Num i)` >>
  Cases_on `ALOOKUP sparse (Num i)` >> gvs[]
QED

Theorem evaluate_type_array_bound_word:
  !tenv et bd tv.
    evaluate_type tenv (ArrayT et bd) = SOME tv ==>
    bound_length bd < dimword (:256)
Proof
  rpt gen_tac >>
  simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename1 `0 < type_slot_size etv` >>
  irule LESS_EQ_LESS_TRANS >>
  qexists_tac `bound_length bd * type_slot_size etv` >>
  reverse conj_tac >- simp[] >>
  Cases_on `bd` >>
  gvs[vyperValueTheory.type_slot_size_def, bound_length_def]
QED

Theorem target_memory_array_static_suffix:
  !ctx func cenv cx es sa sm sb s0 es2 es3 id path et n etv
    rb t entry av ix iw i bt bits dst w res.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (MemoryPlace id path)) (Type (ArrayT et (Fixed n))) rb t /\
    lookup_scopes id es2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    subscripts_type entry.type path = SOME (ArrayTV etv (Fixed n)) /\
    value_has_type (ArrayTV etv (Fixed n)) (ArrayV av) /\
    evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) =
      SOME (ArrayTV etv (Fixed n)) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    (bt = IntT bits \/ bt = UintT bits) /\ bits <= 256 /\
    value_has_type (BaseTV bt) (IntV i) /\
    iw = typed_val_to_w256 (BaseTV bt) (IntV i) /\
    compile_array_subscript (FST rb) ix F n 32 (type_memory_size etv)
      (is_signed_type (BaseT bt))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
    eval_operand (FST rb) t = SOME w /\ eval_operand ix t = SOME iw /\
    (!x. ix = Var x ==> not_fresh_at sm x) /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    extend_place cx (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) es2 = (res,es3) ==>
    frag_exec ctx sm sb
      (\s. s = t /\ stmt_state_rel ctx func cenv cx es2 s)
      (\s. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 es3 pv' (Type et)
          (dst,SOME LocMemory,SOME (ValPT et)) s)
      (expr_exit res)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword (:256)` by
    (drule evaluate_type_array_bound_word >> simp[bound_length_def]) >>
  `(idx_in_range (is_signed_type (BaseT bt)) iw (n2w n) <=>
    0 <= i /\ Num i < n)` by
    (irule idx_in_range_typed_int >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `bits` >> simp[]) >>
  drule_all extend_place_memory_array_index >> strip_tac >>
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[value_has_type_def, array_length_def]) >>
  Cases_on `0 <= i /\ Num i < n` >> gnvs[]
  >- suspend "success" >>
  suspend "oob"
QED

Resume target_memory_array_static_suffix[success]:
  RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  rename1 `target_post ctx func cenv cx es sa sm s0 live_es _ _ rb t` >>
  `!x. FST rb = Var x ==> not_fresh_at sm x` by gvs[target_post_def] >>
  `typed_val_to_w256 (BaseTV bt) (IntV i) = n2w (Num i)` by
    (`i = &Num i` by simp[INT_OF_NUM] >>
     pop_assum SUBST1_TAC >>
     gvs[typed_val_to_w256_def, val_to_w256_def, i2w_pos]) >>
  drule_all compile_array_static_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `live_es`] mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[expr_exit_def] >> rpt strip_tac >>
  drule_then irule target_post_memory_step >>
  simp[word_mul_n2w] >>
  qexistsl_tac [`Num i * type_memory_size etv`, `ValueSubscript (IntV i)`] >>
  simp[mem_step_offset_def]
QED

Resume target_memory_array_static_suffix[oob]:
  drule_all compile_array_static_frag_oob >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es3`] mp_tac) >>
  disch_then (qspec_then `\s. F` mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> gvs[expr_exit_def]
QED

Finalise target_memory_array_static_suffix

(* Audit boundary only: provenance does not rule out this discrepancy.
   Reachability of its premises after an actual base evaluation is separate. *)
Theorem storage_array_capacity_length_discrepancy[local]:
  !cx tr slot et cap i es ms.
    0 <= i /\ cap <= Num i /\
    Num i < w2n (lookup_storage slot (get_storage cx es tr)) ==>
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et (Dynamic cap))))
      (ValueSubscript (IntV i)) es =
      (INR (Error (RuntimeError "array dynamic capacity oob")),es) /\
    idx_in_range F (n2w (Num i))
      (lookup_storage slot (get_storage cx es tr)) /\
    ~expr_exit (INR (Error (RuntimeError "array dynamic capacity oob"))) (OK ms)
Proof
  rpt gen_tac >> strip_tac >>
  `Num i < dimword (:256)` by
    (irule LESS_TRANS >> goal_assum (drule_at Any) >> simp[w2n_lt]) >>
  simp[extend_place_storage_array_index, idx_in_range_def, expr_exit_def,
       w2n_n2w, LESS_MOD]
QED

(* A live captured header is observable through the post-index state relation.
   Liveness is an explicit premise, not a consequence of target_post. *)
Theorem stmt_state_rel_storage_live_head:
  !ctx func cenv cx es s tr slot tv.
    stmt_state_rel ctx func cenv cx es s /\
    storage_read_live cx tr (get_storage cx es tr) slot tv /\
    0 < type_slot_size tv ==>
    (if tr then tload slot s else sload slot s) =
      lookup_storage slot (get_storage cx es tr)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
     (get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
         vyperStorageBackendTheory.get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  drule_all storage_agree_read_head >> strip_tac >>
  Cases_on `tr` >> gvs[sload_def, tload_def]
QED

Theorem target_index_storage_live_head:
  !ctx func cenv cx e es1 res es2 s tr slot tv.
    ~expr_has_effect e /\
    (do raw <- eval_expr cx e; read_result cx raw od) es1 = (res,es2) /\
    stmt_state_rel ctx func cenv cx es2 s /\
    storage_read_live cx tr (get_storage cx es1 tr) slot tv /\
    0 < type_slot_size tv ==>
    (if tr then tload slot s else sload slot s) =
      lookup_storage slot (get_storage cx es2 tr)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all eval_expr_read_noeffect_storage >>
  disch_then (qspec_then `tr` assume_tac) >>
  irule stmt_state_rel_storage_live_head >>
  conj_tac
  >- (qexists_tac `tv` >> simp[]) >>
  goal_assum (drule_at Any)
QED

(* Current local memory, rather than the declared capacity, supplies the
   runtime bound for a dynamic target. *)
Theorem target_memory_array_suffix:
  !ctx func cenv cx env es sa sm sb s0 es2 es3 id path et bd etv
    rb t entry av ix iw i bt bits dst w res.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (MemoryPlace id path)) (Type (ArrayT et bd)) rb t /\
    expr_sim_inv cenv cx env es2 /\
    stmt_state_rel ctx func cenv cx es2 t /\
    lookup_scopes id es2.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
    subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    (bt = IntT bits \/ bt = UintT bits) /\ bits <= 256 /\
    value_has_type (BaseTV bt) (IntV i) /\
    iw = typed_val_to_w256 (BaseTV bt) (IntV i) /\
    compile_array_subscript (FST rb) ix ((case bd of Fixed _ => F | Dynamic _ => T))
      (if (case bd of Fixed _ => F | Dynamic _ => T) then 0 else bound_length bd) 32 (type_memory_size etv)
      (is_signed_type (BaseT bt))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
    eval_operand (FST rb) t = SOME w /\ eval_operand ix t = SOME iw /\
    (!x. ix = Var x ==> not_fresh_at sm x) /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    extend_place cx (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) es2 = (res,es3) ==>
    frag_exec ctx sm sb
      (\s. s = t /\ stmt_state_rel ctx func cenv cx es2 s)
      (\s. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 es3 pv' (Type et)
          (dst,SOME LocMemory,SOME (ValPT et)) s)
      (expr_exit res)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bd`
  >- (gnvs[bound_length_def] >>
      irule target_memory_array_static_suffix >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexists_tac `bits` >> simp[] >>
      qexistsl_tac [`bt`, `rb`, `w`] >> simp[]) >>
  gnvs[bound_length_def] >>
  rename1 `ArrayT et (Dynamic cap)` >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) w
     (FST (SND rb)) (Type (ArrayT et (Dynamic cap)))` by
    gvs[target_post_def] >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  Cases_on `av` >> gnvs[value_has_type_def] >>
  rename1 `ArrayV (DynArrayV vs)` >>
  `mload (w2n w) t = n2w (LENGTH vs)` by
    gvs[val_in_memory_def, mem_word_at_eq_mload] >>
  `cap < dimword (:256)` by
    (drule evaluate_type_array_bound_word >> simp[bound_length_def]) >>
  `(idx_in_range (is_signed_type (BaseT bt))
      (typed_val_to_w256 (BaseTV bt) (IntV i)) (n2w (LENGTH vs)) <=>
      0 <= i /\ Num i < LENGTH vs)` by
    (irule idx_in_range_typed_int >> simp[] >>
     qexists_tac `bits` >> simp[]) >>
  `extend_place cx (PlaceR (MemoryPlace id path))
     (ValueSubscript (IntV i)) es2 =
     (if 0 <= i /\ Num i < LENGTH vs then
        (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),es2)
      else (INR (Error (RuntimeError "evaluate_subscripts array_index")),es2))` by
    (drule extend_place_memory_array_index >>
     disch_then (qspecl_then [`cx`, `path`] mp_tac) >>
     disch_then drule >> disch_then drule >>
     simp[value_has_type_def, array_length_def] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sm x` by gvs[target_post_def] >>
  drule compile_array_dynamic_outcome >>
  simp[] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es2`] mp_tac) >>
  simp[] >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[] >> conj_tac
  >- suspend "dynamic_success" >>
  suspend "dynamic_exit"
QED

Resume target_memory_array_suffix[dynamic_success]:
  rpt strip_tac >> gnvs[] >> RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  `typed_val_to_w256 (BaseTV bt) (IntV i) = n2w (Num i)` by
    (`i = &Num i` by simp[INT_OF_NUM] >>
     pop_assum SUBST1_TAC >>
     gvs[typed_val_to_w256_def, val_to_w256_def, i2w_pos]) >>
  drule_then irule target_post_memory_step >>
  simp[word_mul_n2w, word_add_n2w, WORD_ADD_ASSOC] >>
  qexistsl_tac [`32 + Num i * type_memory_size etv`, `ValueSubscript (IntV i)`] >>
  simp[mem_step_offset_def] >>
  simp[GSYM word_add_n2w, AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Resume target_memory_array_suffix[dynamic_exit]:
  rpt strip_tac >> gvs[expr_exit_def]
QED

Finalise target_memory_array_suffix

(* Scratch allocation need not preserve all memory: the original allocation
   windows and caller-local windows are the target judgment's frame. *)
Theorem target_post_regions_suffix_frame:
  !ctx func cenv cx es sa sm sb s0 es' pv vt rb t u pv' vt' dst loc.
    target_post ctx func cenv cx es sa sm s0 es' pv vt rb t /\
    sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    stmt_state_rel ctx func cenv cx es' u /\
    (?w. eval_operand dst u = SOME w /\
         place_ptr_rel cenv cx u pv' w loc vt') /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    place_readable cx es' pv' /\
    (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
           lookup_var x u = SOME w) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory) /\
    (!n b len. local_region cenv es'.scopes t n b len ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory) ==>
    target_post ctx func cenv cx es sa sb s0 es' pv' vt'
      (dst,loc,SOME (value_type_place vt')) u
Proof
  rpt gen_tac >> strip_tac >>
  `!n b len. local_region cenv es.scopes s0 n b len ==>
     mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt strip_tac >>
     `local_region cenv es'.scopes t n b len` by
       (irule local_region_frame_fwd >>
        qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
        gvs[target_post_def]) >>
     first_x_assum drule >> simp[]) >>
  `locals_kept cenv es s0 u` by
    (irule locals_kept_regions_tail >> qexists_tac `t` >>
     conj_tac >- first_assum ACCEPT_TAC >> gvs[target_post_def]) >>
  gvs[target_post_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) 
  >> rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
    (qpat_x_assum `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> _` drule >> simp[]) >>
  `aid < sm.cs_next_id` by decide_tac >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (qpat_x_assum `!aid b len. aid < sm.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[]) >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
    drule_all >> simp[]
QED

Theorem compile_mapping_subscript_alloca_member:
  compile_mapping_subscript slot_op key_op sa = (op,sb) /\
  fn_has_code sa sb func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) sb.cs_current_insts` by
    gvs[compile_mapping_subscript_def, contextTheory.compile_alloc_buffer_def,
        emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  gvs[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[MEM_APPEND]
QED

(* Evaluability already excludes oversized fixed bytes. *)
Theorem hashmap_key_fixed33_invalid_probe[local]:
  ~well_formed_type FEMPTY (BaseT (BytesT (Fixed 33))) /\
  hashmap_key_type (BaseT (BytesT (Fixed 33))) /\
  ~is_bytestring_type (BaseT (BytesT (Fixed 33))) /\
  ~is_word_type (BaseT (BytesT (Fixed 33)))
Proof
  EVAL_TAC
QED


(* Mapping extension is state preserving and its pointer is independent of
   the machine state; both nested maps and stored leaves use the same hash. *)
Theorem target_mapping_extend_place:
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) es =
    (INL pv, es') ==>
  es' = es /\
  place_ptr_rel cenv cx s pv (hashmap_slot slot (encode_hashmap_key kt kv))
    (SOME (slot_loc tr)) vt /\
  place_readable cx es' pv
Proof
  Cases_on `vt`
  >- (rename1 `Type typ` >>
      Cases_on `evaluate_type (get_tenv cx) typ` >>
      simp[extend_place_def, lift_option_type_def, bind_def,
           return_def, raise_def, place_ptr_rel_def, place_readable_def] >>
      rpt strip_tac >> gvs[place_ptr_rel_def, place_readable_def]) >>
  simp[extend_place_nested_mapping] >> rpt strip_tac >>
  gvs[place_ptr_rel_def, place_readable_def]
QED

Theorem target_mapping_hash_run:
  target_post ctx func cenv cx es sa sm s0 es' (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb t /\
  compile_mapping_subscript (FST rb) key_op sm = (dst,sb) /\
  eval_operand key_op t = SOME (encode_hashmap_key kt kv) /\
  (!x. key_op = Var x ==> not_fresh_at sm x) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) es' =
    (INL pv, es'') ==>
  ?u. run_inst_seq (emitted_insts sm sb) t = OK u /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (dst,SOME (slot_loc tr),SOME (value_type_place vt)) u
Proof
  strip_tac >>
  `eval_operand (FST rb) t = SOME slot /\
   stmt_state_rel ctx func cenv cx es' t /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  drule_all compile_mapping_subscript_alloca_member >> strip_tac >>
  drule_all compile_mapping_subscript_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  drule target_mapping_extend_place >>
  disch_then (qspecl_then [`u`, `cenv`] strip_assume_tac) >> gvs[] >>
  irule target_post_regions_suffix_frame >>
  simp[] >>
  qexistsl_tac [`HashMapRef tr slot kt vt`, `rb`, `sm`, `t`, `HashMapT kt vt`] >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem target_mapping_key_preprocess:
  target_post ctx func cenv cx es sa sm s0 es' (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb t /\
  expr_post ctx func cenv cx e esk se sm sk es' kv key_op t /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key_op F
   else comp_return key_op) sm = (encoded_op,sh) /\
  (!x. key_op = Var x ==> not_fresh_at sm x) /\
  (!l. FST rb <> Label l) /\
  local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sh.cs_next_var ==>
  ?u. run_inst_seq (emitted_insts sm sh) t = OK u /\
    eval_operand encoded_op u = SOME (encode_hashmap_key kt kv) /\
    target_post ctx func cenv cx es sa sh s0 es' (HashMapRef tr slot kt vt)
      (HashMapT kt vt)
      (FST rb,SOME (slot_loc tr),SOME (value_type_place (HashMapT kt vt))) u
Proof
  strip_tac >> drule_all hashmap_key_preprocess >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sh) t = OK u` >>
  `eval_operand (FST rb) t = SOME slot /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  `eval_operand (FST rb) u = SOME slot` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u with vs_vars := t.vs_vars = t`
      (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sh x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  qexists_tac `u` >> simp[] >>
  irule target_post_suffix_frame >>
  simp[place_ptr_rel_def, place_readable_def] >>
  qexistsl_tac [`HashMapRef tr slot kt vt`, `rb`, `sm`, `t`, `HashMapT kt vt`] >>
  simp[]
QED

Theorem target_mapping_suffix_run:
  target_post ctx func cenv cx es sa sm s0 es' (HashMapRef tr slot kt vt)
    (HashMapT kt vt) rb t /\
  expr_post ctx func cenv cx e esk se sm sk es' kv key_op t /\
  expr_type e = kt /\ hashmap_key_type kt /\
  evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv kv /\
  (if is_bytestring_type kt then compile_keccak256_key key_op F
   else comp_return key_op) sm = (encoded_op,sh) /\
  compile_mapping_subscript (FST rb) encoded_op sh = (dst,sb) /\
  (!x. key_op = Var x ==> not_fresh_at sm x) /\
  (!x. encoded_op = Var x ==> not_fresh_at sh x) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\ (!l. FST rb <> Label l) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv sh /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sh.cs_next_var /\
  sa.cs_next_id <= sh.cs_next_id /\
  sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh /\
  sb.cs_current_insts = sh.cs_current_insts ++ emitted_insts sh sb /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_has_code sh sb func /\ fn_inst_ids_distinct func /\
  extend_place cx (HashMapRef tr slot kt vt) (ValueSubscript kv) es' =
    (INL pv, es'') ==>
  ?u. run_inst_seq (emitted_insts sm sb) t = OK u /\
    target_post ctx func cenv cx es sa sb s0 es'' pv vt
      (dst,SOME (slot_loc tr),SOME (value_type_place vt)) u
Proof
  strip_tac >> drule_all target_mapping_key_preprocess >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sh) t = OK preprocessed` >>
  `sa.cs_next_var <= sh.cs_next_var` by decide_tac >>
  qpat_assum `target_post _ _ _ _ _ _ sh _ _ _ _ _ _`
    (mp_then Any mp_tac target_mapping_hash_run) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sb) preprocessed = OK u` >>
  `run_inst_seq (emitted_insts sm sb) t = OK u` by
    (drule_all run_inst_seq_chain >> simp[]) >>
  qexists_tac `u` >> simp[]
QED

Theorem slots_in_range_dynamic_capacity:
  !st slot et cap.
    slots_in_range st (w2n slot) (ArrayTV et (Dynamic cap)) ==>
    w2n (lookup_storage slot st) <= cap
Proof
  simp[vyperLookupStorageTheory.slots_in_range_def,
       vyperStorageTheory.read_slot_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem storage_fixed_array_child_slots:
  !st w et n i.
    slots_in_range st (w2n (w:bytes32)) (ArrayTV et (Fixed n)) /\ i < n ==>
    slots_in_range st (w2n (w + n2w (i * type_slot_size et))) et
Proof
  rpt strip_tac >>
  `slots_in_range st (w2n w + i * type_slot_size et) et` by
    (gvs[vyperLookupStorageTheory.slots_in_range_def,
         vyperLookupStorageTheory.array_slots_in_range_indexed]) >>
  `slots_in_range st (w2n w + i * type_slot_size et) et =
   slots_in_range st (w2n (w + n2w (i * type_slot_size et))) et` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w (i * type_slot_size et) =
      n2w (w2n w + i * type_slot_size et)` by
       simp[GSYM word_add_n2w] >>
     simp[]) >>
  gvs[]
QED

Theorem storage_dynamic_array_child_slots:
  !st w et n i.
    slots_in_range st (w2n (w:bytes32)) (ArrayTV et (Dynamic n)) /\
    i < w2n (lookup_storage w st) ==>
    slots_in_range st (w2n (w + n2w (1 + i * type_slot_size et))) et
Proof
  rpt strip_tac >>
  `slots_in_range st (w2n w + (1 + i * type_slot_size et)) et` by
    (gvs[vyperLookupStorageTheory.slots_in_range_def,
         vyperStorageTheory.read_slot_def, AllCaseEqs(),
         vyperLookupStorageTheory.array_slots_in_range_indexed] >>
     simp[GSYM ADD_ASSOC]) >>
  `slots_in_range st (w2n w + (1 + i * type_slot_size et)) et =
   slots_in_range st (w2n (w + n2w (1 + i * type_slot_size et))) et` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w (1 + i * type_slot_size et) =
      n2w (w2n w + (1 + i * type_slot_size et))` by
       simp[GSYM word_add_n2w] >> simp[]) >>
  gvs[]
QED

Theorem extend_place_storage_array_live:
  !cx tr slot et bd i es pv es'.
    storage_read_live cx tr (get_storage cx es tr) slot (ArrayTV et bd) /\
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
      (ValueSubscript (IntV i)) es = (INL pv,es') ==>
    ?child. pv = PlaceR (StoragePlace tr child et) /\
      storage_read_live cx tr (get_storage cx es' tr) child et
Proof
  rpt gen_tac >> Cases_on `bd` >>
  simp[extend_place_storage_array_index, AllCaseEqs()] >> rpt strip_tac >>
  gvs[]
  >- (irule storage_read_live_fixed_array_child >> goal_assum (drule_at Any) >> simp[]) >>
  once_rewrite_tac[ADD_COMM] >>
  irule storage_read_live_dynamic_array_child >> simp[] >> qexists `n` >> simp[]
QED

Theorem extend_place_storage_array_slots:
  !cx tr slot et bd i es pv es'.
    slots_in_range (get_storage cx es tr) (w2n slot) (ArrayTV et bd) /\
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV et bd)))
      (ValueSubscript (IntV i)) es = (INL pv,es') ==>
    ?child. pv = PlaceR (StoragePlace tr child et) /\
      slots_in_range (get_storage cx es' tr) (w2n child) et
Proof
  rpt gen_tac >> Cases_on `bd` >>
  simp[extend_place_storage_array_index, AllCaseEqs()] >> rpt strip_tac >>
  gvs[]
  >- (irule storage_fixed_array_child_slots >> goal_assum (drule_at Any) >> simp[]) >>
  once_rewrite_tac[ADD_COMM] >>
  irule storage_dynamic_array_child_slots >> simp[] >> qexists `n` >> simp[]
QED

Theorem target_post_storage_step:
  !ctx func cenv cx es sa sm sb s0 es2 tr slot tv ty rb t u
    slot' etv ety dst.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (StoragePlace tr slot tv)) (Type ty) rb t /\
    evaluate_type (get_tenv cx) ety = SOME etv /\
    eval_operand dst u = SOME slot' /\
    stmt_state_rel ctx func cenv cx es2 u /\
    sa.cs_next_var <= sm.cs_next_var /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    (!x z. not_fresh_at sm x /\ lookup_var x t = SOME z ==>
           lookup_var x u = SOME z) /\
    (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
             FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_memory = t.vs_memory ==>
    target_post ctx func cenv cx es sa sb s0 es2
      (PlaceR (StoragePlace tr slot' etv)) (Type ety)
      (dst,SOME (slot_loc tr),SOME (ValPT ety)) u
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[GSYM value_type_place_def] >>
  drule_then irule target_post_suffix_frame >>
  simp[place_ptr_rel_def, place_readable_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem target_storage_array_static_suffix:
  !ctx func cenv cx es sa sm sb s0 es2 es3 tr slot et n etv
    rb t ix iw i bt bits dst res.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed n))))
      (Type (ArrayT et (Fixed n))) rb t /\
    evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) =
      SOME (ArrayTV etv (Fixed n)) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    (bt = IntT bits \/ bt = UintT bits) /\ bits <= 256 /\
    value_has_type (BaseTV bt) (IntV i) /\
    iw = typed_val_to_w256 (BaseTV bt) (IntV i) /\
    compile_array_subscript (FST rb) ix F n 1 (type_slot_size etv)
      (is_signed_type (BaseT bt))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)) sm = (dst,sb) /\
    eval_operand (FST rb) t = SOME slot /\ eval_operand ix t = SOME iw /\
    (!x. ix = Var x ==> not_fresh_at sm x) /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed n))))
      (ValueSubscript (IntV i)) es2 = (res,es3) ==>
    frag_exec ctx sm sb
      (\s. s = t /\ stmt_state_rel ctx func cenv cx es2 s)
      (\s. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 es3 pv' (Type et)
          (dst,SOME (slot_loc tr),SOME (ValPT et)) s)
      (expr_exit res)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `n < dimword (:256)` by
    (drule evaluate_type_array_bound_word >> simp[bound_length_def]) >>
  `(idx_in_range (is_signed_type (BaseT bt)) iw (n2w n) <=>
    0 <= i /\ Num i < n)` by
    (irule idx_in_range_typed_int >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `bits` >> simp[]) >>
  gnvs[extend_place_storage_array_index] >>
  Cases_on `0 <= i /\ Num i < n` >> gnvs[]
  >- suspend "success" >>
  suspend "oob"
QED

Resume target_storage_array_static_suffix[success]:
  RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  rename1 `target_post ctx func cenv cx es sa sm s0 live_es
    (PlaceR (StoragePlace tr slot (ArrayTV etv (Fixed n)))) (Type (ArrayT et (Fixed n))) rb t` >>
  `!x. FST rb = Var x ==> not_fresh_at sm x` by gvs[target_post_def] >>
  `typed_val_to_w256 (BaseTV bt) (IntV i) = n2w (Num i)` by
    (`i = &Num i` by simp[INT_OF_NUM] >>
     pop_assum SUBST1_TAC >>
     gvs[typed_val_to_w256_def, val_to_w256_def, i2w_pos]) >>
  drule_all compile_array_static_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `live_es`] mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[expr_exit_def] >> rpt strip_tac >>
  drule_then irule target_post_storage_step >>
  simp[word_mul_n2w] >> goal_assum (drule_at Any) >> simp[]
QED

Resume target_storage_array_static_suffix[oob]:
  drule_all compile_array_static_frag_oob >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es3`] mp_tac) >>
  disch_then (qspec_then `\s. F` mp_tac) >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> gvs[expr_exit_def]
QED

Finalise target_storage_array_static_suffix

Theorem target_storage_array_dynamic_suffix:
  !ctx func cenv cx es sa sm sb s0 es2 es3 tr slot et cap etv
    rb t ix iw i bt bits dst res.
    target_post ctx func cenv cx es sa sm s0 es2
      (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
      (Type (ArrayT et (Dynamic cap))) rb t /\
    stmt_state_rel ctx func cenv cx es2 t /\
    storage_read_live cx tr (get_storage cx es2 tr) slot (ArrayTV etv (Dynamic cap)) /\
    slots_in_range (get_storage cx es2 tr) (w2n slot) (ArrayTV etv (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) =
      SOME (ArrayTV etv (Dynamic cap)) /\
    evaluate_type (get_tenv cx) et = SOME etv /\
    (bt = IntT bits \/ bt = UintT bits) /\ bits <= 256 /\
    value_has_type (BaseTV bt) (IntV i) /\
    iw = typed_val_to_w256 (BaseTV bt) (IntV i) /\
    compile_array_subscript (FST rb) ix T 0 1 (type_slot_size etv)
      (is_signed_type (BaseT bt))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)) sm = (dst,sb) /\
    eval_operand (FST rb) t = SOME slot /\ eval_operand ix t = SOME iw /\
    (!x. ix = Var x ==> not_fresh_at sm x) /\
    (!x. dst = Var x ==> not_fresh_at sb x) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cap))))
      (ValueSubscript (IntV i)) es2 = (res,es3) ==>
    frag_exec ctx sm sb
      (\s. s = t /\ stmt_state_rel ctx func cenv cx es2 s)
      (\s. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 es3 pv' (Type et)
          (dst,SOME (slot_loc tr),SOME (ValPT et)) s)
      (expr_exit res)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (lookup_storage slot (get_storage cx es2 tr)) <= cap` by
    gvs[vyperLookupStorageTheory.slots_in_range_def, vyperStorageTheory.read_slot_def] >>
  `0 < type_slot_size (ArrayTV etv (Dynamic cap))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all stmt_state_rel_storage_live_head >> strip_tac >>
  `(idx_in_range (is_signed_type (BaseT bt)) iw
      (lookup_storage slot (get_storage cx es2 tr)) <=>
    0 <= i /\ Num i < w2n (lookup_storage slot (get_storage cx es2 tr)))` by
    (`idx_in_range (is_signed_type (BaseT bt)) iw
        (n2w (w2n (lookup_storage slot (get_storage cx es2 tr)))) <=>
        0 <= i /\ Num i < w2n (lookup_storage slot (get_storage cx es2 tr))`
       suffices_by simp[] >>
     irule idx_in_range_typed_int >> simp[w2n_lt] >> qexists_tac `bits` >> simp[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sm x` by gvs[target_post_def] >>
  `~(slot_loc tr = LocMemory)` by (Cases_on `tr` >> gvs[slot_loc_def]) >>
  `(slot_loc tr = LocStorage <=> ~tr)` by (Cases_on `tr` >> gvs[slot_loc_def]) >>
  `(slot_loc tr = LocTransient <=> tr)` by (Cases_on `tr` >> gvs[slot_loc_def]) >>
  drule compile_array_dynamic_outcome >>
  simp[] >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`ctx`,`func`,`cx`,`es2`] mp_tac) >>
  simp[] >>
  disch_then (mp_then Any match_mp_tac frag_exec_weaken) >>
  simp[] >> conj_tac
  >- suspend "success" >>
  suspend "exit"
QED

Resume target_storage_array_dynamic_suffix[success]:
  rpt strip_tac >> RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  `0 <= i /\ Num i < w2n (lookup_storage slot (get_storage cx es2 tr))` by
    (Cases_on `tr` >> gvs[]) >>
  `Num i < cap` by decide_tac >>
  `typed_val_to_w256 (BaseTV bt) (IntV i) = n2w (Num i)` by
    (`i = &Num i` by simp[INT_OF_NUM] >>
     pop_assum SUBST1_TAC >>
     gvs[typed_val_to_w256_def, val_to_w256_def, i2w_pos]) >>
  gnvs[extend_place_storage_array_index] >>
  RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  drule_then irule target_post_storage_step >>
  simp[word_mul_n2w, word_add_n2w, GSYM WORD_ADD_ASSOC,
       AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Resume target_storage_array_dynamic_suffix[exit]:
  rpt strip_tac >> RULE_L_ASSUM_TAC CONJUNCTS >> gnvs[] >>
  `~(0 <= i /\ Num i < w2n (lookup_storage slot (get_storage cx es2 tr)))` by
    (Cases_on `tr` >> gvs[]) >>
  Cases_on `0 <= i /\ Num i < cap` >>
  gvs[extend_place_storage_array_index, expr_exit_def]
QED

Finalise target_storage_array_dynamic_suffix

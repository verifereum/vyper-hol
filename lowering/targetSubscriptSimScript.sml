(* Compiler boundary for subscript assignment places. *)
Theory targetSubscriptSim
Ancestors
  targetPlaceSim exprNoPopScopes exprLowering emitHelper compileEnv
  vyperAST pair exprSimOps exprSim exprLoweringProps loweringShapeDefs fragExec
  vyperState vyperStorageBackend exprSimHyps vyperTypeSystem
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
Libs
  pairLib

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

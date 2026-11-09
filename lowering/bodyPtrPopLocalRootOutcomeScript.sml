Theory bodyPtrPopLocalRootOutcome
Ancestors
  bodyPtrPopLocalRootCompileFrame bodyPtrPopLocalRootCompile bodyPtrPopLocalRootPointerPost
  exprSimDefs
  bodyPtrPopLocalRootSemanticPost bodyPtrPopLocalRootSource
  bodyPtrPopLocalRootEntry bodyPtrPopLocalRootBounds
  bodyPtrDefs exprSimPop exprSimProps exprSimHypsDefs
  exprLowering exprLoweringProps emitHelperProps compileEnv context venomState
  gasOutcome gasSummary fragGasPathPtr fragExec stmtFragPtr
  finite_map words list rich_list arithmetic loweringPosts vyperLookup

Theorem pop_local_expr_vv_ptr:
  expr_sim_pre cenv cx env (Pop ann (NameTarget id)) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann (NameTarget id)) es
Proof
  strip_tac >> rw[expr_vv_sim_ptr_def] >>
  drule_all pop_name_facts >> strip_tac >>
  drule_all compile_expr_pop_name >> strip_tac >> gvs[] >>
  Cases_on `compile_dynarray_pop (Var p) 32 (type_memory_size etv)
    cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory sa` >>
  qmatch_asmsub_rename_tac `compile_dynarray_pop _ _ _ _ _ _ _ = (rop,sc)` >>
  gvs[] >>
  `not_fresh_at sa p /\ local_ptrs_rel func cenv es.scopes s0` by
    (fs[local_ptrs_reserved_def, stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  drule_all pop_local_robust_layout >> strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  rename1 `find_containing_scope id es.scopes = SOME (pre,envs,entry,rest)` >>
  Cases_on `vs = []`
  >- suspend "empty" >>
  suspend "positive"
QED

Resume pop_local_expr_vv_ptr[empty]:
  gvs[] >>
  `32 <= sz` by decide_tac >>
  drule_all pop_local_compile_empty_path >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError "pop empty memory array"))`,
    `es`, `G'`, `tn'`, `Abort Revert_abort (revert_state (set_returndata [] t))`] >>
  simp[exit_result_def, expr_exit_def] >> rpt strip_tac >>
  irule pop_local_source_empty_ptr >> simp[] >> metis_tac[]
QED

Resume pop_local_expr_vv_ptr[positive]:
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `0 < type_memory_size etv` by
    (drule placeMemoryTypedBaseTheory.typed_memory_array_stride_bounds >> simp[]) >>
  `32 <= sz /\ LENGTH vs < dimword(:256) /\
   32+(LENGTH vs-1)*type_memory_size etv < sz /\
   32+(LENGTH vs-1)*type_memory_size etv+type_memory_size etv <= sz /\
   w2n w+sz <= dimword(:256)` by
    (mp_tac (Q.INST [`esz` |-> `type_memory_size etv`,
       `len` |-> `LENGTH (vs:value list)`, `cap` |-> `n`, `bytes` |-> `sz`]
       pop_local_interior_bounds) >>
     simp[] >> strip_tac >>
     `s0.vs_alloca_next < dimword(:256)` by
       (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
     decide_tac) >>
  drule_all pop_local_compile_nonempty_exact >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "posts"
QED

Resume pop_local_expr_vv_ptr[posts]:
  qabbrev_tac `ee = es with scopes := pre ++ envs |+ (id,pop_name_entry entry vs) :: rest` >>
  `lookup_scopes id ee.scopes = SOME (pop_name_entry entry vs) /\
   (!name. name <> id ==> lookup_scopes name ee.scopes = lookup_scopes name es.scopes)` by
    (drule find_containing_scope_pre_none >> strip_tac >>
     simp[Abbr `ee`, lookup_scopes_update] >>
     metis_tac[lookup_scopes_set_other]) >>
  `w2n w+32+(LENGTH vs-1)*type_memory_size etv < dimword(:256)` by decide_tac >>
  drule_all pop_local_pointer_endpoint >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  `lookup_var out t = SOME
    (w+32w+(n2w (LENGTH vs)-1w)*n2w (type_memory_size etv))` by
    (simp[GSYM n2w_sub, GSYM word_add_n2w, GSYM word_mul_n2w] >>
     simp[word_add_n2w, word_mul_n2w, ADD_ASSOC]) >>
  `t.vs_memory = (mstore (w2n w) (n2w (LENGTH vs)-1w) s0).vs_memory` by
    simp[GSYM n2w_sub] >>
  `vv_post ctx func cenv cx (Pop ann (NameTarget id)) es sa sc s0 ee
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) t` by
    (simp[Abbr `ee`] >> irule pop_local_vv_post_cursor >>
     simp[] >> rpt conj_tac
     >- (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[])
     >- metis_tac[local_ptrs_reserved_imm_base] >>
     metis_tac[]) >>
  suspend "package"
QED

Resume pop_local_expr_vv_ptr[package]:
  `vv_post ctx func cenv cx (Pop ann (NameTarget id)) es sa sc s0
    (ee with gas_obs := [])
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) t` by
    (irule pop_local_memory_post_gas_obs >> simp[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs-1))]))`,
    `ee`, `G'`, `tn'`, `OK t`] >>
  simp[exit_result_def, mk_ptr_def, vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (gen_tac >> simp[Abbr `ee`] >>
      irule pop_local_source_nonempty_ptr >> simp[] >> metis_tac[]) >>
  metis_tac[mk_ptr_def]
QED

Finalise pop_local_expr_vv_ptr

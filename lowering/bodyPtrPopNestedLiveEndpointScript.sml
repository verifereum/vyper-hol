Theory bodyPtrPopNestedLiveEndpoint
Ancestors
  bodyPtrPopNestedLiveGhost bodyPtrPopNestedLiveUpdate bodyPtrPopNestedLiveResult
  bodyPtrPopNestedLivePost exprSimPopNestedLocalMemory exprSimPop
  valueEncoding valueEncodingDefs list rich_list
  bodyPtrPopNestedLiveSuffixFrame exprSimPopNestedLocalSuffix bodyPtrDefs
  localPtrsProps compileEnv venomState finite_map pred_set

Theorem pop_updated_local_ghost:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME old /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) cap) /\
  lookup_var root s = SOME b /\
  local_region cenv es.scopes s id (w2n b) cap /\ k+32 <= cap /\
  lookup_scopes id scopes' = SOME (old with <|value := updated; popped := hist|>) /\
  (!name. name <> id ==> lookup_scopes name scopes' = lookup_scopes name es.scopes) /\
  (!mem. mem_agree_outside tn.t_mem (mstore (w2n b+k) wd s).vs_memory mem ==>
    val_in_memory old.type updated (w2n b) mem) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\
  t.vs_memory = (mstore (w2n b+k) wd s).vs_memory /\
  stor_taint_ok cx tf t ==>
  ghost_inv d cenv cx (es with scopes := scopes') H tf t
Proof
  strip_tac >>
  irule pop_header_ghost_transport >>
  pure_asm_rewrite_tac [boolTheory.AND_CLAUSES] >>
  qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
  asm_simp_tac bool_ss [vyperStateTheory.evaluation_state_accfupds] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  rewrite_tac[combinTheory.K_THM] >>
  match_mp_tac pop_header_locals_robust >>
  simp[]
QED

Theorem pop_clean_path_update_robust:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts tv a path (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  (!i. locbase+k <= i /\ i < locbase+k+32 ==> i NOTIN dirty) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory tv a locbase mem) ==>
  !mem. mem_agree_outside dirty
    (mstore (locbase+k) (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory tv updated locbase mem
Proof
  strip_tac >>
  `val_wf tv updated` by (drule_all pop_path_update_val_wf >> simp[]) >>
  `dirty DIFF {i | locbase+k <= i /\ i < locbase+k+32} = dirty` by
    (simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss) [EXTENSION] >> metis_tac[]) >>
  metis_tac[pop_path_update_robust]
QED

Theorem pop_clean_path_result_robust:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  (!i. locbase+k <= i /\ i < locbase+k+32 ==> i NOTIN dirty) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
    val_in_memory tv a locbase mem) ==>
  !mem. mem_agree_outside dirty
    (mstore (locbase+k) (n2w (LENGTH vs-1)) s).vs_memory mem ==>
    val_in_memory etv (LAST vs)
      (locbase+k+32+(LENGTH vs-1)*type_memory_size etv) mem
Proof
  strip_tac >>
  `dirty DIFF {i | locbase+k <= i /\ i < locbase+k+32} = dirty` by
    (simp_tac (bool_ss ++ pred_setLib.PRED_SET_ss) [EXTENSION] >> metis_tac[]) >>
  metis_tac[pop_path_result_robust]
QED

Theorem pop_path_result_ptr_post:
  mutable_place_path tv path /\ value_has_type tv a /\
  well_formed_type_value tv /\ val_wf tv a /\
  mem_path_offset tv path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  (!i. locbase+k <= i /\ i < locbase+k+32 ==> i NOTIN tn.t_mem) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv a locbase mem) /\
  tf.t_mem = tn.t_mem /\
  t.vs_memory = (mstore (locbase+k) (n2w (LENGTH vs-1)) s).vs_memory /\
  lookup_var out t = SOME w /\
  w2n w = locbase+k+32+(LENGTH vs-1)*type_memory_size etv /\
  ptr_covers H tf out t (type_memory_size etv) /\
  read_result cx result es' = (INL (LAST vs),es') /\
  evaluate_type (get_tenv cx) ty = SOME etv ==>
  ptr_vv_ok cx ty result (LocatedValue ty (mk_ptr (Var out) LocMemory)) es' H tf t
Proof
  strip_tac >>
  `val_in_memory tv a locbase s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_wf (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (drule_all val_in_memory_mutable_path >> simp[]) >>
  `val_wf etv (LAST vs)` by
    (fs[val_wf_def] >> drule elems_val_wf_EL >>
     disch_then (qspec_then `LENGTH vs-1` mp_tac) >>
     `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  irule pop_result_ptr_vv_ok >>
  qexistsl_tac [`etv`, `LAST vs`, `w`] >>
  asm_simp_tac bool_ss [] >>
  match_mp_tac pop_clean_path_result_robust >> simp[]
QED

Theorem pop_live_path_ghost_post:
  ghost_inv d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\
  lookup_scopes id es.scopes = SOME old /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var root) cap) /\
  lookup_var root s = SOME b /\
  local_region cenv es.scopes s id (w2n b) cap /\ k+32 <= cap /\
  lookup_scopes id scopes' = SOME (old with <|value := updated; popped := hist|>) /\
  (!name. name <> id ==> lookup_scopes name scopes' = lookup_scopes name es.scopes) /\
  mutable_place_path old.type path /\ value_has_type old.type old.value /\
  well_formed_type_value old.type /\ val_wf old.type old.value /\
  mem_path_offset old.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts old.type old.value path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  assign_subscripts old.type old.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  (!i. w2n b+k <= i /\ i < w2n b+k+32 ==> i NOTIN tn.t_mem) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\
  t.vs_memory = (mstore (w2n b+k) (n2w (LENGTH vs-1)) s).vs_memory /\
  stor_taint_ok cx tf t ==>
  ghost_inv d cenv cx (es with scopes := scopes') H tf t
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`wd` |-> `n2w (LENGTH (vs:value list)-1)`] pop_updated_local_ghost) >>
  asm_simp_tac bool_ss [] >>
  reverse conj_tac >- metis_tac[] >>
  match_mp_tac (Q.INST [`a` |-> `old.value`] pop_clean_path_update_robust) >>
  asm_simp_tac bool_ss [] >>
  fs[ghost_inv_def] >> metis_tac[]
QED

(* Keep the first EC point through the successful read of the second operand. *)
Theory bodyECHeldPointMods
Ancestors
  bodyFullPostsMods bodyRawLocalBytesLayoutMods bodyMemEcArithOperands
  bodyPtrPrecompileBuiltinsArithmeticSource bodyPtrPrecompileBuiltinsBoundary
  bodyPtrPrecompileBuiltinsGhost exprOperandVar exprBodyPreProps exprSimHyps
  exprSimOperands exprSimProps compileEnv freshWrites loweringPosts
  bodyPtrDefs vyperTypeExprSoundness vyperTyping vyperAST vyperValue
  valueEncoding venomState words exprLowering vyperTypeSystem

Theorem ecadd_operand_post_type:
  expr_body_pre_mods mods cenv cx env e es /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      gvs[well_typed_expr_def, lowered_value_type_def, expr_type_def] >>
      drule_all_then assume_tac expr_sim_inv_mods_return_type >>
      gvs[] >> metis_tac[type_widens_to_ec_point]) >>
  irule post_value_type_not_int_call >> metis_tac[]
QED

Theorem ec_local_point_apart[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  local_path_at cenv cx n k (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) /\
  dynarray_len_at cenv n k' ==>
  k + 64 <= k' \/ k' + 32 <= k
Proof
  rw[local_path_at_def, dynarray_len_at_def] >> gvs[] >>
  drule_all_then strip_assume_tac type_path_offset_mem_mods >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `dynarray_free (ArrayTV (BaseTV (UintT 256)) (Fixed 2))` by
    simp[dynarray_free_fixed, dynarray_free_base] >>
  drule_all mem_path_offset_dynarray_apart >> simp[type_memory_size_def]
QED

Theorem ec_point_window_kept[local]:
  post_value_type cenv e1 = expr_type e1 /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
  expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
  expr_sim_inv_mods mods cenv cx env es /\
  eval_operand x t1 = SOME w /\ eval_operand x t2 = SOME w /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  s1.cs_next_id <= s2.cs_next_id /\
  ghost_kept cenv es1 s1 G1 tn1 t1 G2 tn2 /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn1.t_mem) ==>
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa s2 es2 v1 x t2 /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn2.t_mem)
Proof
  strip_tac >>
  `expr_val_at cenv cx (expr_type e1) sa s1 es1 v1 x t1` by
    gvs[expr_post_def] >>
  pop_assum mp_tac >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def,
       is_word_type_def, type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >> strip_tac
  >- (`expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t1` by
        (simp[expr_val_in_alloca_def, evaluate_type_def, is_word_type_def,
              ec_point_footprint] >> metis_tac[]) >>
      `!wx. eval_operand x t1 = SOME wx ==> eval_operand x t2 = SOME wx` by simp[] >>
      drule_all_then strip_assume_tac expr_post_operand_kept_stable >>
      qpat_assum `expr_val_in_alloca _ _ _ _ _ _ _ _ t2`
        (mp_tac o MATCH_MP expr_val_in_alloca_at) >>
      simp[expr_val_at_def,local_val_at_def,evaluate_type_def,is_word_type_def,
           type_slot_size_def,wordsTheory.dimword_def,ec_point_footprint] >>
      disch_tac >> gvs[] >>
      metis_tac[Q.INST [`a` |-> `w2n (w:256 word)`, `m` |-> `64`]
                 ghost_kept_alloca_clean]) >>
  `!k. dynarray_len_at cenv n k ==>
       w2n w + 64 <= b + k \/ b + k + 32 <= w2n w` by
    (rpt strip_tac >> drule_all ec_local_point_apart >> decide_tac) >>
  conj_tac
  >- (irule expr_post_operand_local_kept >>
      simp[evaluate_type_def,is_word_type_def,ec_point_footprint] >>
      qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexistsl_tac [`sz`,`n`,`b`] >>
      simp[type_slot_size_def, wordsTheory.dimword_def,
           GSYM arithmeticTheory.ADD_ASSOC] >> gvs[expr_post_def]) >>
  conj_tac
  >- (`local_region cenv es2.scopes t2 n b sz` by
        (irule local_region_frame_fwd >>
         qexistsl_tac [`t1`,`s1`,`es1.scopes`] >> fs[expr_post_def]) >>
      simp[expr_val_at_def, local_val_at_def, evaluate_type_def,
           is_word_type_def, type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
      disj2_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]) >>
  metis_tac[Q.INST [`a` |-> `w2n (w:256 word)`, `m` |-> `64`] ghost_kept_local_clean]
QED

Theorem ec_held_point_at_second_cut_mods:
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  post_value_type cenv e1 = expr_type e1 /\
  expr_post_mods H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
  expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
  expr_store_bound cx (post_value_type cenv e1) v1 x t1 /\
  ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t1 /\
  value_runtime_typed env (expr_type e1) v1 /\
  expr_sim_inv_mods mods cenv cx env es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  MAP FDOM es1.scopes = MAP FDOM es2.scopes /\
  s1.cs_next_var <= s2.cs_next_var /\ s1.cs_next_id <= s2.cs_next_id /\
  t1.vs_alloca_next <= t2.vs_alloca_next /\
  ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2 ==>
  ?p w lp. x = Var p /\ lookup_var p t1 = SOME w /\ lookup_var p t2 = SOME w /\
    not_fresh_at s2 p /\
    expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lp s2 es2 v1 (Var p) t2 /\
    expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 (Var p) t2 /\
    ptr_covers G2 tn2 p t2 64 /\ w2n w + 64 < dimword (:256) /\
    w2n w + 64 <= t2.vs_alloca_next /\
    (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn2.t_mem)
Proof
  rewrite_tac[expr_post_mods_def] >> strip_tac >>
  `expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) sa s1 es1 v1 x t1` by
    gvs[expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx es1 t1` by fs[expr_post_def] >>
  drule_all_then strip_assume_tac ec_point_eval_bound >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1` by
    gvs[value_runtime_typed_def, evaluate_type_def] >>
  `ptr_val_ok cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x G1 tn1 t1` by gvs[] >>
  drule_all_then strip_assume_tac ec_point_read_ready >>
  `not_fresh_at s1 p` by (drule_all compile_lower_value_var >> simp[]) >>
  qpat_x_assum `x = Var p` SUBST_ALL_TAC >>
  `eval_operand (Var p) t2 = SOME w` by fs[expr_post_def, eval_operand_def] >>
  `ghost_kept cenv es1 s1 G1 tn1 t1 G2 tn2` by
    (qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     gvs[ghost_kept_at_def, ghost_kept_def]) >>
  drule_all_then strip_assume_tac ec_point_window_kept >>
  drule_all_then assume_tac ghost_kept_ptr_covers >>
  `w2n w + 64 <= t2.vs_alloca_next` by
    (irule ec_point_read_capacity >> qexistsl_tac [`cx`,`Var p`,`t1`,`v1`] >> gvs[]) >>
  map_every qexists_tac [`p`,`w`,`sa`] >> gvs[eval_operand_def] >>
  irule not_fresh_at_mono >> qexists_tac `s1` >> simp[]
QED

Theory bodyPtrPrecompileBuiltinsOperandTransport
Ancestors bodyPtrPrecompileBuiltinsArithmeticValue valueTypingMemoryProps
          valueEncodingProps exprSimProps bodyPtrDefs loweringPosts
          exprSimOperands bodyPtrPrecompileBuiltinsOperands
          valueEncoding compileEnv vyperTyping exprSimAttributeFields vyperValue

Theorem ec_point_ptr_reconstruct:
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) /\
  ~is_word_type ty /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v /\
  expr_val_rel cx ty v (Var dst) s /\
  eval_operand (Var dst) s = SOME w /\
  ptr_covers G tn dst s 64 /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem) ==>
  ptr_val_ok cx ty v (Var dst) G tn s
Proof
  strip_tac >>
  `val_wf (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v` by
    metis_tac[value_has_type_memory_wf] >>
  `val_store_size (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v <= 64` by
    (drule val_store_size_le >> simp[valueEncodingTheory.type_memory_size_def]) >>
  simp[ptr_val_ok_def] >> conj_tac
  >- gvs[ptr_covers_def] >>
  simp[ptr_mem_ok_def] >> conj_tac
  >- (rpt strip_tac >> irule val_in_memory_mem_agree >>
      conj_tac >- simp[] >>
      qexistsl [`64`, `s.vs_memory`] >>
      simp[valueEncodingTheory.type_memory_size_def] >> conj_tac
      >- (irule clean_window_mem_agree >> qexists `tn.t_mem` >> simp[]) >>
      gvs[expr_val_rel_def]) >>
  gvs[ptr_covers_def, venomStateTheory.eval_operand_def] >>
  qexistsl [`b`, `sz'`] >> simp[]
QED

Theorem ec_point_operand_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  s1.cs_next_id <= s2.cs_next_id ==>
  expr_val_rel cx (expr_type e1) v1 x u /\
  expr_val_at cenv cx (expr_type e1) sa s2 es' v1 x u
Proof
  strip_tac >>
  `val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 = 64` by
    (Cases_on `v1` >> simp[val_footprint_def, type_memory_size_def]) >>
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME w` by metis_tac[] >>
  `expr_val_at cenv cx (expr_type e1) sa s1 es1 v1 x t` by
    gvs[expr_post_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  strip_tac
  >- (`expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t` by
        (simp[expr_val_in_alloca_def, evaluate_type_def, is_word_type_def,
              type_slot_size_def, wordsTheory.dimword_def] >>
         qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
      drule_all expr_post_operand_kept_stable >> strip_tac >>
      drule expr_val_in_alloca_at >> strip_tac >>
      gvs[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
          type_slot_size_def, wordsTheory.dimword_def] >> metis_tac[]) >>
  conj_tac
  >- (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
        expr_post_operand_local_kept >>
      simp[is_word_type_def, evaluate_type_def,
           type_slot_size_def, wordsTheory.dimword_def] >>
      disch_then irule >>
      simp[is_word_type_def, evaluate_type_def,
           type_slot_size_def, wordsTheory.dimword_def] >>
      conj_tac >- gvs[expr_post_def] >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> rpt strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `es`, `n`, `w2n w - b`,
                   `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`, `k`] mp_tac
        local_path_at_dynarray_apart >>
      simp[dynarray_free_fixed, dynarray_free_base, type_memory_size_def]) >>
  `local_region cenv es'.scopes u n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`t`, `s1`, `es1.scopes`] >> simp[] >> gvs[expr_post_def]) >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def] >>
  disj2_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem ec_point_ptr_operand_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_post ctx func cenv cx e2 es1 s1 s2 t es' v2 y u /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) /\
  local_ptrs_reserved cenv s1 /\ MAP FDOM es1.scopes = MAP FDOM es'.scopes /\
  s1.cs_next_id <= s2.cs_next_id /\
  ptr_val_ok cx (expr_type e1) v1 x G0 tn0 t /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  ghost_kept cenv es1 s1 G0 tn0 t G tn /\
  (!p. x = Var p ==> not_fresh_at s1 p) ==>
  ptr_val_ok cx (expr_type e1) v1 x G tn u
Proof
  strip_tac >>
  drule_all ec_point_operand_kept >> strip_tac >>
  `!w. eval_operand x u = SOME w ==>
       !i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem` by
    metis_tac[ec_point_clean_kept] >>
  drule_all ec_point_covers_kept >> strip_tac >>
  `?w. eval_operand x u = SOME w` by gvs[expr_val_rel_def] >>
  gvs[] >> irule ec_point_ptr_reconstruct >>
  simp[evaluate_type_def, is_word_type_def, type_slot_size_def,
       wordsTheory.dimword_def] >> metis_tac[]
QED

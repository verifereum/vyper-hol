Theory bodyPtrPrecompileBuiltinsOperands
Ancestors bodyPtrPrecompileBuiltinsGhost exprSimAttributeFields exprSimProps
          exprSimDefs loweringPosts valueEncoding compileEnv vyperTyping
          vyperValue

Theorem ec_point_interval_clean_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\ eval_operand x t = SOME w /\
  ghost_kept cenv es1 s1 G0 tn0 t G tn /\
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn0.t_mem) ==>
  (!i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 = 64` by
    (Cases_on `v1` >> simp[val_footprint_def, type_memory_size_def]) >>
  `expr_val_at cenv cx (expr_type e1) sa s1 es1 v1 x t` by
    gvs[expr_post_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def,
       is_word_type_def, type_slot_size_def, wordsTheory.dimword_def] >>
  strip_tac
  >- (metis_tac[ghost_kept_alloca_clean]) >>
  `!k. dynarray_len_at cenv n k ==>
       w2n w + 64 <= b + k \/ b + k + 32 <= w2n w` by
    (rpt strip_tac >>
     drule local_path_at_dynarray_apart >> disch_then drule >>
     simp[dynarray_free_fixed, dynarray_free_base, type_memory_size_def] >>
     disch_then drule >> decide_tac) >>
  metis_tac[ghost_kept_local_clean]
QED

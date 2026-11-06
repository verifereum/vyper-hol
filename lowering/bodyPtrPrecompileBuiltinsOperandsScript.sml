Theory bodyPtrPrecompileBuiltinsOperands
Ancestors bodyPtrPrecompileBuiltinsGhost exprSimAttributeFields exprSimProps
          exprSimDefs loweringPosts valueEncoding compileEnv vyperTyping
          vyperValue bodyPtrDefs representationCleanPtr vyperABI contractABI

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

Theorem word_ptr_val_ok_kept:
  is_word_type ty /\ ptr_val_ok cx ty v op G0 tn0 t /\
  ghost_kept cenv es sa G0 tn0 t G tn /\
  (!p. op = Var p ==> not_fresh_at sa p) ==>
  ptr_val_ok cx ty v op G tn u
Proof
  strip_tac >> drule_all ghost_kept_operand_taint >> strip_tac >>
  Cases_on `op` >> gvs[ptr_val_ok_def, ptrDisciplineTheory.op_prov_def] >>
  drule_all ghost_kept_provenance >> simp[]
QED

Theorem ec_point_clean_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_sim_inv cenv cx env es /\
  ptr_val_ok cx (expr_type e1) v1 x G0 tn0 t /\
  value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 /\
  ghost_kept cenv es1 s1 G0 tn0 t G tn /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) ==>
  !w. eval_operand x u = SOME w ==>
      !i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `?w0. eval_operand x t = SOME w0` by
    fs[expr_post_def, expr_val_rel_def] >>
  `!i. w2n w0 <= i /\ i < w2n w0 + 64 ==> i NOTIN tn0.t_mem` by
    (drule ptr_val_ok_static_clean >>
     simp[is_word_type_def, evaluate_type_def, vyper_to_abi_type_def,
          vyper_base_to_abi_type_def, is_dynamic_def,
          type_memory_size_def, type_slot_size_def, wordsTheory.dimword_def] >>
     disch_then drule >> simp[]) >>
  `!i. w2n w0 <= i /\ i < w2n w0 + 64 ==> i NOTIN tn.t_mem` by
    (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)
       ec_point_interval_clean_kept >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[]) >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem ec_point_covers_kept:
  expr_post ctx func cenv cx e1 es sa s1 s0 es1 v1 x t /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  ptr_val_ok cx (expr_type e1) v1 x G0 tn0 t /\
  ghost_kept cenv es1 s1 G0 tn0 t G tn /\
  (!p. x = Var p ==> not_fresh_at s1 p) /\
  (!w. eval_operand x t = SOME w ==> eval_operand x u = SOME w) ==>
  ?p. x = Var p /\ ptr_covers G tn p u 64
Proof
  strip_tac >>
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1 = 64` by
    (Cases_on `v1` >> simp[val_footprint_def, type_memory_size_def]) >>
  `?p. x = Var p /\ ptr_covers G0 tn0 p t 64` by
    (drule ptr_val_ok_read_covers >>
     simp[is_word_type_def, evaluate_type_def, type_slot_size_def,
          wordsTheory.dimword_def] >> metis_tac[]) >>
  qexists_tac `p` >> simp[] >>
  irule ghost_kept_ptr_covers >> metis_tac[]
QED

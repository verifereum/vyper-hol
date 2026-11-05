(* Operand boundaries for the memory-counted EC arithmetic case. *)
Theory bodyMemEcArithOperands
Ancestors
  exprSimMemDefs exprSimProps compileEnv exprSimOperands exprSimAttributeFields loweringPosts valueEncoding vyperValue

Theorem ec_point_read_capacity:
  expr_store_bound cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v p t /\
  eval_operand p t = SOME w /\ eval_operand p u = SOME w /\
  t.vs_alloca_next <= u.vs_alloca_next ==>
  w2n w + 64 <= u.vs_alloca_next
Proof
  Cases_on `v` >>
  simp[expr_store_bound_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, val_store_size_def, valueEncodingTheory.type_memory_size_def,
       vyperValueTheory.type_slot_size_def, wordsTheory.dimword_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `w` mp_tac) >> simp[]
QED

(* Restatement of private exprSimECArith.ec_point_footprint;
   proof from alan-ref/base/exprSimECArithScript.sml.txt. *)
Theorem ec_point_footprint:
  val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64
Proof
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

(* Restatement of private exprSimECArith.ec_point_operand_kept;
   proof from alan-ref/base/exprSimECArithScript.sml.txt. *)
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
  `?w. eval_operand x t = SOME w` by
    fs[expr_post_def, expr_val_rel_def] >>
  `eval_operand x u = SOME w` by metis_tac[] >>
  `expr_val_at cenv cx (expr_type e1) sa s1 es1 v1 x t` by
    gvs[expr_post_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  strip_tac
  >- (`expr_val_in_alloca cenv cx (expr_type e1) sa s1 es1 v1 x t` by
        (simp[expr_val_in_alloca_def, evaluate_type_def, is_word_type_def,
              type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
         qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
      drule_all expr_post_operand_kept_stable >> strip_tac >>
      drule expr_val_in_alloca_at >> strip_tac >>
      gvs[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
          type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
      metis_tac[]) >>
  conj_tac
  >- (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    expr_post_operand_local_kept >>
  simp[is_word_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disch_then irule >>
  simp[is_word_type_def, evaluate_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  conj_tac >- gvs[expr_post_def] >>
  qexistsl_tac [`b`, `n`, `sz`] >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`cenv`, `cx`, `env`, `es`, `n`, `w2n w - b`,
               `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`, `k`] mp_tac
    local_path_at_dynarray_apart >>
  simp[dynarray_free_fixed, dynarray_free_base, type_memory_size_def]) >>
  `local_region cenv es'.scopes u n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`t`, `s1`, `es1.scopes`] >> simp[] >>
     gvs[expr_post_def]) >>
  simp[expr_val_at_def, local_val_at_def, evaluate_type_def, is_word_type_def,
       type_slot_size_def, wordsTheory.dimword_def, ec_point_footprint] >>
  disj2_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

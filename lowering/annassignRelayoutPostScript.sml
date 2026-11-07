(* Runtime ownership boundary for a strictly widened aggregate result. *)
Theory annassignRelayoutPost
Ancestors
  exprSimAggregateChildren allocationPtr allocaSiteResource
  vyperTypeSystem valueEncoding loweringPosts vyperValue vyperMisc
  arithmetic loweringSlice exprLoweringProps words

Theorem arg_type_fits_zero_size_rigid:
  (!sty dty. arg_type_fits sty dty ==>
    !tenv tv. evaluate_type tenv sty = SOME tv /\
      type_memory_size tv = 0 ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys ==>
    !tenv tvs. OPT_MMAP (evaluate_type tenv) stys = SOME tvs /\
      type_memory_size_list tvs = 0 ==> stys = dtys)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[evaluate_type_def, evaluate_types_OPT_MMAP,
       type_memory_size_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[arg_type_fits_def, type_memory_size_def] >>
  metis_tac[]
QED

Theorem strict_widening_source_positive:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv ==>
  0 < type_memory_size stv
Proof
  simp[type_widens_to_def] >> rpt strip_tac >>
  Cases_on `type_memory_size stv = 0` >> simp[] >>
  metis_tac[cj 1 arg_type_fits_zero_size_rigid]
QED

Theorem expr_post_reserved_destination_source:
  !ctx func cenv cx e es sa sb s0 es' v op s sty stv
   did b cap dst dlen p dw.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    post_value_type cenv e = sty /\ sty <> expr_type e /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
    val_footprint stv v = type_memory_size stv /\
    FLOOKUP s0.vs_allocas did = SOME (b,cap) /\ did < sa.cs_next_id /\
    b <= dst /\ dst + dlen <= b + cap /\
    not_fresh_at sa p /\ lookup_var p s0 = SOME dw ==>
    ?sw. eval_operand op s = SOME sw /\
      val_in_memory stv v (w2n sw) s.vs_memory /\
      lookup_var p s = SOME dw /\
      FLOOKUP s.vs_allocas did = SOME (b,cap) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      dst + dlen < dimword (:256) /\
      (w2n sw + type_memory_size stv <= dst \/
       dst + dlen <= w2n sw)
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  gnvs[expr_post_def] >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `FLOOKUP s.vs_allocas did = SOME (b,cap)` by metis_tac[] >>
  `lookup_var p s = SOME dw` by metis_tac[] >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def] >>
  strip_tac >>
  `aid <> did` by decide_tac >>
  `w2n w + type_memory_size stv < dimword (:256) /\
   (w2n w + type_memory_size stv <= dst \/ dst + dlen <= w2n w)` by
    (irule aggregate_allocated_source_bounds >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [`b'`, `aid`, `b`, `did`, `cap`, `sz`] >> simp[]) >>
  `b + cap <= s.vs_alloca_next` by
    (irule alloca_site_registered_below >>
     fs[stmt_state_rel_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `dst + dlen < dimword (:256)` by decide_tac >>
  qexists_tac `w` >> simp[] >>
  fs[expr_val_rel_def]
QED

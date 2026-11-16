Theory bodyFullBopBytestringCuts
Ancestors
  exprBopLowering gasShadowCompile gasShadowCompileHelpers
  gasShadowCompileMembership gasShadowCompilePure gasShadowState
  exprLowering compileEnv gasShadow
Libs pairLib

Theorem bop_bytestring_selected_compile_cuts:
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  expr_type e2 = expr_type e1 /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  gas_shadow_state sa shadow_sa ==>
  ?h1 sh1 h2 sh2 shadow_sh1 shadow_sh2.
    (case bytestring_literal_hash e1 of
       NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e1) e1 sa))
       (SND (lower_value compile_expr cenv (expr_type e1) e1 sa))
     | SOME digest => (Lit digest,sa)) = (h1,sh1) /\
    (case bytestring_literal_hash e2 of
       NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e2) e2 sh1))
       (SND (lower_value compile_expr cenv (expr_type e2) e2 sh1))
     | SOME digest => (Lit digest,sh1)) = (h2,sh2) /\
    (case bytestring_literal_hash (gas_shadow_expr e1) of
       NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type (gas_shadow_expr e1))
           (gas_shadow_expr e1) shadow_sa))
       (SND (lower_value compile_expr cenv (expr_type (gas_shadow_expr e1))
           (gas_shadow_expr e1) shadow_sa))
     | SOME digest => (Lit digest,shadow_sa)) = (h1,shadow_sh1) /\
    (case bytestring_literal_hash (gas_shadow_expr e2) of
       NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type (gas_shadow_expr e2))
           (gas_shadow_expr e2) shadow_sh1))
       (SND (lower_value compile_expr cenv (expr_type (gas_shadow_expr e2))
           (gas_shadow_expr e2) shadow_sh1))
     | SOME digest => (Lit digest,shadow_sh1)) = (h2,shadow_sh2) /\
    gas_shadow_state sh1 shadow_sh1 /\ gas_shadow_state sh2 shadow_sh2 /\
    (if bop = Eq then emit_op EQ [h1;h2] sh2
     else emit_op ISZERO [FST (emit_op EQ [h1;h2] sh2)] (SND (emit_op EQ [h1;h2] sh2))) = (op,sb) /\
    (!m cb. bytestring_literal_hash e1 = NONE /\
      lower_value compile_expr cenv (expr_type e1) e1 sa = (m,cb) ==>
      ?shadow_cb. lower_value compile_expr cenv (expr_type e1)
        (gas_shadow_expr e1) shadow_sa = (m,shadow_cb) /\
        gas_shadow_state cb shadow_cb) /\
    (!m cb. bytestring_literal_hash e2 = NONE /\
      lower_value compile_expr cenv (expr_type e2) e2 sh1 = (m,cb) ==>
      ?shadow_cb. lower_value compile_expr cenv (expr_type e2)
        (gas_shadow_expr e2) shadow_sh1 = (m,shadow_cb) /\
        gas_shadow_state cb shadow_cb)
Proof
  strip_tac >> drule_at (Pos last) comparison_compile_cut >>
  simp[] >> strip_tac >>
  `!e cty a a' m cb. gas_shadow_state a a' /\
    lower_value compile_expr cenv cty e a = (m,cb) ==>
    ?cb'. lower_value compile_expr cenv cty (gas_shadow_expr e) a' =
      (m,cb') /\ gas_shadow_state cb cb'` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (cj 1 gas_shadow_compile_expr) >>
     disch_then (mp_tac o Q.INST [`ty` |-> `cty`, `sh` |-> `T`] o
       MATCH_MP gas_shadow_compiles_lower_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`, `a'`] mp_tac) >>
     simp[] >> Cases_on `lower_value compile_expr cenv cty
       (gas_shadow_expr e) a'` >> simp[] >> metis_tac[]) >>
  `!m cb cb' h sz. gas_shadow_state cb cb' /\
    compile_bytestring_hash m cb = (h,sz) ==>
    ?sz'. compile_bytestring_hash m cb' = (h,sz') /\ gas_shadow_state sz sz'` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`ptr_op` |-> `m`] gas_shadow_compiles_bytestring_hash) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`cb`, `cb'`] mp_tac) >>
     simp[] >> Cases_on `compile_bytestring_hash m cb'` >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`h1`, `sh1`, `h2`, `sh2`] >>
  Cases_on `bytestring_literal_hash e1` >>
  Cases_on `bytestring_literal_hash e2` >> gvs[] >>
  qpat_assum `!e ty a a' m cb. _` imp_res_tac >>
  qpat_assum `!m cb cb' h sz. _` imp_res_tac >>
  gvs[] >>
  qpat_assum `!e ty a a' m cb. _` imp_res_tac >>
  qpat_assum `!m cb cb' h sz. _` imp_res_tac >>
  gvs[] >> metis_tac[]
QED

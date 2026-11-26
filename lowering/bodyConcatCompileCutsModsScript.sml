(* Paired compiler cuts of a Concat loop iteration, independent of execution. *)
Theory bodyConcatCompileCutsMods
Ancestors
  bodyConcatCutsMods exprSimConcatPath exprSimFullBundleProps
  exprLowering exprLoweringProps fragExec
  gasShadow gasShadowState gasShadowCompileStmtHelpers
  compileEnv vyperAST list
Libs monadsyntax

Theorem concat_cons_unfold[local]:
  compile_concat compile_expr cenv (e::es) dp ((b,m)::infos) off sa = ((),sb) ==>
  ?op sc s2 arm.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sc) /\
    arm sc = ((),s2) /\
    compile_concat compile_expr cenv es dp infos off s2 = ((),sb) /\
    (!st. ci_mono st (SND (arm st))) /\ gas_shadow_compiles arm arm /\
    Abbrev (arm = if b then
      do arg_len <- emit_op MLOAD [op];
         arg_data <- emit_op ADD [op;Lit 32w];
         offset_op <- emit_op MLOAD [off];
         dst <- emit_op ADD [dp;offset_op];
         emit_void MCOPY [dst;arg_data;arg_len];
         new_offset <- emit_op ADD [offset_op;arg_len];
         emit_void MSTORE [off;new_offset]
      od
    else
      do offset_op <- emit_op MLOAD [off];
         dst <- emit_op ADD [dp;offset_op];
         emit_void MSTORE [dst;op];
         new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
         emit_void MSTORE [off;new_offset]
      od)
Proof
  Cases_on `b` >> simp[] >>
  (disch_then (strip_assume_tac o MATCH_MP compile_concat_bytes_cons) ORELSE
   disch_then (strip_assume_tac o MATCH_MP compile_concat_fixed_cons)) >>
  rename1 `lower_value _ _ _ _ _ = (op,sc)` >>
  rename1 `compile_concat _ _ es _ _ _ s2 = _` >>
  qexistsl_tac [`op`,`sc`,`s2`] >>
  qmatch_asmsub_abbrev_tac `(arm sc : unit # compile_state) = ((),s2)` >>
  qexists `arm` >> simp[] >>
  (conj_tac
   >- (simp[Abbr `arm`,comp_ignore_bind_def] >> rpt gen_tac >>
       rpt (irule ci_mono_bind >> simp[ci_mono_emit_op,ci_mono_emit_void] >> rpt gen_tac)) >>
   simp[Abbr `arm`,comp_ignore_bind_def] >>
   rpt (irule gas_shadow_compiles_bind >>
        simp[gas_shadow_compiles_emit_op,gas_shadow_compiles_emit_void] >> rpt gen_tac))
QED

Theorem concat_code_three_slices[local]:
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sb,ha,hb) /\
  gas_shadow_state sc hc /\ gas_shadow_state s2 h2 /\
  ci_mono sa sc /\ ci_mono sc s2 /\ ci_mono s2 sb /\
  ci_mono ha hc /\ ci_mono hc h2 /\ ci_mono h2 hb ==>
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sc,ha,hc) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sc,s2,hc,h2) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (s2,sb,h2,hb)
Proof
  simp[expr_sim_full_code_def,ci_mono_def] >> rpt strip_tac >>
  metis_tac[fn_has_code_split,cs_extends_trans]
QED

Theorem concat_shadow_cut[local]:
  gas_shadow_compiles f g /\ gas_shadow_state s h /\
  f s = (op,t) /\ g h = (hop,ht) ==>
  hop = op /\ gas_shadow_state t ht
Proof
  rw[gas_shadow_compiles_def] >>
  first_x_assum (qspecl_then [`s`,`h`] mp_tac) >> simp[]
QED

Theorem concat_compile_cut_mono[local]:
  (lower_value compile_expr cenv ty e sa = (op,sc) ==> ci_mono sa sc) /\
  (compile_concat compile_expr cenv es dp infos off s2 = ((),sb) ==> ci_mono s2 sb)
Proof
  `!ce xs dp infos off st.
     ci_mono st (SND (compile_concat compile_expr ce xs dp infos off st))` by
    simp[ci_mono_compile_concat_cfn,compile_expr_ci_mono] >>
  metis_tac[ci_mono_lower_value_compile_expr,pairTheory.SND]
QED

Theorem concat_cons_compile_cuts_mods:
  compile_concat compile_expr cenv (e::es) dp (concat_infos_mods (e::es)) off sa = ((),sb) /\
  compile_concat compile_expr (gas_shadow_env T cenv)
    (MAP gas_shadow_expr (e::es)) dp (concat_infos_mods (e::es)) off ha = ((),hb) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sb,ha,hb) /\
  (is_bytestring_type (expr_type e) \/ ?m. expr_type e = BaseT (BytesT (Fixed m))) ==>
  ?op sc hc s2 h2 arm.
    lower_value compile_expr cenv (expr_type e) e sa = (op,sc) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) ha =
      (op,hc) /\
    (if is_bytestring_type (expr_type e) then
       arm = (do arg_len <- emit_op MLOAD [op];
                 arg_data <- emit_op ADD [op;Lit 32w];
                 offset_op <- emit_op MLOAD [off];
                 dst <- emit_op ADD [dp;offset_op];
                 emit_void MCOPY [dst;arg_data;arg_len];
                 new_offset <- emit_op ADD [offset_op;arg_len];
                 emit_void MSTORE [off;new_offset]
              od)
     else ?m. expr_type e = BaseT (BytesT (Fixed m)) /\
       arm = (do offset_op <- emit_op MLOAD [off];
                 dst <- emit_op ADD [dp;offset_op];
                 emit_void MSTORE [dst;op];
                 new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
                 emit_void MSTORE [off;new_offset]
              od)) /\
    arm sc = ((),s2) /\ arm hc = ((),h2) /\
    compile_concat compile_expr cenv es dp (concat_infos_mods es) off s2 = ((),sb) /\
    compile_concat compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es) dp
      (concat_infos_mods es) off h2 = ((),hb) /\
    ci_mono sa sc /\ ci_mono sc s2 /\ ci_mono s2 sb /\
    ci_mono ha hc /\ ci_mono hc h2 /\ ci_mono h2 hb /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sc,ha,hc) /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (sc,s2,hc,h2) /\
    expr_sim_full_code (ctx,hctx,func,hfunc) (s2,sb,h2,hb)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?b m. concat_infos_mods (e::es) = (b,m)::concat_infos_mods es /\
         b = is_bytestring_type (expr_type e) /\
         (~b ==> expr_type e = BaseT (BytesT (Fixed m)))` by
    (Cases_on `is_bytestring_type (expr_type e)` >>
     gvs[concat_infos_mods_def,is_bytestring_type_def]) >>
  qpat_x_assum `concat_infos_mods (e::es) = _` SUBST_ALL_TAC >>
  qpat_x_assum `compile_concat _ _ (e::es) _ _ _ sa = _`
    (strip_assume_tac o MATCH_MP concat_cons_unfold) >>
  qpat_x_assum `compile_concat _ _ (MAP gas_shadow_expr (e::es)) _ _ _ ha = _`
    (strip_assume_tac o MATCH_MP concat_cons_unfold o REWRITE_RULE [listTheory.MAP]) >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr e) ha = _`
    (assume_tac o REWRITE_RULE [gas_shadow_expr_type]) >>
  rename1 `lower_value _ cenv _ e sa = (op,sc)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) ha = (hop,hc)` >>
  rename1 `compile_concat _ _ es _ _ _ s2 = _` >>
  rename1 `compile_concat _ _ (MAP gas_shadow_expr es) _ _ _ h2 = _` >>
  rename1 `arm sc = ((),s2)` >> rename1 `harm hc = ((),h2)` >>
  `gas_shadow_state sa ha` by (drule expr_sim_full_code_fields >> simp[]) >>
  `hop = op /\ gas_shadow_state sc hc` by
    (irule concat_shadow_cut >>
     qexistsl_tac [`lower_value compile_expr cenv (expr_type e) e`,
                   `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)`,
                   `ha`,`sa`] >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `hop = op` SUBST_ALL_TAC >>
  `harm = arm` by (simp[Abbr `arm`,Abbr `harm`]) >>
  qpat_x_assum `harm = arm` SUBST_ALL_TAC >>
  `gas_shadow_state s2 h2` by (drule_all concat_shadow_cut >> simp[]) >>
  imp_res_tac concat_compile_cut_mono >>
  `ci_mono sc s2 /\ ci_mono hc h2` by metis_tac[pairTheory.SND] >>
  `expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sc,ha,hc) /\
   expr_sim_full_code (ctx,hctx,func,hfunc) (sc,s2,hc,h2) /\
   expr_sim_full_code (ctx,hctx,func,hfunc) (s2,sb,h2,hb)` by
    (irule concat_code_three_slices >> simp[]) >>
  qexistsl_tac [`op`,`sc`,`hc`,`s2`,`h2`,`arm`] >>
  Cases_on `b` >> gvs[] >> metis_tac[]
QED

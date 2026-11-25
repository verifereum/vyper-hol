Theory s1PrefixStructLitCodeCut
Ancestors
  compileEnv exprLowering exprLoweringProps exprSimFullBundleProps fragExec
  gasShadowCompile gasShadowCompileHelpers gasShadowState

Theorem structlit_cons_cut[local]:
  compile_struct_lit compile_expr ce (StructT nsid) ((fname,e)::fs) buf off si =
    (out,sb) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,type_memory_bytes ce fty) ==>
  ?vv sm ss.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_struct_lit compile_expr ce (StructT nsid) [(fname,e)] buf off si =
      (buf,ss) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf
      (off + type_memory_bytes ce fty) ss = (out,sb) /\
    ci_mono si sm /\ ci_mono sm ss /\ ci_mono ss sb
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e si` >>
  rename1 `compile_expr ce (expr_type e) e si = (vv,sm)` >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] sm` >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  Cases_on `unwrap_value ce vv sn` >>
  rename1 `unwrap_value ce vv sn = (src,su)` >>
  Cases_on `compile_store_memory ce src dst fty (lowered_value_type ce e) su` >>
  rename1 `compile_store_memory _ _ _ _ _ su = (_,ss)` >>
  qpat_x_assum `compile_struct_lit _ _ _ (_::_) _ _ _ = _` mp_tac >>
  simp[Once compile_struct_lit_def, comp_ignore_bind_def, comp_bind_def] >>
  strip_tac >> qexists_tac `ss` >>
  simp[compile_struct_lit_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  conj_tac
  >- (qspecl_then [`ce`,`expr_type e`,`e`,`si`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  conj_tac
  >- (qspecl_then [`ADD`,`[buf; Lit (n2w off)]`,`sm`] mp_tac ci_mono_emit_op >>
      qspecl_then [`ce`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >>
      qspecl_then [`ce`,`src`,`dst`,`fty`,`lowered_value_type ce e`,`su`]
        mp_tac ci_mono_compile_store_memory >>
      simp[] >> metis_tac[ci_mono_trans]) >>
  qspecl_then [`compile_expr`,`ce`,`StructT nsid`,`fs`,`buf`,
      `off + type_memory_bytes ce fty`,`ss`] mp_tac ci_mono_compile_struct_lit_cfn >>
  simp[compile_expr_ci_mono]
QED

Theorem structlit_cons_code_cut:
  compile_struct_lit compile_expr ce (StructT nsid) ((fname,e)::fs) (Var root) off si = (out,sb) /\
  compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
    (MAP (I ## gas_shadow_expr) ((fname,e)::fs)) (Var root) off shadow_si = (out,shadow_sb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sb,shadow_si,shadow_sb) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,type_memory_bytes ce fty) ==>
  ?vv sm shadow_sm ss shadow_ss.
    compile_expr ce (expr_type e) e si = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_si =
      (vv,shadow_sm) /\
    compile_struct_lit compile_expr ce (StructT nsid) [(fname,e)] (Var root) off si =
      (Var root,ss) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) [(fname,e)]) (Var root) off shadow_si = (Var root,shadow_ss) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs (Var root)
      (off + type_memory_bytes ce fty) ss = (out,sb) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) (Var root)
      (off + type_memory_bytes ce fty) shadow_ss = (out,shadow_sb) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,sm,shadow_si,shadow_sm) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,ss,shadow_si,shadow_ss) /\
    expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (ss,sb,shadow_ss,shadow_sb) /\
    ci_mono si sm /\ ci_mono sm ss /\ ci_mono ss sb /\
    ci_mono shadow_si shadow_sm /\ ci_mono shadow_sm shadow_ss /\ ci_mono shadow_ss shadow_sb
Proof
  strip_tac >>
  drule_all structlit_cons_cut >> strip_tac >>
  `compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
     ((fname,gas_shadow_expr e)::MAP (I ## gas_shadow_expr) fs)
     (Var root) off shadow_si = (out,shadow_sb)` by fs[] >>
  `ALOOKUP (get_struct_fields (gas_shadow_env T ce).ce_struct_fields (nsid_to_string nsid)) fname =
     SOME (fty,type_memory_bytes (gas_shadow_env T ce) fty)` by simp[] >>
  qpat_assum `compile_struct_lit _ _ _ ((fname,gas_shadow_expr e)::_)
                _ _ shadow_si = (_,shadow_sb)`
    (fn th => mp_tac (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] structlit_cons_cut) th)) >>
  simp[gasShadowTheory.gas_shadow_expr_type] >> strip_tac >>
  qpat_assum `expr_sim_full_code _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
     (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`T`] mp_tac
       (Q.INST [`sd` |-> `T`] (cj 1 gas_shadow_compile_expr_env)) >> simp[]) >>
  `gas_shadow_compiles (compile_struct_lit compile_expr ce (StructT nsid) [(fname,e)] (Var root) off)
     (compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
       (MAP (I ## gas_shadow_expr) [(fname,e)]) (Var root) off)` by
    (irule (REWRITE_RULE [COND_CLAUSES] (Q.INST [`sh` |-> `T`] gas_shadow_compiles_struct_lit)) >>
     simp[gas_shadow_compile_expr_env]) >>
  qpat_x_assum `gas_shadow_compiles (compile_expr _ _ _) _`
    (qspecl_then [`si`,`shadow_si`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  qpat_x_assum `gas_shadow_compiles (compile_struct_lit _ _ _ _ _ _) _`
    (qspecl_then [`si`,`shadow_si`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> rpt strip_tac >>
  fs[expr_sim_full_code_def, ci_mono_def] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

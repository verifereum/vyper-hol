(* Paired compiler cuts for a linked struct literal and its ordered fields. *)
Theory bodyStructFieldsCompileMods
Ancestors
  exprSimAggregateLayout exprSimFullBundleProps exprOperandVar
  stmtLoweringMono gasShadowCompile gasShadowCompileContext
  gasShadowCompileConvert gasShadowCompilePure gasShadowCompileBase
  gasShadowState gasShadow exprLowering exprLoweringProps compileEnv fragExec
  list pair alist context vyperAST venomInst


Theorem shadow_compiler_result[local]:
  gas_shadow_compiles f g /\ gas_shadow_state a a' /\ f a = (v,b) ==>
  ?b'. g a' = (v,b') /\ gas_shadow_state b b'
Proof
  simp[gas_shadow_compiles_def] >> strip_tac >>
  first_x_assum drule >> Cases_on `g a'` >> simp[]
QED

Theorem struct_fields_ci_mono[local]:
  compile_struct_lit compile_expr ce ty fs buf off a = (v,b) ==>
  ci_mono a b
Proof
  strip_tac >>
  `ci_mono a (SND (compile_struct_lit compile_expr ce ty fs buf off a))` by
    (irule ci_mono_compile_struct_lit_cfn >> simp[ci_mono_compile_expr_sa]) >>
  qpat_x_assum `ci_mono _ (SND _)` mp_tac >> simp[]
QED

Theorem code_split_at_ci_mono[local]:
  ci_mono a b /\ ci_mono b c /\ fn_has_code a c f ==>
  fn_has_code a b f /\ fn_has_code b c f
Proof
  simp[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem struct_literal_paired_compile:
  compile_expr ce ty (StructLit ann nsid fs) a = (vv,b) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (StructLit ann nsid fs)) a' = (vv,b') /\
  expr_sim_full_code (ctx,shctx,f,f') (a,b,a',b') /\
  n = SUM (MAP (SND o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) ==>
  ?ba m m'.
    compile_alloc_buffer n a = (ba,m) /\
    compile_alloc_buffer n a' = (ba,m') /\
    vv = LocatedValue (expr_type (StructLit ann nsid fs)) (base_ptr ba) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs ba.buf_operand 0 m =
      (ba.buf_operand,b) /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) ba.buf_operand 0 m' = (ba.buf_operand,b') /\
    expr_sim_full_code (ctx,shctx,f,f') (a,m,a',m') /\
    expr_sim_full_code (ctx,shctx,f,f') (m,b,m',b') /\
    ci_mono a m /\ ci_mono m b /\ ci_mono a' m' /\ ci_mono m' b'
Proof
  strip_tac >>
  drule_then (qx_choosel_then [`ba`,`m`,`u`] strip_assume_tac) compile_struct_literal_inv >>
  qpat_x_assum `expr_sim_full_code _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  `?m'. compile_alloc_buffer n a' = (ba,m') /\ gas_shadow_state m m'` by
    (irule shadow_compiler_result >>
     irule_at Any gas_shadow_compiles_alloc_buffer >> qexists_tac `a` >> simp[]) >>
  `u = ba.buf_operand` by metis_tac[compiler_struct_lit_result] >>
  `compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) ba.buf_operand 0 m' = (ba.buf_operand,b')` by
    (qpat_assum `n = SUM _` (fn sz =>
       qpat_assum `compile_alloc_buffer n a' = _` (assume_tac o REWRITE_RULE [sz])) >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, compile_struct_literal] >>
     Cases_on `compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
       (MAP (I ## gas_shadow_expr) fs) ba.buf_operand 0 m'` >>
     drule_then assume_tac compiler_struct_lit_result >> simp[]) >>
  `ci_mono a m /\ ci_mono a' m'` by
    (mp_tac (Q.SPECL [`n`,`a`] ci_mono_compile_alloc_buffer) >>
     mp_tac (Q.SPECL [`n`,`a'`] ci_mono_compile_alloc_buffer) >> simp[]) >>
  qpat_assum `compile_struct_lit _ _ _ _ _ _ m = _`
    (mp_then Any assume_tac struct_fields_ci_mono) >>
  qpat_assum `compile_struct_lit _ _ _ _ _ _ m' = _`
    (mp_then Any assume_tac struct_fields_ci_mono) >>
  qpat_assum `fn_has_code a b f`
    (mp_then Any (drule_all_then strip_assume_tac) code_split_at_ci_mono) >>
  qpat_assum `fn_has_code a' b' f'`
    (mp_then Any (drule_all_then strip_assume_tac) code_split_at_ci_mono) >>
  qexistsl [`ba`,`m`,`m'`] >> simp[expr_sim_full_code_def]
QED

Theorem struct_field_cons_compile[local]:
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name = SOME (fty,n) /\
  compile_struct_lit compile_expr ce (StructT nsid) ((name,e)::fs) buf off a = (out,b) ==>
  ?vv m dst j opn u v p.
    compile_expr ce (expr_type e) e a = (vv,m) /\
    emit_op ADD [buf; Lit (n2w off)] m = (dst,j) /\
    unwrap_value ce vv j = (opn,u) /\
    compile_store_memory ce opn dst fty (lowered_value_type ce e) u = (v,p) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf (off+n) p = (out,b) /\
    ci_mono a m /\ ci_mono m j /\ ci_mono j u /\ ci_mono u p /\ ci_mono p b
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e a` >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,m)` >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] m` >>
  rename1 `emit_op ADD _ m = (dst,j)` >>
  Cases_on `unwrap_value ce vv j` >>
  rename1 `unwrap_value ce vv j = (opn,u)` >>
  Cases_on `compile_store_memory ce opn dst fty (lowered_value_type ce e) u` >>
  rename1 `compile_store_memory ce opn dst fty _ u = (v,p)` >>
  qpat_x_assum `compile_struct_lit _ _ _ ((name,e)::fs) _ _ _ = _` mp_tac >>
  simp[Once compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def] >> strip_tac >>
  conj_tac >- (qspec_then `ce` mp_tac (cj 1 ci_mono_compile_expr_sa) >>
    disch_then (qspecl_then [`expr_type e`,`e`,`a`] mp_tac) >> simp[]) >>
  conj_tac >- (mp_tac (Q.SPECL [`ADD`,`[buf; Lit (n2w off)]`,`m`] ci_mono_emit_op) >> simp[]) >>
  conj_tac >- (mp_tac (Q.SPECL [`ce`,`vv`,`j`] ci_mono_unwrap_value) >> simp[]) >>
  conj_tac >- (mp_tac (Q.SPECL [`ce`,`opn`,`dst`,`fty`,`lowered_value_type ce e`,`u`]
    ci_mono_compile_store_memory) >> simp[]) >>
  qpat_assum `compile_struct_lit _ _ _ fs _ _ p = _`
    (mp_then Any ACCEPT_TAC struct_fields_ci_mono)
QED

Theorem struct_field_shadow_prefix[local]:
  compile_expr ce (expr_type e) e a = (vv,m) /\
  emit_op ADD [buf; Lit (n2w off)] m = (dst,j) /\
  unwrap_value ce vv j = (opn,u) /\
  compile_store_memory ce opn dst fty (lowered_value_type ce e) u = (v,p) /\
  gas_shadow_state a a' ==>
  ?m' j' u' p'.
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) a' = (vv,m') /\
    emit_op ADD [buf; Lit (n2w off)] m' = (dst,j') /\
    unwrap_value ce vv j' = (opn,u') /\
    compile_store_memory ce opn dst fty (lowered_value_type ce e) u' = (v,p') /\
    gas_shadow_state m m' /\ gas_shadow_state j j' /\
    gas_shadow_state u u' /\ gas_shadow_state p p'
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
     (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`T`] mp_tac
      (cj 1 (Q.INST [`sd` |-> `T`] gas_shadow_compile_expr_env)) >> simp[]) >>
  drule_all_then (qx_choose_then `m'` strip_assume_tac) shadow_compiler_result >>
  `?j'. emit_op ADD [buf; Lit (n2w off)] m' = (dst,j') /\ gas_shadow_state j j'` by
    (irule shadow_compiler_result >> irule_at Any gas_shadow_compiles_emit_op_same >>
     qexists_tac `m` >> simp[]) >>
  `?u'. unwrap_value ce vv j' = (opn,u') /\ gas_shadow_state u u'` by
    (irule shadow_compiler_result >> irule_at Any gas_shadow_compiles_unwrap_value >>
     qexists_tac `j` >> simp[]) >>
  `?p'. compile_store_memory ce opn dst fty (lowered_value_type ce e) u' = (v,p') /\
        gas_shadow_state p p'` by
    (irule shadow_compiler_result >> irule_at Any gas_shadow_compiles_store_memory >>
     qexists_tac `u` >> simp[]) >>
  qexistsl [`m'`,`j'`,`u'`,`p'`] >> simp[]
QED

Theorem struct_field_code_slices[local]:
  ci_mono a m /\ ci_mono m j /\ ci_mono j u /\ ci_mono u p /\ ci_mono p b /\
  fn_has_code a b f ==>
  fn_has_code a m f /\ fn_has_code m j f /\ fn_has_code j u f /\
  fn_has_code u p f /\ fn_has_code p b f
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends a p /\ cs_extends m u` by metis_tac[cs_extends_trans] >>
  `fn_has_code a p f /\ fn_has_code p b f` by metis_tac[fn_has_code_split] >>
  `cs_extends a u` by metis_tac[cs_extends_trans] >>
  `fn_has_code a u f /\ fn_has_code u p f` by metis_tac[fn_has_code_split] >>
  `fn_has_code a m f /\ fn_has_code m u f` by metis_tac[fn_has_code_split] >>
  simp[] >> metis_tac[fn_has_code_split]
QED

Theorem struct_field_cons_paired_compile:
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name = SOME (fty,n) /\
  compile_struct_lit compile_expr ce (StructT nsid) ((name,e)::fs) buf off a = (out,b) /\
  compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
    (MAP (I ## gas_shadow_expr) ((name,e)::fs)) buf off a' = (out,b') /\
  expr_sim_full_code (ctx,shctx,f,f') (a,b,a',b') ==>
  ?vv m dst j opn u v p m' j' u' p'.
    compile_expr ce (expr_type e) e a = (vv,m) /\
    emit_op ADD [buf; Lit (n2w off)] m = (dst,j) /\
    unwrap_value ce vv j = (opn,u) /\
    compile_store_memory ce opn dst fty (lowered_value_type ce e) u = (v,p) /\
    compile_struct_lit compile_expr ce (StructT nsid) fs buf (off+n) p = (out,b) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) a' = (vv,m') /\
    emit_op ADD [buf; Lit (n2w off)] m' = (dst,j') /\
    unwrap_value ce vv j' = (opn,u') /\
    compile_store_memory ce opn dst fty (lowered_value_type ce e) u' = (v,p') /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf (off+n) p' = (out,b') /\
    ci_mono a m /\ ci_mono m j /\ ci_mono j u /\ ci_mono u p /\ ci_mono p b /\
    ci_mono a' m' /\ ci_mono m' j' /\ ci_mono j' u' /\ ci_mono u' p' /\ ci_mono p' b' /\
    expr_sim_full_code (ctx,shctx,f,f') (a,m,a',m') /\
    expr_sim_full_code (ctx,shctx,f,f') (m,j,m',j') /\
    expr_sim_full_code (ctx,shctx,f,f') (j,u,j',u') /\
    expr_sim_full_code (ctx,shctx,f,f') (u,p,u',p') /\
    expr_sim_full_code (ctx,shctx,f,f') (p,b,p',b')
Proof
  strip_tac >>
  drule_all_then (qx_choosel_then [`vv`,`m`,`dst`,`j`,`opn`,`u`,`v`,`p`] strip_assume_tac)
    struct_field_cons_compile >>
  qpat_x_assum `expr_sim_full_code _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_code_def]) >>
  drule_all_then (qx_choosel_then [`m'`,`j'`,`u'`,`p'`] strip_assume_tac) struct_field_shadow_prefix >>
  `ALOOKUP (get_struct_fields (gas_shadow_env T ce).ce_struct_fields (nsid_to_string nsid))
      name = SOME (fty,n)` by simp[] >>
  `ci_mono a' m' /\ ci_mono m' j' /\ ci_mono j' u' /\ ci_mono u' p' /\ ci_mono p' b' /\
    compile_struct_lit compile_expr (gas_shadow_env T ce) (StructT nsid)
      (MAP (I ## gas_shadow_expr) fs) buf (off+n) p' = (out,b')` by
    (qpat_x_assum `compile_struct_lit _ (gas_shadow_env T ce) _ _ _ _ a' = _` mp_tac >>
     simp[Once compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def,
          gas_shadow_expr_type] >> strip_tac >> simp[] >>
     conj_tac >- (qspec_then `gas_shadow_env T ce` mp_tac (cj 1 ci_mono_compile_expr_sa) >>
       disch_then (qspecl_then [`expr_type e`,`gas_shadow_expr e`,`a'`] mp_tac) >> simp[]) >>
     conj_tac >- (mp_tac (Q.SPECL [`ADD`,`[buf; Lit (n2w off)]`,`m'`] ci_mono_emit_op) >> simp[]) >>
     conj_tac >- (mp_tac (Q.SPECL [`ce`,`vv`,`j'`] ci_mono_unwrap_value) >> simp[]) >>
     conj_tac >- (mp_tac (Q.SPECL [`ce`,`opn`,`dst`,`fty`,`lowered_value_type ce e`,`u'`]
       ci_mono_compile_store_memory) >> simp[]) >>
     qpat_assum `compile_struct_lit _ _ _ _ _ _ p' = _`
       (mp_then Any ACCEPT_TAC struct_fields_ci_mono)) >>
  qpat_assum `fn_has_code a b f`
    (mp_then Any (drule_all_then strip_assume_tac) struct_field_code_slices) >>
  qpat_assum `fn_has_code a' b' f'`
    (mp_then Any (drule_all_then strip_assume_tac) struct_field_code_slices) >>
  qexistsl [`vv`,`m`,`dst`,`j`,`opn`,`u`,`v`,`p`,`m'`,`j'`,`u'`,`p'`] >>
  simp[expr_sim_full_code_def]
QED

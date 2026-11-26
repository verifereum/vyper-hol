(* Compilation boundaries for the allocation, operand fold and header write. *)
Theory bodyConcatOuterCodeMods
Ancestors
  bodyConcatCutsMods exprSimConcatResult exprSimFullBundleProps
  exprLoweringProps fragExec compileEnv context venomInst
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileContext
  gasShadow gasShadowState

Theorem concat_outer_shape[local]:
  compile_expr cenv ty (Builtin a (Concat n) args) sa = (vv,sb) ==>
  ?buf s1 dp s2 ob s3 s4 s5 fo s6.
    context$compile_alloc_buffer (concat_alloc_size (MAP expr_type args)) sa = (buf,s1) /\
    emit_op ADD [buf.buf_operand;Lit 32w] s1 = (dp,s2) /\
    context$compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [ob.buf_operand;Lit 0w] s3 = ((),s4) /\
    compile_concat compile_expr cenv args dp (concat_infos_mods args) ob.buf_operand s4 = ((),s5) /\
    emit_op MLOAD [ob.buf_operand] s5 = (fo,s6) /\
    emit_void MSTORE [buf.buf_operand;fo] s6 = ((),sb) /\
    vv = LocatedValue a (base_ptr buf)
Proof
  disch_then (strip_assume_tac o MATCH_MP concat_compile_shape) >>
  rename1 `emit_void MSTORE [_;Lit 0w] _ = (u,_)` >>
  rename1 `emit_void MSTORE [_;_] _ = (v,sb)` >>
  Cases_on `u` >> Cases_on `v` >> fs[concat_infos_mods_def] >>
  metis_tac[]
QED

Theorem concat_outer_shadow_maps[local]:
  MAP expr_type (MAP gas_shadow_expr args) = MAP expr_type args /\
  concat_infos_mods (MAP gas_shadow_expr args) = concat_infos_mods args
Proof
  simp[concat_infos_mods_def,listTheory.MAP_MAP_o,combinTheory.o_DEF,
       gas_shadow_expr_type,ETA_AX]
QED

Theorem concat_outer_shadow_step[local]:
  gas_shadow_state s h /\ f s = (x,t) /\ g h = (y,ht) /\ gas_shadow_compiles f g ==>
  y = x /\ gas_shadow_state t ht
Proof
  simp[gas_shadow_compiles_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`s`,`h`] mp_tac) >> simp[]
QED

Theorem concat_outer_shadow_loop[local]:
  gas_shadow_compiles (compile_concat compile_expr cenv args dp infos off)
    (compile_concat compile_expr (gas_shadow_env T cenv)
       (MAP gas_shadow_expr args) dp infos off)
Proof
  irule (SIMP_RULE bool_ss [COND_CLAUSES]
    (Q.INST [`sh` |-> `T`, `sd` |-> `T`] gas_shadow_compiles_concat_env)) >>
  irule (cj 1 gas_shadow_compile_expr_env)
QED

Theorem concat_outer_slices[local]:
  fn_has_code sa sb func /\
  cs_extends sa s4 /\ cs_extends s4 s5 /\ cs_extends s5 sb ==>
  fn_has_code sa s4 func /\ fn_has_code s4 s5 func /\ fn_has_code s5 sb func
Proof
  strip_tac >> `cs_extends s4 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem concat_outer_layout[local]:
  context$compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand;Lit 32w] s1 = (dp,s2) /\
  context$compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand;Lit 0w] s3 = ((),s4) /\
  compile_concat compile_expr cenv args dp infos ob.buf_operand s4 = ((),s5) /\
  emit_op MLOAD [ob.buf_operand] s5 = (fo,s6) /\
  emit_void MSTORE [buf.buf_operand;fo] s6 = ((),sb) /\
  fn_has_code sa sb func ==>
  let bv = STRING #"%" (toString sa.cs_next_var);
      dv = STRING #"%" (toString (sa.cs_next_var+1));
      ov = STRING #"%" (toString (sa.cs_next_var+2));
      binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)] [bv];
      oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w] [ov] in
    buf.buf_operand = Var bv /\ dp = Var dv /\ ob.buf_operand = Var ov /\
    s4.cs_next_var = sa.cs_next_var+3 /\ s4.cs_next_id = sa.cs_next_id+4 /\
    sb.cs_next_var = s5.cs_next_var+1 /\ sb.cs_next_id = s5.cs_next_id+2 /\
    ci_mono s4 s5 /\
    emitted_insts sa s4 =
      [binst; mk_inst (sa.cs_next_id+1) ADD [Var bv;Lit 32w] [dv];
       oinst; mk_inst (sa.cs_next_id+3) MSTORE [Var ov;Lit 0w] []] /\
    emitted_insts s5 sb =
      [mk_inst s5.cs_next_id MLOAD [Var ov] [STRING #"%" (toString s5.cs_next_var)];
       mk_inst (s5.cs_next_id+1) MSTORE
         [Var bv;Var (STRING #"%" (toString s5.cs_next_var))] []] /\
    fn_has_code sa s4 func /\ fn_has_code s4 s5 func /\ fn_has_code s5 sb func /\
    MEM binst (fn_insts func) /\ MEM oinst (fn_insts func)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all concat_prefix_code >> strip_tac >> gvs[] >>
  drule_all concat_suffix_code >> strip_tac >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ s4 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[ci_mono_compile_concat_cfn, cj 1 compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa s4 /\ cs_extends s5 sb` by
    (conj_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends s4 s5` by fs[ci_mono_def] >>
  drule_all concat_outer_slices >> strip_tac >> simp[] >>
  conj_tac >> irule concat_code_mem >>
  qexistsl_tac [`sa`,`s4`] >> simp[]
QED

Theorem concat_outer_code_mods:
  compile_expr cenv ty (Builtin a (Concat n) args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin a (Concat n) args)) ha = (hvv,hb) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,sb,ha,hb) ==>
  ?buf ob bv dv ov s1 s2 s3 s4 s5 s6 h1 h2 h3 h4 h5 h6 fo binst oinst.
    let bsz = concat_alloc_size (MAP expr_type args) in
    vv = LocatedValue a (base_ptr buf) /\ hvv = vv /\
    buf.buf_operand = Var bv /\ ob.buf_operand = Var ov /\
    bv = STRING #"%" (toString sa.cs_next_var) /\
    dv = STRING #"%" (toString (sa.cs_next_var+1)) /\
    ov = STRING #"%" (toString (sa.cs_next_var+2)) /\
    context$compile_alloc_buffer bsz sa = (buf,s1) /\
    emit_op ADD [Var bv;Lit 32w] s1 = (Var dv,s2) /\
    context$compile_alloc_buffer 64 s2 = (ob,s3) /\
    emit_void MSTORE [Var ov;Lit 0w] s3 = ((),s4) /\
    emit_op MLOAD [Var ov] s5 = (fo,s6) /\
    emit_void MSTORE [Var bv;fo] s6 = ((),sb) /\
    context$compile_alloc_buffer bsz ha = (buf,h1) /\
    emit_op ADD [Var bv;Lit 32w] h1 = (Var dv,h2) /\
    context$compile_alloc_buffer 64 h2 = (ob,h3) /\
    emit_void MSTORE [Var ov;Lit 0w] h3 = ((),h4) /\
    emit_op MLOAD [Var ov] h5 = (fo,h6) /\
    emit_void MSTORE [Var bv;fo] h6 = ((),hb) /\
    (!ow B. concat_loop_code_mods (ctx,hctx,func,hfunc) cenv
      (dv,ov,ow,binst,oinst,B,bsz) args (s4,s5,h4,h5)) /\
    ci_mono s4 s5 /\ ci_mono h4 h5 /\
    fn_has_code sa s4 func /\ fn_has_code s4 s5 func /\ fn_has_code s5 sb func /\
    fn_has_code ha h4 hfunc /\ fn_has_code h4 h5 hfunc /\ fn_has_code h5 hb hfunc /\
    s4.cs_next_var = sa.cs_next_var+3 /\ s4.cs_next_id = sa.cs_next_id+4 /\
    sb.cs_next_var = s5.cs_next_var+1 /\ sb.cs_next_id = s5.cs_next_id+2 /\
    h4.cs_next_var = ha.cs_next_var+3 /\ h4.cs_next_id = ha.cs_next_id+4 /\
    hb.cs_next_var = h5.cs_next_var+1 /\ hb.cs_next_id = h5.cs_next_id+2 /\
    binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)] [bv] /\
    oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w] [ov] /\
    MEM binst (fn_insts func) /\ MEM oinst (fn_insts func) /\
    emitted_insts sa s4 =
      [binst; mk_inst (sa.cs_next_id+1) ADD [Var bv;Lit 32w] [dv];
       oinst; mk_inst (sa.cs_next_id+3) MSTORE [Var ov;Lit 0w] []] /\
    emitted_insts s5 sb =
      [mk_inst s5.cs_next_id MLOAD [Var ov] [STRING #"%" (toString s5.cs_next_var)];
       mk_inst (s5.cs_next_id+1) MSTORE
         [Var bv;Var (STRING #"%" (toString s5.cs_next_var))] []] /\
    emitted_insts ha h4 = emitted_insts sa s4 /\ emitted_insts h5 hb = emitted_insts s5 sb
Proof
  strip_tac >>
  qpat_assum `compile_expr _ _ (Builtin _ (Concat _) _) _ = _`
    (strip_assume_tac o MATCH_MP concat_outer_shape) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def,gas_shadow_builtin_def]) >>
  disch_then (mp_tac o MATCH_MP concat_outer_shape) >>
  simp_tac bool_ss [concat_outer_shadow_maps] >>
  disch_then (qx_choosel_then [`hbuf`,`h1`,`hdp`,`h2`,`hob`,`h3`,`h4`,`h5`,`hfo`,`h6`]
    (map_every assume_tac o CONJUNCTS)) >>
  fs[expr_sim_full_code_def] >>
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `hbuf = buf /\ gas_shadow_state s1 h1` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`context$compile_alloc_buffer bsz`,
                   `context$compile_alloc_buffer bsz`,`ha`,`sa`] >>
     simp[gas_shadow_compiles_alloc_buffer]) >>
  qpat_x_assum `hbuf = buf` SUBST_ALL_TAC >>
  `hdp = dp /\ gas_shadow_state s2 h2` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`emit_op ADD [buf.buf_operand;Lit 32w]`,
                   `emit_op ADD [buf.buf_operand;Lit 32w]`,`h1`,`s1`] >> simp[]) >>
  qpat_x_assum `hdp = dp` SUBST_ALL_TAC >>
  `hob = ob /\ gas_shadow_state s3 h3` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`context$compile_alloc_buffer 64`,
                   `context$compile_alloc_buffer 64`,`h2`,`s2`] >>
     simp[gas_shadow_compiles_alloc_buffer]) >>
  qpat_x_assum `hob = ob` SUBST_ALL_TAC >>
  `() = () /\ gas_shadow_state s4 h4` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`emit_void MSTORE [ob.buf_operand;Lit 0w]`,
                   `emit_void MSTORE [ob.buf_operand;Lit 0w]`,`h3`,`s3`] >>
     simp[gas_shadow_compiles_emit_void]) >>
  `() = () /\ gas_shadow_state s5 h5` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`compile_concat compile_expr cenv args dp (concat_infos_mods args) ob.buf_operand`,
       `compile_concat compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args)
         dp (concat_infos_mods args) ob.buf_operand`,`h4`,`s4`] >>
     simp[concat_outer_shadow_loop]) >>
  `hfo = fo /\ gas_shadow_state s6 h6` by
    (irule concat_outer_shadow_step >>
     qexistsl_tac [`emit_op MLOAD [ob.buf_operand]`,`emit_op MLOAD [ob.buf_operand]`,`h5`,`s5`] >>
     simp[]) >>
  qpat_x_assum `hfo = fo` SUBST_ALL_TAC >>
  qpat_assum `compile_concat _ cenv args _ _ _ s4 = _`
    (mp_then Any mp_tac concat_outer_layout) >>
  disch_then (drule_all_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [LET_THM])) >>
  qpat_assum `compile_concat _ (gas_shadow_env T cenv) _ _ _ _ h4 = _`
    (mp_then Any mp_tac concat_outer_layout) >>
  disch_then (drule_all_then (map_every assume_tac o CONJUNCTS o REWRITE_RULE [LET_THM])) >>
  qpat_assum `gas_shadow_state sa ha` (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
  qpat_assum `gas_shadow_state s5 h5` (strip_assume_tac o REWRITE_RULE [gas_shadow_state_def]) >>
  qexistsl_tac [`ob`,`s2`,`s3`,`s4`,`s5`,`s6`,`h2`,`h3`,`h4`,`h5`,`h6`,`fo`] >>
  fs[concat_loop_code_mods_def,expr_sim_full_code_def]
QED

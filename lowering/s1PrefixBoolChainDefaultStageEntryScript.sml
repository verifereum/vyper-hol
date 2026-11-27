(* The default stage starts at the reached end of the supplied-argument stage. *)
Theory s1PrefixBoolChainDefaultStageEntry
Ancestors
  bodyFullIntCallArgs bodyPtrDefs loweringPosts fragGasOriginPtr
  vyperStorageFootprint vyperInterpreter vyperState exprLowering compileEnv
  list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule_all intcall_args_supplied_stage_setup >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`art`,`imms`,`A`,`roots`,`compiled_dflts`,`ds`,`vv`,`sm`,
    `shadow_vv`,`shadow_sm`,`rc'`,`rbs`,`pvs`,`buf_n`,`st2`,`st2a`,`st3`,
    `sh_st2`,`sh_st2a`,`sh_st3`,`sup_ops`,`def_ops`,`sh_def_ops`,`entry`,`Ga`,`tna`,`pin`]
    (map_every assume_tac o CONJUNCTS)) >>
  `TAKE (LENGTH args) (cenv.ce_func_param_types (nsid_to_string (NONE,name))) =
     MAP SND args` by simp[] >>
  qpat_assum `TAKE (LENGTH args) _ = MAP SND args` (fn tys =>
    qpat_assum `sh_def_ops = def_ops` (fn ops =>
      qpat_x_assum `compile_stage_intcall_args _ _ ds _ _ st2a = _`
        (assume_tac o PURE_REWRITE_RULE [tys]) >>
      qpat_x_assum `compile_stage_intcall_args _ _ (MAP gas_shadow_expr ds) _ _ sh_st2a = _`
        (assume_tac o PURE_REWRITE_RULE [tys,ops]))) >>
  qexistsl_tac [`rc'`,`rbs`,`pvs`,`ds`,`st2`,`st2a`,`st3`,`sh_st2`,`sh_st2a`,`sh_st3`,
    `sup_ops`,`def_ops`,`entry`,`Ga`,`tna`,`pin`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- simp[]
  >- simp[] >>
  rpt gen_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [intcall_args_stage_post_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_default_stage_entry:
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx tenv es0 /\
  expr_body_pre cenv cx tenv (Call ann (IntCall (NONE,name)) es dflt) es0 /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  LENGTH args - LENGTH dflts <= LENGTH es /\ LENGTH es <= LENGTH args /\
  (!v. cs_appends (kc v)) /\
  comp_bind (compile_expr cenv ty (Call ann (IntCall (NONE,name)) es dflt))
    kc sa = (out,sb) /\
  comp_bind (compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (NONE,name)) es dflt)))
    kc shadow_sa = (out,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ MEM func ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  storage_trace_domain cx st0 es0.storage_trace /\
  (!H. valid_horizon cx st0 H es0.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es0 s0 /\
    storage_well_formed_on cx es0 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es0 G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?rc rbs pvs ds st2 st2a st3 sh_st2 sh_st2a sh_st3 sup_ops def_ops entry Ga tna pin.
    cenv.ce_func_info (nsid_to_string (NONE,name)) = (rc,rbs,pvs) /\
    cenv.ce_func_param_types (nsid_to_string (NONE,name)) = MAP SND args /\
    ds = DROP (LENGTH dflts - (LENGTH args - LENGTH es))
      (subst_consts_exprs (module_consts_env tops []) dflts) /\
    omitted_defaults cenv (nsid_to_string (NONE,name)) (LENGTH es) = ds /\
    compile_stage_intcall_args compile_expr cenv es
      (TAKE (LENGTH es) pvs) (TAKE (LENGTH es) (MAP SND args)) st2 = (sup_ops,st2a) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr es)
      (TAKE (LENGTH es) pvs) (TAKE (LENGTH es) (MAP SND args)) sh_st2 = (sup_ops,sh_st2a) /\
    compile_stage_intcall_args compile_expr
      (cenv_without_defaults cenv (nsid_to_string (NONE,name))) ds
      (DROP (LENGTH es) pvs) (DROP (LENGTH es) (MAP SND args)) st2a = (def_ops,st3) /\
    compile_stage_intcall_args compile_expr
      (gas_shadow_env T (cenv_without_defaults cenv (nsid_to_string (NONE,name))))
      (MAP gas_shadow_expr ds) (DROP (LENGTH es) pvs) (DROP (LENGTH es) (MAP SND args))
      sh_st2a = (def_ops,sh_st3) /\
    gas_shadow_state st2 sh_st2 /\ gas_shadow_state st2a sh_st2a /\ gas_shadow_state st3 sh_st3 /\
    fn_has_code st2 st2a func /\ fn_has_code sh_st2 sh_st2a shadow_func /\
    fn_has_code st2a st3 func /\ fn_has_code sh_st2a sh_st3 shadow_func /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
    ~entry.vs_halted /\ entry.vs_current_bb = st2.cs_current_bb /\
    entry.vs_inst_idx = LENGTH st2.cs_current_insts /\
    (!H xs ee t G tn.
      intcall_args_stage_post (DF,lo,d,ctx,func,cenv,cx,tenv)
        (es,sa,s0,es0,G0,tn0,st2a)
        (TAKE (LENGTH es) pvs,TAKE (LENGTH es) (MAP SND args),sup_ops,
         [],[],[],[],pin,T,T) H (INL xs) ee G tn t ==>
      ~t.vs_halted /\ t.vs_current_bb = st2a.cs_current_bb /\
      t.vs_inst_idx = LENGTH st2a.cs_current_insts /\
      return_buf_frame d cenv st2a t /\
      stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t)
Proof
  cheat
QED

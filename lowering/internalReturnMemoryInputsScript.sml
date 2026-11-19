(* Robust source inputs for the joint buffered internal Return suffix. *)
Theory internalReturnMemoryInputs
Ancestors
  assignBasePtrBoundary bodyDeclCopyMemory exprSimMemDefs loweringPosts
  bodyPtrDefs ptrDiscipline venomExecSemantics venomState
  exprSimHypsDefs vyperTypeEvalSoundness vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeInvariants valueCopyBytes
  externalReturnSiteSemantics typedCopyCompatibility exprLowering compileEnv
  exprSimHyps exprSimIfExpCompat exprSimSource
  vyperTypeArgFits valueTypingMemoryProps

Theorem return_value_typed:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) =
    (INL v, es') ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
       value_has_type tv v
Proof
  rw[expr_sim_inv_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def, AllCaseEqs()] >>
  `call_evaluation_safe cx (int_calls_expr e)`
    by gvs[int_calls_stmt_def, int_calls_expr_def] >>
  mp_tac (Q.INST [`st` |-> `es with gas_obs := g`, `res` |-> `INL v`,
                  `st'` |-> `es'`] eval_expr_read_type_sound) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  gvs[value_runtime_typed_def, env_consistent_def,
      env_context_consistent_def]
QED

(* An internal call's allocated layout is its declared result type.
   Its post uses the annotation only when the two layouts read alike. *)
Theorem internal_return_buffer_value_layout:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) =
    (INL v,ee) /\
  (lowered_value_type cenv e = expr_type e \/
   ?ann fid args drv. e = Call ann (IntCall fid) args drv) ==>
  ?stv ptv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
    value_has_type stv v /\ value_has_type ptv v /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret /\
    (post_value_type cenv e = lowered_value_type cenv e \/
     (is_bytestring_type (post_value_type cenv e) /\
      is_bytestring_type (lowered_value_type cenv e)) \/
     is_word_type (expr_type e))
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `well_typed_expr env e /\ type_widens_to (get_tenv cx) (expr_type e) ret` by
    gvs[type_stmt_def,AllCaseEqs()] >>
  drule_all return_value_typed >> strip_tac
  >- (`post_value_type cenv e = expr_type e` by metis_tac[post_value_type_lowered] >>
      qexistsl_tac [`tv`,`tv`] >> asm_rewrite_tac[]) >>
  TRY (qpat_x_assum `e = Call _ _ _ _` SUBST_ALL_TAC) >>
  `expr_sim_inv cenv cx env (es with gas_obs := g)` by simp[] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := g`, `ce` |-> `cenv`,
    `ty` |-> `ann`, `fid` |-> `fid`, `args` |-> `args`, `drv` |-> `drv`,
    `env` |-> `env`, `cx` |-> `cx`, `v` |-> `v`, `es'` |-> `ee`]
    (CONV_RULE (DEPTH_CONV ETA_CONV) return_intcall_physical_typed)) >>
  simp[] >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv
     (Call ann (IntCall fid) args drv)) ann` by
    metis_tac[return_intcall_lowered_widens] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv
     (Call ann (IntCall fid) args drv)) ret` by
    metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans,
      vyperASTTheory.expr_type_def] >>
  Cases_on `is_word_type ann`
  >- (qexistsl_tac [`stv`,`tv`] >> fs[vyperASTTheory.expr_type_def]) >>
  Cases_on `is_bytestring_type ann`
  >- (qexistsl_tac [`stv`,`tv`] >> fs[vyperASTTheory.expr_type_def] >>
      metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source]) >>
  qexistsl_tac [`stv`,`stv`] >> simp[]
QED

Theorem internal_return_buffer_value_layout_typed:
  expr_sim_inv cenv cx env es /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  alloc_limits_expr cenv e /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := g) =
    (INL v,ee) ==>
  ?stv ptv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
    value_has_type stv v /\ value_has_type ptv v /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret /\
    (post_value_type cenv e = lowered_value_type cenv e \/
     (is_bytestring_type (post_value_type cenv e) /\
      is_bytestring_type (lowered_value_type cenv e)) \/
     is_word_type (expr_type e))
Proof
  strip_tac >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
     (?ann fid args drv. e = Call ann (IntCall fid) args drv)`
  >- (qpat_assum `lowered_value_type cenv e = expr_type e \/ _`
        (mp_then Any (qspecl_then [`v`,`ret`,`g`,`es`,`env`,`ee`,`cx`] mp_tac)
          internal_return_buffer_value_layout) >>
      asm_rewrite_tac[]) >>
  `env_consistent env cx es /\
   sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!fid sig. FLOOKUP env.fn_sigs fid = SOME sig ==>
     cenv.ce_func_return_type (nsid_to_string fid) = sig.ret_ty)` by
    fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def,env_context_consistent_def] >>
  `well_typed_expr env e /\ type_widens_to (get_tenv cx) (expr_type e) ret` by
    fs[type_stmt_def,AllCaseEqs()] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, exprSimSourceTheory.env_consistent_var_type_evaluates] >>
  mp_tac (Q.SPECL [`cenv`,`e`,`env`] ifexp_lowered_type_classify) >>
  asm_rewrite_tac[] >> strip_tac >> fs[] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[expr_sim_inv_type_evaluates] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    fs[type_widens_to_def, well_formed_type_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ret` by
    metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[int_calls_stmt_def, int_calls_expr_def] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    (mp_tac (Q.SPECL [`cenv`,`e`,`env`,`cx`,`es with gas_obs := g`,`v`,`ee`]
       (CONV_RULE (DEPTH_CONV ETA_CONV) expr_sim_inv_read_lowered_typed)) >>
     simp[]) >>
  drule_all return_value_typed >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_not_int_call] >>
  fs[value_runtime_typed_def] >>
  rename1 `evaluate_type env.type_defs (lowered_value_type cenv e) = SOME stv` >>
  qexists_tac `stv` >> fs[] >>
  qpat_assum `env.type_defs = get_tenv cx` (rewrite_tac o single o SYM) >>
  first_assum ACCEPT_TAC
QED

(* Capacity coverage and the actual source-read bound are distinct facts.
   Neither asserts that the entire source capacity is below the frontier. *)
Theorem internal_return_memory_value_inputs:
  !H ctx func cenv cx e es sa sm s0 ee v op t G tn ty tv.
    expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    ptr_buf_ok cenv e op G t /\
    expr_store_bound cx (post_value_type cenv e) v op t /\
    lowered_value_type cenv e = expr_type e /\ expr_type e = ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    0 < type_memory_size tv /\
    type_memory_bytes cenv ty = type_memory_size tv ==>
    ?src a.
      op = Var src /\ lookup_var src t = SOME a /\
      ptr_covers G tn src t (type_memory_size tv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
           val_in_memory tv v (w2n a) m) /\
      w2n a + val_store_size tv v <= t.vs_alloca_next
Proof
  rpt strip_tac >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `?a. eval_operand op t = SOME a` by
    fs[expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {} /\ ptr_mem_ok cx ty v op G tn t` by
    fs[ptr_val_ok_def] >>
  `?src. op = Var src /\ ptr_covers G tn src t (type_memory_size tv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`, `e`] >> simp[]) >>
  `0 < val_store_size tv v` by metis_tac[val_store_size_pos] >>
  qexistsl [`src`, `a`] >>
  gvs[eval_operand_def, ptr_mem_ok_def, expr_store_bound_def]
QED

(* A nested call can keep its bytestring payload in a narrower physical
   buffer than the annotation used in the expression post. *)
Theorem internal_return_memory_value_inputs_lowered:
  !H ctx func cenv cx e es sa sm s0 ee v op t G tn ty pt stv ptv.
    expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
    ptr_val_ok cx pt v op G tn t /\
    ptr_buf_ok cenv e op G t /\
    expr_store_bound cx pt v op t /\
    lowered_value_type cenv e = ty /\
    post_value_type cenv e = pt /\
    evaluate_type (get_tenv cx) ty = SOME stv /\
    evaluate_type (get_tenv cx) pt = SOME ptv /\
    ~is_word_type pt /\
    value_has_type stv v /\ value_has_type ptv v /\
    (pt = ty \/ (is_bytestring_type pt /\ is_bytestring_type ty)) /\
    0 < type_memory_size stv /\
    type_memory_bytes cenv ty = type_memory_size stv ==>
    ?src a.
      op = Var src /\ lookup_var src t = SOME a /\
      ptr_covers G tn src t (type_memory_size stv) /\
      (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
           val_in_memory stv v (w2n a) m) /\
      w2n a + val_store_size stv v <= t.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?a. eval_operand op t = SOME a` by
    fs[expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {} /\ ptr_mem_ok cx pt v op G tn t` by
    fs[ptr_val_ok_def] >>
  `?src. op = Var src /\ ptr_covers G tn src t (type_memory_size stv)` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
     simp[] >> qexistsl [`cenv`, `e`] >> simp[]) >>
  `val_store_size ptv v = val_store_size stv v` by
    (Cases_on `pt = ty` >> gvs[] >> metis_tac[bytestring_val_store_size_eq]) >>
  `0 < val_store_size stv v` by metis_tac[val_store_size_pos] >>
  `w2n a + val_store_size stv v <= t.vs_alloca_next` by
    (gvs[expr_store_bound_def] >> metis_tac[arithmeticTheory.NOT_LT_ZERO_EQ_ZERO]) >>
  `!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
     val_in_memory ptv v (w2n a) m` by
    (qpat_assum `ptr_mem_ok cx pt v op G tn t`
      (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     disch_then (qspecl_then [`ptv`,`a`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `lookup_var src t = SOME a` by gvs[eval_operand_def] >>
  qexistsl [`src`, `a`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_assum `!m. mem_agree_outside _ _ m ==> val_in_memory _ _ _ m`
    (drule_then assume_tac) >>
  Cases_on `pt = ty` >> gvs[] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED

(* An evaluated, nonvoid callable result occupies memory. *)
Theorem callable_return_memory_size_pos:
  functions_well_typed cx /\ env_context_consistent env cx /\
  get_module_code cx src = SOME tops /\
  lookup_callable_function cx.in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,ss) /\
  context_function_live cx (src,name) /\ ret <> NoneT /\
  evaluate_type (get_tenv cx) ret = SOME tv ==>
  0 < type_memory_size tv
Proof
  rpt strip_tac >>
  `assignable_type (get_tenv cx) ret` by
    (qpat_x_assum `functions_well_typed cx`
       (mp_tac o REWRITE_RULE [functions_well_typed_def]) >>
     disch_then
       (qspecl_then [`env.fn_sigs`, `env.bare_globals`,
                     `env.bare_global_assignable`, `env.toplevel_vtypes`,
                     `env.flag_members`] mp_tac) >>
     impl_tac
     >- (drule vyperTypeInitialStateTheory.env_context_consistent_static_maps_function_side_condition >>
         strip_tac >> gvs[env_context_consistent_def] >>
         rw[] >> first_x_assum drule_all >> simp[]) >>
     disch_then
       (qspecl_then [`src`, `name`, `tops`, `mut`, `nr`, `args`,
                     `dflts`, `ret`, `ss`] mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[assignable_type_slot_size_pos, cj 1 valueEncodingPropsTheory.type_memory_size_pos]
QED

(* Interface at the fixed memory selector, after both children return. *)
Theory bodyFullFramedMemorySelectionSpec
Ancestors
  bodyFullEmptyLeafData bodyFullShadowBodyInv bodyFullPreds
  exprSimHypsDefs exprSimFullBundleProps exprSimDefs
  exprSimArrayIndex exprLowering compileEnv context vyperTypeValues vyperInterpreter
  gasOutcomeFullCompose fragExec fragGasOriginPtr

Definition framed_memory_selection_hypotheses_def:
  framed_memory_selection_hypotheses
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    (tops,cenv,cx,env,ty,ann,e1,e2,et,n)
    (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0)
    (sm,bvv,marks,tv,mid,s,G1,tn1)
    (st2,iop,imarks,v,fin,it,Gi,tni) dst <=>
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et (Fixed n) /\
    place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t res t'. eval_expr cx e2 t = (INL res,t') ==>
       t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!t tr slot vt t'.
       eval_expr cx e1 t <> (INL (PlaceR (StoragePlace tr slot vt)),t')) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty' st. vv_location (FST (compile_expr cenv ty' e1 st)) = SOME LocMemory) /\
    expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
    compile_expr cenv ty e1 sa = (bvv,sm) /\
    lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
    vv_location bvv = SOME LocMemory /\
    compile_array_subscript (vv_operand bvv) iop F n (word_scale LocMemory)
      (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type e2))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory) /\
    cs_extends sa sm /\ cs_extends sm st2 /\ cs_extends st2 sb /\
    fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func /\
    expr_body_pre cenv cx env e1 es /\ expr_body_pre cenv cx env e2 mid /\
    (!tail. eval_expr cx e1
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL tv,mid with gas_obs := tail)) /\
    ~s.vs_halted /\ mid.gas_obs = [] /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx e1
        (es,sa,sm,s0,bvv,G0,tn0) H (INL tv : eval_result + exception) mid G1 tn1 s /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK s,G1,tn1)) /\
    (!tail. bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit imarks s.vs_gas_readings ++ tail) =
      (INL v,fin with gas_obs := tail)) /\
    ~it.vs_halted /\ fin.gas_obs = [] /\ storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e2
        (mid,sm,st2,s,iop,G1,tn1) H (INL v : value + exception) fin Gi tni it /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G1,tn1) imarks (OK it,Gi,tni))
End

(* The observation is on the very same endpoint as the ordinary posts. *)
Definition framed_memory_selection_rule_def:
  framed_memory_selection_rule Obs <=>
    !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann e1 e2 et n
     st0 es sa sb sha shb vv s0 G0 tn0 sm bvv marks tv mid s G1 tn1
     st2 iop imarks v fin it Gi tni dst.
    framed_memory_selection_hypotheses
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      (tops,cenv,cx,env,ty,ann,e1,e2,et,n)
      (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0)
      (sm,bvv,marks,tv,mid,s,G1,tn1)
      (st2,iop,imarks,v,fin,it,Gi,tni) dst ==>
    ?sc s_mul off out res r Gf tnf.
      array_bounds_check iop (Lit (n2w n)) (is_signed_type (expr_type e2)) st2 = ((),sc) /\
      emit_op MUL [iop; Lit (n2w (elem_size_in_location cenv LocMemory et))] sc =
        (Var off,s_mul) /\
      emit_op ADD [vv_operand bvv; Var off] s_mul = (Var out,sb) /\
      dst = Var out /\
      Obs st2 sc sb it r /\
      (!tail. select_result cx (expr_type e1) tv (ValueSubscript v)
        (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (it,Gi,tni) [] (r,Gf,tnf)) /\
      ((?child sf. res = INL child /\ r = OK sf /\
          !H. valid_horizon cx st0 H fin.storage_trace ==>
            expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript ann e1 e2)
              (es,sa,sb,s0,vv,G0,tn0) H res fin Gf tnf sf) \/
       (?sf. res = INR (Error (RuntimeError "evaluate_subscripts array_index")) /\
          r = Abort Revert_abort sf /\
          !H. valid_horizon cx st0 H fin.storage_trace ==>
            expr_exit res r /\ halt_exit H cx fin res r /\
            (ctx_has_dalloca ctx ==> !s'. r = Halt s' ==> allocas_below_fmp s')))
End

Theorem framed_memory_selection_rule_full:
  framed_memory_selection_rule Obs /\
  framed_memory_selection_hypotheses
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    (tops,cenv,cx,env,ty,ann,e1,e2,et,n)
    (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0)
    (sm,bvv,marks,tv,mid,s,G1,tn1)
    (st2,iop,imarks,v,fin,it,Gi,tni) dst ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (select_result cx (expr_type e1) tv (ValueSubscript v))
    (fin,it,Gi,tni)
    (expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript ann e1 e2)
      (es,sa,sb,s0,vv,G0,tn0))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s'. r = Halt s' ==> allocas_below_fmp s'))
Proof
  strip_tac >>
  `~it.vs_halted /\ fin.gas_obs = []` by
    (qpat_assum `framed_memory_selection_hypotheses _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [framed_memory_selection_hypotheses_def]) >> simp[]) >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum `framed_memory_selection_rule _`
    (mp_tac o REWRITE_RULE [framed_memory_selection_rule_def]) >>
  disch_then drule >> strip_tac
  >- (irule gas_outcome_full_pure >> simp[] >>
      qexistsl_tac [`Gf`,`fin`,`INL child`,`sf`,`tnf`] >> gvs[]) >>
  irule gas_outcome_full_exit >> simp[exit_result_def] >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort sf`,
    `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
  gvs[exit_result_def] >> metis_tac[]
QED

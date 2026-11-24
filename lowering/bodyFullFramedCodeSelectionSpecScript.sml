(* Ordinary interface at the runtime-code selector, after both children return. *)
Theory bodyFullFramedCodeSelectionSpec
Ancestors
  bodyFullEmptyLeafData bodyFullShadowBodyInv bodyFullPreds
  exprSimHypsDefs exprSimFullBundleProps
  exprSimDefs exprSimArrayIndex exprLowering compileEnv context vyperInterpreter
  gasOutcomeFullCompose fragExec fragGasOriginPtr

Definition framed_code_selection_hypotheses_def:
  framed_code_selection_hypotheses
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    (tops,cenv,cx,env,ty,ann,e1,e2,et,bd)
    (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0)
    (sm,bvv,marks,tv,mid,s,G1,tn1)
    (st2,iop,imarks,v,fin,it,Gi,tni) dst <=>
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et bd /\
    place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t res t'. eval_expr cx e2 t = (INL res,t') ==>
       t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!t tr slot vt t'.
       eval_expr cx e1 t <> (INL (PlaceR (StoragePlace tr slot vt)),t')) /\
    ~cenv.ce_is_ctor /\
    (!ty' st. vv_location (FST (compile_expr cenv ty' e1 st)) = SOME LocCode) /\
    expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
    compile_expr cenv ty e1 sa = (bvv,sm) /\
    lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
    vv_location bvv = SOME LocCode /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic n => n) (word_scale LocCode)
      (elem_size_in_location cenv LocCode et) (is_signed_type (expr_type e2))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) st2 = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocCode) /\
    cs_extends sa sm /\ cs_extends sm st2 /\ cs_extends st2 sb /\
    fn_has_code sa sm func /\ fn_has_code sm st2 func /\ fn_has_code st2 sb func /\
    expr_body_pre cenv cx env e1 es /\ expr_body_pre cenv cx env e2 mid /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\
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

(* Straight-line fragments share the actual endpoint up to PC reindexing. *)
Definition framed_code_run_def:
  framed_code_run a b s t <=>
    ?u. run_inst_seq (emitted_insts a b) s = OK u /\
        t = (u with vs_inst_idx := LENGTH b.cs_current_insts)
End

Definition framed_code_selection_rule_def:
  framed_code_selection_rule B <=>
    !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann e1 e2 et bd
     st0 es sa sb sha shb vv s0 G0 tn0 sm bvv marks tv mid s G1 tn1
     st2 iop imarks v fin it Gi tni dst.
    framed_code_selection_hypotheses
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      (tops,cenv,cx,env,ty,ann,e1,e2,et,bd)
      (st0,es,sa,sb,sha,shb,vv,s0,G0,tn0)
      (sm,bvv,marks,tv,mid,s,G1,tn1)
      (st2,iop,imarks,v,fin,it,Gi,tni) dst ==>
    ?sl sc len il checked res r Gf tnf.
      (case bd of
         Fixed n => sl = st2 /\ il = it /\ len = Lit (n2w n)
       | Dynamic n =>
           compile_imm_load_word F cenv.ce_imm_alloca (vv_operand bvv) st2 = (len,sl) /\
           framed_code_run st2 sl it il) /\
      array_bounds_check iop len (is_signed_type (expr_type e2)) sl = ((),sc) /\
      array_elem_ptr (vv_operand bvv) iop
        (case bd of Fixed _ => F | Dynamic _ => T) (word_scale LocCode)
        (elem_size_in_location cenv LocCode et) sc = (dst,sb) /\
      cs_extends st2 sl /\ cs_extends sl sc /\ cs_extends sc sb /\
      fn_has_code st2 sl func /\ fn_has_code sl sc func /\ fn_has_code sc sb func /\
      ~il.vs_halted /\ il.vs_current_bb = sl.cs_current_bb /\
      il.vs_inst_idx = LENGTH sl.cs_current_insts /\
      B sl sc il checked /\
      (!tail. select_result cx (expr_type e1) tv (ValueSubscript v)
        (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (it,Gi,tni) [] (r,Gf,tnf)) /\
      ((?child ib sf. res = INL child /\ checked = OK ib /\ r = OK sf /\
          ~ib.vs_halted /\ ib.vs_current_bb = sc.cs_current_bb /\
          ib.vs_inst_idx = LENGTH sc.cs_current_insts /\ framed_code_run sc sb ib sf /\
          !H. valid_horizon cx st0 H fin.storage_trace ==>
            expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript ann e1 e2)
              (es,sa,sb,s0,vv,G0,tn0) H res fin Gf tnf sf) \/
       (?sf. res = INR (Error (RuntimeError "evaluate_subscripts array_index")) /\
          checked = Abort Revert_abort sf /\ r = checked /\
          !H. valid_horizon cx st0 H fin.storage_trace ==>
            expr_exit res r /\ halt_exit H cx fin res r /\
            (ctx_has_dalloca ctx ==> !s'. r = Halt s' ==> allocas_below_fmp s')))
End

Theorem framed_code_selection_rule_full:
  framed_code_selection_rule B /\
  framed_code_selection_hypotheses
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    (tops,cenv,cx,env,ty,ann,e1,e2,et,bd)
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
    (qpat_assum `framed_code_selection_hypotheses _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [framed_code_selection_hypotheses_def]) >> simp[]) >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_x_assum `framed_code_selection_rule _`
    (mp_tac o REWRITE_RULE [framed_code_selection_rule_def]) >>
  disch_then drule >> strip_tac
  >- (irule gas_outcome_full_pure >> simp[] >>
      qexistsl_tac [`Gf`,`fin`,`INL child`,`sf`,`tnf`] >> gvs[]) >>
  irule gas_outcome_full_exit >> simp[exit_result_def] >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort sf`,
    `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
  gvs[exit_result_def] >> metis_tac[]
QED

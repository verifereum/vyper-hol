(* Positional arguments are read and snapshotted before the next operand. *)
Theory extcallEagerOperandsMemory
Ancestors
  exprSimMemDefs stmtReasonVvMemory exprSimWordArgs exprLoweringProps
  stmtLoweringMono exprLowering compileEnv fragExec gasOutcome vyperState list
  loweringPosts context vyperInterpreter exprSimDefs

Theorem extcall_arg_value_capture:
  vv_holds ce cx lt raw vv ee s /\
  vv_store_bound cx ty lt ee raw vv s /\ vv_storage_live cx vv ee s ==>
  vv_holds ce cx lt raw (ext_call_arg_value lt vv) ee s /\
  vv_store_bound cx ty lt ee raw (ext_call_arg_value lt vv) s /\
  vv_storage_live cx (ext_call_arg_value lt vv) ee s
Proof
  Cases_on `vv` >- simp[ext_call_arg_value_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location` >>
  gvs[ext_call_arg_value_def,vv_holds_def,vv_store_bound_def] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Theorem extcall_nonword_snapshot_no_copy:
  ~is_word_type ty ==>
  compile_snapshot_vv ce F (ext_call_arg_value ty vv) sa =
    (ext_call_arg_value ty vv,sa)
Proof
  strip_tac >> Cases_on `vv` >>
  simp[ext_call_arg_value_def,compile_snapshot_vv_def,vv_type_def,
       unwrap_value_def,comp_bind_def,comp_return_def] >>
  Cases_on `is_word_type t` >> simp[comp_bind_def,comp_return_def]
QED

Theorem extcall_word_snapshot_lower_value:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce F (ext_call_arg_value (expr_type e) vv) sm =
    (saved,sb) /\ is_word_type (expr_type e) /\
  (!tag p. vv = LocatedValue tag p ==> tag = expr_type e) ==>
  ?tag op. saved = StackValue tag op /\
    lower_value compile_expr ce (expr_type e) e sa = (op,sb)
Proof
  strip_tac >> Cases_on `vv`
  >- (Cases_on `is_word_type t` >>
      gvs[ext_call_arg_value_def,compile_snapshot_vv_def,vv_type_def,
          lower_value_def,unwrap_value_def,comp_bind_def,comp_return_def]) >>
  gvs[ext_call_arg_value_def,compile_snapshot_vv_def,vv_type_def,
      lower_value_def,comp_bind_def,comp_return_def] >>
  pairarg_tac >> gvs[]
QED

Theorem extcall_eager_operands_mem_cps:
  !es tys sa vvs sb ars avvs ee s.
    compile_ext_call_args compile_expr ce kws tys es sa = (vvs,sb) /\
    LENGTH tys = LENGTH es /\ fn_has_code sa sb func /\
    P ars avvs ee s sa es /\
    (!ty e tail rs vs st t sc sm vv sn saved.
       MEM (ty,e) (ZIP (tys,es)) /\ P rs vs st t sc (e::tail) /\
       compile_expr ce (expr_type e) e sc = (vv,sm) /\
       compile_snapshot_vv ce (exprs_can_mutate ce (tail ++ kws))
         (ext_call_arg_value ty vv) sm = (saved,sn) /\
       fn_has_code sc sm func /\ fn_has_code sm sn func ==>
       gas_outcome T (cx_tops cx) (ctx,func)
         (bind (eval_expr cx e) (read_result cx)) (st,t)
         (\res fin u. ?v. res = INL v /\
           P (rs ++ [v]) (vs ++ [saved]) fin u sn tail)
         (\res fin r. expr_exit res r)) /\
    (!rs vs st t. P rs vs st t sb [] ==>
       gas_outcome T (cx_tops cx) (ctx,func) (next rs vs) (st,t) Q
         (\res fin r. expr_exit res r)) ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (eval_exprs cx es) (\rs. next (ars ++ rs) (avvs ++ vvs)))
      (ee,s) Q (\res fin r. expr_exit res r)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_ext_call_args_def, comp_return_def, Once evaluate_def,
          bind_return] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `tys` >> gvs[] >>
  rename1 `LENGTH tyrest = LENGTH es` >>
  qpat_x_assum `compile_ext_call_args _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_ext_call_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def,comp_return_def]) >>
  strip_tac >> gvs[] >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `compile_snapshot_vv ce _ _ sm = (saved,sn)` >>
  rename1 `compile_ext_call_args compile_expr ce kws tyrest es sn = (rest,sf)` >>
  suspend "head"
QED
Resume extcall_eager_operands_mem_cps[head]:
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sf` by
    (rpt conj_tac
     >- metis_tac[cj 1 ci_mono_compile_expr_sa,pairTheory.SND]
     >- metis_tac[ci_mono_compile_snapshot_vv,pairTheory.SND] >>
     `ci_mono sn (SND (compile_ext_call_args compile_expr ce kws tyrest es sn))` by
       (irule ci_mono_compile_ext_call_args >>
        simp[cj 1 ci_mono_compile_expr_sa]) >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn sf func` by
    (fs[ci_mono_def] >>
     metis_tac[fn_has_code_mid,cs_extends_trans,cs_extends_refl]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (bind (eval_expr cx h) (read_result cx)) (ee,s)
     (\res fin u. ?v. res = INL v /\
       P (ars ++ [v]) (avvs ++ [saved]) fin u sn es)
     (\res fin r. expr_exit res r)` by
    (qpat_x_assum `!ty e tail rs vs st t sc sm vv sn saved. _`
       (qspecl_then [`h'`,`h`,`es`,`ars`,`avvs`,`ee`,`s`,`sa`,`sm`,
                    `vv`,`sn`,`saved`] mp_tac) >> simp[]) >>
  simp[eval_exprs_cons_action,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "tail" >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume extcall_eager_operands_mem_cps[tail]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!tys sa vvs sb ars avvs ee s. _`
    (qspecl_then [`tyrest`, `sn`, `rest`, `sf`, `ars ++ [v]`,
                 `avvs ++ [saved]`, `mid with gas_obs := []`, `t`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  simp[] >> disch_then irule >>
  rpt conj_tac >> metis_tac[]
QED
Finalise extcall_eager_operands_mem_cps

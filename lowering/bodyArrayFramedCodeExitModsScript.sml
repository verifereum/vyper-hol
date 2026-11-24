(* Rejection needs the loaded (or literal) length, not the element address. *)
Theory bodyArrayFramedCodeExitMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullSubscriptArrayCodeBounds gasOutcomeFullPostMods
  bodyFullShadowBodyInv fragGasOriginPtr fragExec exprSimDefs ptrDiscipline
  exprSimArrayIndex vyperTypeSystem vyperState

Theorem framed_code_bounds_exit_mods:
  array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty obj idx et bd st0
    (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,LocCode)
    (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
    (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) /\
  (!D. allocas_from lo it ==>
       gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (it,Gi,tni) [] (OK sl,Gl,tnl)) /\
  sl.vs_allocas = it.vs_allocas /\
  array_bounds_check iop len_op (is_signed_type (expr_type idx)) sc = ((),se) /\
  fn_has_code sc se func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp sl) /\ ~sl.vs_halted /\
  sl.vs_current_bb = sc.cs_current_bb /\ sl.vs_inst_idx = LENGTH sc.cs_current_insts /\
  eval_operand iop sl = SOME iw /\ eval_operand len_op sl = SOME len /\
  ~idx_in_range (is_signed_type (expr_type idx)) iw len /\
  op_taint tnl iop = {} /\ op_taint tnl len_op = {} /\
  op_prov Gl iop = NONE /\ op_prov Gl len_op = NONE /\
  (!q. iop = Var q \/ len_op = Var q ==> not_fresh_at sc q) /\
  (!l. iop <> Label l /\ len_op <> Label l) /\
  (!tail. select_result cx (ArrayT et bd) raw (ValueSubscript key)
       (fin with gas_obs := tail) =
     (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)) ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
    cenv cx ann obj idx et bd st0 (es,s0,G0,tn0) (sa,sb,dst,LocCode)
    (raw,key) (fin,it,Gi,tni)
Proof
  strip_tac >>
  drule_all array_bounds_check_joint_oob_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Gf`,`tnf`,`sf`] strip_assume_tac)) >>
  `~it.vs_halted /\ (!H. valid_horizon cx st0 H fin.storage_trace ==> allocas_from lo it)` by
    (qhdtm_x_assum `array_nocopy_cut_mods`
       (strip_assume_tac o REWRITE_RULE [array_nocopy_cut_mods_def]) >>
     simp[] >> gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ it /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def])) >>
     first_assum ACCEPT_TAC) >>
  rewrite_tac[array_select_outcome_mods_def, LET_THM] >> BETA_TAC >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`fin`,`Abort Revert_abort sf`,
                `INR (Error (RuntimeError "evaluate_subscripts array_index"))`,`tnf`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  gen_tac >> strip_tac >>
  `allocas_from lo it` by
    (qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> allocas_from lo it`
       (drule_then ACCEPT_TAC)) >>
  `allocas_from lo sl` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `sl.vs_allocas = it.vs_allocas` SUBST1_TAC >>
     qpat_assum `allocas_from lo it` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qpat_assum `!D. _ ==> gas_origin_ptr_path _ (it,Gi,tni) [] (OK sl,Gl,tnl)`
    (qspec_then `DF H` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[] >>
  disch_then irule >> simp[]
QED

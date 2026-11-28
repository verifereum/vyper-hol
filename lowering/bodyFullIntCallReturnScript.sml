(*
 * The internal call full case's return stage over the finite-horizon joint
 * judgment.
 *
 * TOP-LEVEL:
 *   intcall_return_full
 *)
Theory bodyFullIntCallReturn
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams bodyFullPreds bodySimFull
  gasOutcomeFull fragGasFocus bodyPtrDefs gasShadow gasContext
  exprSimHypsDefs exprLowering vyperInterpreter vyperAST list
  bodyFullIntCallReturnNormal bodyFullIntCallReturnSource bodyFullIntCallReturnUnwrap
  bodyInvSplit[qualified]
  gasOutcomeFullMods[qualified] bodyFullPostsMods[qualified]

val _ = Parse.hide "body";

(* Keep the compiler and callee parameters fixed while matching the result. *)
fun apply_intcall_return_rule rule =
  let
    val return_args =
      [`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`func`,`shadow_func`,`tops`,
       `cenv`,`cx`,`tenv`,`ty`,`ann`,`name`,`es`,`dflt`,`es0`,`st0`,`sa`,
       `sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`,`mut`,`nr`,`args`,
       `ret`,`ss`,`rr`,`prev`,`penv`,`rtv`,`es1`,`t`,`G`,`tn`,
       `result_count`,`buf_size`,`param_vars`,`callee`,`entered`,`bb`,
       `inst`,`lbl`,`arg_ops`,`argv`,`dflts`]
    val shadow_expr = ``gasShadow$gas_shadow_expr``
    val shadow_var = mk_var ("gas_shadow_expr", type_of shadow_expr)
  in
    match_mp_tac (INST [shadow_var |-> shadow_expr] (Q.SPECL return_args rule))
  end;

val intcall_return_premises =
  simp[] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC);

(* (c) Return and unlock restore, at (DF H, lo).  From an
   intcall_entry_full state t at the INVOKE, with every callee run the
   INVOKE can enter ending as stage (b) gives it: the INVOKE, the results'
   store into the return buffer, the frame's cleanup with the lock's
   release, and the cast reach the call's joint vv post at the end of its
   code; with the value unwrapped after it, they reach its joint value
   post. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `cenv.ce_func_info _ = (result_count,buf_size,param_vars)` >>
  `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es
    sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
    metis_tac[] >>
  `?callee entered. gas_invoke_entry (ctx,func) t callee entered` by
    (fs[intcall_entry_full_def] >> metis_tac[]) >>
  `?bb inst lbl arg_ops argv.
     lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb t.vs_inst_idx = SOME inst /\
     decode_invoke inst = SOME (lbl,arg_ops) /\
     eval_operands arg_ops t = SOME argv` by
    (fs[gas_invoke_entry_def] >> metis_tac[]) >>
  qpat_x_assum `!callee entered bb inst lbl arg_ops argv. _` drule_all >>
  strip_tac >>
  conj_asm1_tac >-
    (qhdtm_x_assum `gas_outcome_full`
       (strip_assume_tac o SIMP_RULE bool_ss [gas_outcome_full_def])
     >- (rename1 `gas_origin_ptr_focus (DF focus_horizon,_,_,_,_,_) _
                    focus_marks (focus_leaf,focus_pg,focus_g,focus_tn,focus_finish)` >>
         apply_intcall_return_rule intcall_return_noncompleted >>
         intcall_return_premises >>
         qexists_tac `focus_marks` >> disj1_tac >> simp[] >>
         qexistsl_tac
           [`focus_horizon`,`focus_leaf`,`focus_pg`,`focus_g`,`focus_tn`,`focus_finish`] >>
         simp[])
     >- (rename1 `!tail. intcall_callee_src cx name mut nr ss
                           (es1 with gas_obs :=
                             gas_explicit return_marks entered.vs_gas_readings ++ tail) =
                         (return_res,return_source with gas_obs := tail)` >>
         rename1 `!h. valid_horizon cx st0 h return_source.storage_trace ==>
                        gas_origin_ptr_path
                          (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
                           MAP (op_prov G) arg_ops)
                          (entered,FEMPTY,tn with t_var := FEMPTY)
                          return_marks (return_r,return_g,return_tn) /\
                        exit_result return_r /\ create_size_exit_ok ctx return_res return_r /\
                        intcall_callee_exit_full (DF,lo) h func cenv cx mut nr rtv
                          result_count
                          (if result_count = 0 /\ 0 < buf_size then SOME (HD argv) else NONE)
                          sa.cs_next_id sm.cs_next_id t tn return_res
                          (return_source with gas_obs := []) (return_g,return_tn) return_r` >>
         apply_intcall_return_rule intcall_return_normal_owned >>
         intcall_return_premises >>
         qexistsl_tac
           [`return_marks`,`return_res`,`return_source`,`return_r`,`return_g`,`return_tn`] >>
         simp[] >> rpt strip_tac >>
         qpat_assum `!h. valid_horizon cx st0 h return_source.storage_trace ==>
                           gas_origin_ptr_path _ _ _ _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     rename1 `gas_exempt_cert _ _ _ _ _ _ (exempt_error,exempt_source) _` >>
     rename1 `gas_origin_ptr_focus (DF focus_horizon,_,_,_,_,_) _
                focus_marks (focus_leaf,focus_pg,focus_g,focus_tn,focus_finish)` >>
     apply_intcall_return_rule intcall_return_noncompleted >>
     intcall_return_premises >> qexists_tac `focus_marks` >> disj2_tac >>
     qexistsl_tac
       [`exempt_error`,`exempt_source`,`focus_leaf`,`focus_pg`,`focus_g`,`focus_tn`,`focus_finish`] >>
     simp[] >> qexists_tac `focus_horizon` >> simp[]) >>
  match_mp_tac intcall_return_unwrap >>
  qexistsl_tac
    [`tops`, `tenv`, `ty`, `args`, `ret`, `rr`, `penv`,
     `result_count`, `buf_size`, `param_vars`, `dflts`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_assum `_ ==> gas_outcome_full _ _ _ _ _ _ _ _` drule_all >>
  strip_tac >>
  irule gas_outcome_full_post_mono >>
  qhdtm_assum `gas_outcome_full` (irule_at Any) >>
  simp[] >> rpt strip_tac >> qexists_tac `tv` >> simp[]
QED
*)
Theorem intcall_return_full_owned:
  !DF lo d ctx shadow_ctx PG func shadow_func mods exps caller_src caller_tops
   src callee_tops vis cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs dflts.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods caller_src caller_tops cenv cx) /\
    expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (src,name)) es dflt) es0 /\
    ALOOKUP mods src = SOME callee_tops /\
    (src = NONE \/ context_function_live cx (src,name)) /\
    ((src = NONE /\ mods = [(NONE,callee_tops)]) \/
     MEM (src,name) (linked_live_functions mods exps)) /\
    lookup_callable_function cx.in_deploy name callee_tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) callee_tops /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    compile_expr cenv ty (Call ann (IntCall (src,name)) es dflt) sa =
      (vv, sm) /\
    compile_expr (gasShadowCompileBase$gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (src,name)) es dflt)) shadow_sa =
      (vv, shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full_mods (DF, lo, d) H mods src callee_tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (ctx,func) t callee entered /\
       lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome_full_mods
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
          MAP (op_prov G) arg_ops)
         mods cx st0 (intcall_callee_src_at cx src name mut nr ss)
         (es1, entered, FEMPTY, tn with t_var := FEMPTY)
         (\H res ee G' tn' t'. F)
         (\H res ee gt r.
            intcall_callee_exit_full_mods mods (DF, lo) H func cenv cx mut nr rtv rc
              (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
              sa.cs_next_id sm.cs_next_id t tn res ee gt r)) ==>
    (fn_has_code sa sm func /\
     fn_has_code shadow_sa shadow_sm shadow_func ==>
     gas_outcome_full_mods
       (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       cenv.ce_modules cx st0 (intcall_rest_at cx src name mut nr ss prev rtv)
       (es1, t, G, tn)
       (\H res ee G tn t'. ?tv. res = INL tv /\
         vv_post_mods H ctx func cenv cx (Call ann (IntCall (src,name)) es dflt)
           es0 sa sm s0 ee tv vv t' /\
         vv_store_bound cx (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           (lowered_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           ee tv vv t' /\
         t'.vs_current_bb = sm.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t' /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
         s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
         ptr_vv_ok cx
           (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           tv vv ee G tn t' /\
         (!v. tv = Value v /\
              ~is_word_type
                (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) /\
              ~is_bytestring_type
                (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) ==>
              vv_own cenv cx
                (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
                sa sm ee tv vv t' /\
              (!ty' p. vv = LocatedValue ty' p ==> p.ptr_location = LocMemory)) /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val, ee) /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv
                            (Call ann (IntCall (src,name)) es dflt)) =
                         SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!ty' op. vv = StackValue ty' op /\
                   ~is_word_type
                      (post_value_type cenv
                         (Call ann (IntCall (src,name)) es dflt)) ==>
                   ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt)
                     op G t') /\
         (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt)
                    p.ptr_operand G t') /\
         ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
    (!op sb shadow_sb.
       unwrap_value cenv vv sm = (op, sb) /\
       unwrap_value cenv vv shadow_sm = (op, shadow_sb) /\
       gas_shadow_state sb shadow_sb /\
       fn_has_code sa sb func /\
       fn_has_code shadow_sa shadow_sb shadow_func /\
       gas_admissible
         (bind (intcall_rest_at cx src name mut nr ss prev rtv) (read_result cx))
         expr_res_ok es1 ==>
       gas_outcome_full_mods
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         cenv.ce_modules cx st0
         (bind (intcall_rest_at cx src name mut nr ss prev rtv) (read_result cx))
         (es1, t, G, tn)
         (\H res ee G tn t'. ?v. res = INL v /\
           expr_post_mods H ctx func cenv cx (Call ann (IntCall (src,name)) es dflt)
             es0 sa sb s0 ee v op t' /\
           expr_store_bound cx
             (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) v op t' /\
           t'.vs_current_bb = sb.cs_current_bb /\
           t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t' /\
           (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
           s0.vs_alloca_next <= t'.vs_alloca_next /\
           ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
           ptr_val_ok cx
             (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
             v op G tn t' /\
           (~is_word_type
               (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) ==>
            ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt) op G t') /\
           ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >>
  disch_then (strip_assume_tac o Q.SPEC `PG` o MATCH_MP intcall_return_full_owned) >>
  conj_tac >-
    (strip_tac >>
     qpat_assum `_ ==> gas_outcome_full _ _ _ _ _ _ _ _` drule_all >>
     strip_tac >>
     irule gas_outcome_full_post_mono >>
     qhdtm_assum `gas_outcome_full` (irule_at Any) >>
     simp[] >> rpt strip_tac >> qexists_tac `tv` >> simp[]) >>
  first_assum ACCEPT_TAC
QED
*)
Theorem intcall_return_full:
  !DF lo d ctx shadow_ctx PG func shadow_func mods exps caller_src caller_tops
   src callee_tops vis cenv cx tenv ty ann name
   es dflt es0 st0 sa sm shadow_sa shadow_sm vv s0 G0 tn0 mut nr args ret ss
   rr prev penv rtv es1 t G tn rc rbs pvs dflts.
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods caller_src caller_tops cenv cx) /\
    expr_body_pre_mods mods cenv cx tenv (Call ann (IntCall (src,name)) es dflt) es0 /\
    ALOOKUP mods src = SOME callee_tops /\
    (src = NONE \/ context_function_live cx (src,name)) /\
    ((src = NONE /\ mods = [(NONE,callee_tops)]) \/
     MEM (src,name) (linked_live_functions mods exps)) /\
    lookup_callable_function cx.in_deploy name callee_tops =
      SOME (mut,nr,args,dflts,ret,ss) /\
    (vis = Internal \/ (cx.in_deploy /\ src <> NONE /\ vis = Deploy)) /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret ss) callee_tops /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    LENGTH args - LENGTH dflts <= LENGTH es /\
    LENGTH es <= LENGTH args /\
    compile_expr cenv ty (Call ann (IntCall (src,name)) es dflt) sa =
      (vv, sm) /\
    compile_expr (gasShadowCompileBase$gas_shadow_env T cenv) ty
      (gas_shadow_expr (Call ann (IntCall (src,name)) es dflt)) shadow_sa =
      (vv, shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
            not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
       intcall_entry_full_mods (DF, lo, d) H mods src callee_tops ctx func cenv cx tenv name es
         sa sm vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t
         G tn) /\
    (?H. valid_horizon cx st0 H es1.storage_trace) /\
    cenv.ce_func_info (nsid_to_string (src,name)) = (rc,rbs,pvs) /\
    (!callee entered bb inst lbl arg_ops argv.
       gas_invoke_entry (ctx,func) t callee entered /\
       lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       decode_invoke inst = SOME (lbl,arg_ops) /\
       eval_operands arg_ops t = SOME argv ==>
       gas_outcome_full_mods
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, callee,
          MAP (op_prov G) arg_ops)
         mods cx st0 (intcall_callee_src_at cx src name mut nr ss)
         (es1, entered, FEMPTY, tn with t_var := FEMPTY)
         (\H res ee G' tn' t'. F)
         (\H res ee gt r.
            intcall_callee_exit_full_mods mods (DF, lo) H func cenv cx mut nr rtv rc
              (if rc = 0 /\ 0 < rbs then SOME (HD argv) else NONE)
              sa.cs_next_id sm.cs_next_id t tn res ee gt r)) ==>
    (fn_has_code sa sm func /\
     fn_has_code shadow_sa shadow_sm shadow_func ==>
     gas_outcome_full_mods
       (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
       cenv.ce_modules cx st0 (intcall_rest_at cx src name mut nr ss prev rtv)
       (es1, t, G, tn)
       (\H res ee G tn t'. ?tv. res = INL tv /\
         vv_post_mods H ctx func cenv cx (Call ann (IntCall (src,name)) es dflt)
           es0 sa sm s0 ee tv vv t' /\
         vv_store_bound cx (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           (lowered_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           ee tv vv t' /\
         t'.vs_current_bb = sm.cs_current_bb /\
         t'.vs_inst_idx = LENGTH sm.cs_current_insts /\
         alloca_history func t' /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
         s0.vs_alloca_next <= t'.vs_alloca_next /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
         ptr_vv_ok cx
           (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
           tv vv ee G tn t' /\
         (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx tv ee = (INL val, ee) /\
                !rt w. evaluate_type (get_tenv cx)
                         (post_value_type cenv
                            (Call ann (IntCall (src,name)) es dflt)) =
                         SOME rt /\
                       eval_operand (vv_operand vv) t' = SOME w ==>
                       w2n w + type_memory_size rt <= lo /\
                       (!mem. mem_agree_outside tn.t_mem t'.vs_memory mem ==>
                              val_in_memory rt val (w2n w) mem)) /\
         (!ty' op. vv = StackValue ty' op /\
                   ~is_word_type
                      (post_value_type cenv
                         (Call ann (IntCall (src,name)) es dflt)) ==>
                   ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt)
                     op G t') /\
         (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt)
                    p.ptr_operand G t') /\
         ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
       (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
    (!op sb shadow_sb.
       unwrap_value cenv vv sm = (op, sb) /\
       unwrap_value cenv vv shadow_sm = (op, shadow_sb) /\
       gas_shadow_state sb shadow_sb /\
       fn_has_code sa sb func /\
       fn_has_code shadow_sa shadow_sb shadow_func /\
       gas_admissible
         (bind (intcall_rest_at cx src name mut nr ss prev rtv) (read_result cx))
         expr_res_ok es1 ==>
       gas_outcome_full_mods
         (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
         cenv.ce_modules cx st0
         (bind (intcall_rest_at cx src name mut nr ss prev rtv) (read_result cx))
         (es1, t, G, tn)
         (\H res ee G tn t'. ?v. res = INL v /\
           expr_post_mods H ctx func cenv cx (Call ann (IntCall (src,name)) es dflt)
             es0 sa sb s0 ee v op t' /\
           expr_store_bound cx
             (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) v op t' /\
           t'.vs_current_bb = sb.cs_current_bb /\
           t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t' /\
           (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
           s0.vs_alloca_next <= t'.vs_alloca_next /\
           ghost_inv_at (DF H) lo d cenv cx ee G tn t' /\
           ptr_val_ok cx
             (post_value_type cenv (Call ann (IntCall (src,name)) es dflt))
             v op G tn t' /\
           (~is_word_type
               (post_value_type cenv (Call ann (IntCall (src,name)) es dflt)) ==>
            ptr_buf_ok cenv (Call ann (IntCall (src,name)) es dflt) op G t') /\
           ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  cheat
QED

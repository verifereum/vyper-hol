(* Linked source inputs at the three ExtCall operand cuts. *)
Theory bodyExtRequestInputsMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods bodyBranchCellFrameMods
  exprBodyPreProps exprSimHypsDefs exprSimSource supportedExprTraverse
  allocLimits vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeExprSoundness list rich_list arithmetic
Libs monadsyntax

Theorem ext_call_typing[local]:
  well_typed_expr env (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) ==>
  ann = rt /\ dr = NONE /\ ext_call_opts_ok stat opts /\
  (rt = NoneT ==> ~MEM EKDefault opts) /\
  LENGTH args = 1 + LENGTH ats + LENGTH opts /\
  MAP expr_type (TAKE 1 args) = [BaseT AddressT] /\
  arg_types_fit (MAP expr_type (TAKE (LENGTH ats) (DROP 1 args))) ats /\
  MAP expr_type (DROP (1 + LENGTH ats) args) = MAP (ext_call_kw_type rt) opts
Proof
  simp[Once well_typed_expr_def] >> strip_tac >>
  Cases_on `args` >> gvs[ADD1]
QED

Theorem ext_call_operand_pre[local]:
  expr_body_pre_mods mods ce cx env
    (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env st ==>
  expr_body_pre_mods mods ce cx env e st
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def] >>
  strip_tac >> gvs[int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def] >>
  drule_all_then assume_tac well_typed_exprs_member >>
  drule_all_then assume_tac byte_widths_exprs_mem >>
  drule_all_then assume_tac alloc_limits_exprs_mem >>
  drule_all_then assume_tac call_evaluation_safe_exprs_mem >>
  drule_all_then assume_tac int_calls_exprs_every_mem >>
  `!p. supported_expr_exists p e ==>
       supported_expr_exists p (Call ann (ExtCall stat skip (name,ats,ann) opts) args NONE)` by
    (simp[Once supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
     metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- (qpat_x_assum `~expr_has_evm_run (Call _ _ _ _)` mp_tac >>
      simp[expr_has_evm_run_thm, EXISTS_MEM] >> metis_tac[])
  >- metis_tac[]
  >- metis_tac[]
  >> metis_tac[]
QED

Theorem ext_operand_list_success[local]:
  !args es vs ee.
    expr_sim_inv_mods mods ce cx env es /\ body_const_cells_agree_mods mods cx env es /\
    (!e st. MEM e args /\ expr_sim_inv_mods mods ce cx env st ==>
            expr_body_pre_mods mods ce cx env e st) /\
    eval_exprs cx args es = (INL vs,ee) ==>
    expr_sim_inv_mods mods ce cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
    LIST_REL (\e v. value_runtime_typed env (expr_type e) v) args vs
Proof
  Induct >> rpt gen_tac
  >- (simp[Once evaluate_def, return_def] >> metis_tac[]) >>
  simp[Once evaluate_def, bind_assoc] >>
  simp[bind_apply, return_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_expr cx e es = (INL raw,at_raw)` >>
  rename1 `read_result cx raw at_raw = (INL v,mid)` >>
  `expr_body_pre_mods mods ce cx env e es` by simp[] >>
  `bind (eval_expr cx e) (read_result cx) es = (INL v,mid)` by simp[bind_def] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  rename1 `eval_exprs cx args mid = (INL tail_values,ee)` >>
  qpat_x_assum `!es vs ee. _ ==> _` (qspecl_then [`mid`,`tail_values`,`ee`] mp_tac) >>
  simp[]
QED

(* Refreshing the gas observations between cuts is allowed, but later
   inputs are issued only after success of the actual preceding cuts. *)
Theorem ext_request_inputs_mods:
  expr_body_pre_mods mods ce cx env
    (Call ann (ExtCall stat skip (name,ats,rt) opts) args dr) es /\
  body_const_cells_agree_mods mods cx env es /\
  body_exprs_full_ok_mods mods exps cx (TAKE 1 args) /\
  (!st target mid. eval_exprs cx (TAKE 1 args) st = (INL target,mid) ==>
    body_exprs_full_ok_mods mods exps cx (TAKE (LENGTH ats) (DROP 1 args))) /\
  (!st target mid src vs ee.
    eval_exprs cx (TAKE 1 args) st = (INL target,mid) /\
    eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) src = (INL vs,ee) ==>
    body_exprs_full_ok_mods mods exps cx (DROP (1 + LENGTH ats) args)) ==>
  (ann = rt /\ dr = NONE /\ ext_call_opts_ok stat opts /\
   (rt = NoneT ==> ~MEM EKDefault opts) /\
   LENGTH args = 1 + LENGTH ats + LENGTH opts /\
   MAP expr_type (TAKE 1 args) = [BaseT AddressT] /\
   arg_types_fit (MAP expr_type (TAKE (LENGTH ats) (DROP 1 args))) ats /\
   MAP expr_type (DROP (1 + LENGTH ats) args) = MAP (ext_call_kw_type rt) opts) /\
  expr_sim_inv_mods mods ce cx env es /\
  body_exprs_full_ok_mods mods exps cx (TAKE 1 args) /\
  (!e st. MEM e args /\ expr_sim_inv_mods mods ce cx env st ==>
          expr_body_pre_mods mods ce cx env e st) /\
  (!obs1 target mid.
    eval_exprs cx (TAKE 1 args) (es with gas_obs := obs1) = (INL target,mid) ==>
    expr_sim_inv_mods mods ce cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
    LIST_REL (\e v. value_runtime_typed env (expr_type e) v) (TAKE 1 args) target /\
    body_exprs_full_ok_mods mods exps cx (TAKE (LENGTH ats) (DROP 1 args)) /\
    (!obs2 vs ee.
      eval_exprs cx (TAKE (LENGTH ats) (DROP 1 args)) (mid with gas_obs := obs2) = (INL vs,ee) ==>
      expr_sim_inv_mods mods ce cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
      LIST_REL (\e v. value_runtime_typed env (expr_type e) v)
        (TAKE (LENGTH ats) (DROP 1 args)) vs /\
      body_exprs_full_ok_mods mods exps cx (DROP (1 + LENGTH ats) args) /\
      (!obs3 kws out.
        eval_exprs cx (DROP (1 + LENGTH ats) args) (ee with gas_obs := obs3) = (INL kws,out) ==>
        expr_sim_inv_mods mods ce cx env out /\ body_const_cells_agree_mods mods cx env out /\
        LIST_REL (\e v. value_runtime_typed env (expr_type e) v)
          (DROP (1 + LENGTH ats) args) kws)))
Proof
  strip_tac >>
  conj_tac
  >- drule_then (ACCEPT_TAC o MATCH_MP ext_call_typing) expr_body_pre_mods_well_typed >>
  conj_tac >- (drule expr_body_pre_mods_inv >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `!e st. MEM e args /\ expr_sim_inv_mods mods ce cx env st ==>
          expr_body_pre_mods mods ce cx env e st` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC ext_call_operand_pre) >>
  pop_assum (mk_asm "child") >>
  conj_tac >- asm "child" ACCEPT_TAC >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv_mods mods ce cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
   LIST_REL (\e v. value_runtime_typed env (expr_type e) v) (TAKE 1 args) target` by
    (irule ext_operand_list_success >>
     qpat_assum `eval_exprs cx (TAKE 1 args) _ = _` (irule_at Any) >>
     simp[] >> rpt strip_tac >> asm "child" irule >> metis_tac[MEM_TAKE]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv_mods mods ce cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
   LIST_REL (\e v. value_runtime_typed env (expr_type e) v)
     (TAKE (LENGTH ats) (DROP 1 args)) vs` by
    (irule ext_operand_list_success >>
     qpat_assum `eval_exprs cx (TAKE _ (DROP 1 _)) _ = _` (irule_at Any) >>
     simp[] >> rpt strip_tac >> asm "child" irule >> metis_tac[MEM_TAKE, MEM_DROP_IMP]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `!st target mid src vs ee. _ ==> _` (irule o ONCE_REWRITE_RULE [ADD_COMM]) >>
      conj_tac >> goal_assum (drule_at Any)) >>
  rpt gen_tac >> strip_tac >>
  irule ext_operand_list_success >>
  qpat_assum `eval_exprs cx (DROP (LENGTH ats + 1) args) _ = _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> asm "child" irule >> metis_tac[MEM_DROP_IMP]
QED

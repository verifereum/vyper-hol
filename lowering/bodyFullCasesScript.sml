(* The cases of bodySimFullMain's induction, one per evaluate_ind case
 * bodySimPtrMainAt's does not close by a short tactic, at the joint
 * judgments of bodySimFull.  A case with an existing joint producer is
 * proved here; every other case is admitted until its leaf lands, and its
 * comment names the separate source, memory and pointer cases it joins.
 *
 * TOP-LEVEL: body_expr_full_ok_leaf and the body_*_case_full cases.
 *)
Theory bodyFullCases
Ancestors
  bodyFullPreds bodySimFull stmtSimZero stmtSimPass gasShadow bodySim
  exprSimHyps bodySimStmtCases bodyExprPreFacts supportedStmts
  supportedExprs supportedStmtTraverse supportedExprTraverse
  bodyMemBiEnvMsgGas exprSimHypsDefs gasContext vyperTypeSystem vyperContext vyperTypeCallGraph
  vyperAST vyperInterpreter vyperState vyperValue list

val _ = Parse.hide "body";

(* Admitted: the joint twin of body_expr_ptr_ok_at_leaf (bodySimPtrMain). *)
Theorem body_expr_full_ok_leaf:
  !cx e.
    (?a id. e = Name a id) \/ (?a nsid. e = TopLevelName a nsid) \/
    (?a nsid mid. e = FlagMember a nsid mid) \/ (?a l. e = Literal a l) ==>
    body_expr_full_ok cx e
Proof
  cheat
QED

(* Admitted: the joint twin of body_annassign_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_annassign_case_full:
  !cx id typ e.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (AnnAssign id typ e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_append_case_ptr_at (bodyPtrLogCases). *)
Theorem body_append_case_full:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (Append t e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_assert_case_ptr_at (bodyPtrExitCases). *)
Theorem body_assert_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertBare)
Proof
  cheat
QED

(* Admitted: the joint twin of body_assert_reason_case_ptr_at (bodyPtrExitCases). *)
Theorem body_assert_reason_case_full:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_full_ok cx se) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED

(* Admitted: the joint twin of body_assert_unreachable_case_ptr_at (bodyPtrExitCases). *)
Theorem body_assert_unreachable_case_full:
  !cx e.
    body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertUnreachable)
Proof
  cheat
QED

(* Admitted: the joint twin of body_assign_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_assign_case_full:
  !cx t e.
    (!s'' pv t'.
       eval_expr cx e s'' = (INL pv,t') ==> body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assign (BaseTarget t) e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_assign_tuple_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_assign_tuple_case_full:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (Assign (TupleTarget gs) e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_attribute_case_ptr_at (bodyPtrExprCases). *)
Theorem body_attribute_case_full:
  !cx v9 e id. body_expr_full_ok cx e ==> body_expr_full_ok cx (Attribute v9 e id)
Proof
  cheat
QED

(* Admitted: the joint twin of body_augassign_case_ptr_at (bodyPtrAssignCases). *)
Theorem body_augassign_case_full:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\ body_base_target_full_ok cx t ==>
    body_stmt_full_ok cx (AugAssign ty t bop e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_break_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_break_case_full:
  !cx. body_stmt_full_ok cx Break
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrEnvBuiltins's env_builtin_expr_ptr_ok, without Env MsgGas. *)
Theorem env_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrBopIn's bop_in_expr_ptr_ok. *)
Theorem bop_in_expr_full_ok:
  !cx ty bop es.
    (bop = In \/ bop = NotIn) /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrBop's bop_expr_ptr_ok. *)
Theorem bop_expr_full_ok:
  !cx ty bop es.
    bop <> In /\ bop <> NotIn /\
    (builtin_args_length_ok (Bop bop) (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty (Bop bop) es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrMakeArray's make_array_expr_ptr_ok. *)
Theorem make_array_expr_full_ok:
  !cx ty bt es.
    (?t n. bt = MakeArray t n) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrWordBuiltins's word_builtin_expr_ptr_ok. *)
Theorem word_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrHashBuiltins's hash_builtin_expr_ptr_ok. *)
Theorem hash_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrBytestringBuiltins's bytestring_builtin_expr_ptr_ok. *)
Theorem bytestring_builtin_expr_full_ok:
  !cx ty bt es.
    ((?n. bt = CalldataSlice n) \/ (?n. bt = Concat n) \/ (?n. bt = Slice n) \/
     (?n. bt = Uint2Str n)) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* Admitted: the joint twin of bodyPtrPrecompileBuiltins's precompile_builtin_expr_ptr_ok. *)
Theorem precompile_builtin_expr_full_ok:
  !cx ty bt es.
    (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  cheat
QED

(* msg.gas, by bodyMemBiEnvMsgGas's joint fragment: typing fixes the
   annotation and the empty argument list. *)
Theorem body_msg_gas_full_case:
  !cx ann args. body_expr_full_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_full_ok_def] >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[compile_msg_gas_sim_full]
QED

(* A builtin, split by family as body_builtin_case_ptr does. *)
Theorem body_builtin_case_full:
  !cx ty bt es.
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len /\ bt <> Env MsgGas ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok cx (HD es)) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bt = Env MsgGas` >- simp[body_msg_gas_full_case] >>
  `builtin_args_length_ok bt (LENGTH es) /\ bt <> Len ==>
   body_exprs_full_ok cx es` by
    (strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def]) >>
  Cases_on `bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/ (?i. bt = Acc i) \/
             bt = BlockHash \/ bt = BlobHash \/ bt = MethodId`
  >- (irule env_builtin_expr_full_ok >> rpt conj_tac >> gvs[] >>
      metis_tac[]) >>
  Cases_on `?bop. bt = Bop bop`
  >- (gvs[] >> Cases_on `bop = In \/ bop = NotIn`
      >- (irule bop_in_expr_full_ok >> gvs[]) >>
      irule bop_expr_full_ok >> gvs[]) >>
  Cases_on `bt` >> gvs[] >>
  FIRST (map (fn th => irule th >> simp[] >> NO_TAC)
    [make_array_expr_full_ok, word_builtin_expr_full_ok,
     hash_builtin_expr_full_ok, bytestring_builtin_expr_full_ok,
     precompile_builtin_expr_full_ok])
QED

(* Admitted: the joint twin of body_continue_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_continue_case_full:
  !cx. body_stmt_full_ok cx Continue
Proof
  cheat
QED

(* Admitted: the joint twin of body_create_case_ptr_at (bodyPtrCallCases). *)
Theorem body_create_case_full:
  !cx ty kind has_salt rof v26 es v27.
    (!raw_args s'' prefix t s'3' code_size t'.
       kind = CreateFromBlueprint raw_args /\
       eval_exprs cx (TAKE (if has_salt then 4 else 3) es) s'' =
       (INL prefix,t) /\
       check_create_blueprint has_salt prefix s'3' = (INL code_size,t') ==>
       body_results_full_ok cx (DROP (if has_salt then 4 else 3) es)) /\
    (!raw_args.
       kind = CreateFromBlueprint raw_args ==>
       body_exprs_full_ok cx (TAKE (if has_salt then 4 else 3) es)) /\
    (!s'' prefix t ctor_es nargs s'3' results t' s'4' args t''.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) /\
       eval_expr_results cx (TAKE nargs ctor_es) s'3' = (INL results,t') /\
       read_results cx results s'4' = (INL args,t'') ==>
       body_exprs_full_ok cx (DROP nargs ctor_es)) /\
    (!s'' prefix t ctor_es nargs.
       kind = RawCreate /\ eval_exprs cx (TAKE 2 es) s'' = (INL prefix,t) /\
       ctor_es = DROP 2 es /\
       nargs = LENGTH ctor_es - (if has_salt then 1 else 0) ==>
       body_results_full_ok cx (TAKE nargs ctor_es)) /\
    (kind = CreateCopyOf ==> body_exprs_full_ok cx es) /\
    (kind = CreateMinimalProxy ==> body_exprs_full_ok cx es) /\
    (kind = RawCreate ==> body_exprs_full_ok cx (TAKE 2 es)) ==>
    body_expr_full_ok cx (Call ty (CreateTarget kind has_salt rof v26) es v27)
Proof
  cheat
QED

(* Admitted: the joint twin of body_expr_stmt_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_expr_stmt_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Expr e)
Proof
  cheat
QED

(* Admitted: the joint twin of body_extcall_case_ptr_at (bodyPtrCallCases). *)
Theorem body_extcall_case_full:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_full_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_full_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_full_ok cx (TAKE 1 es) ==>
    body_expr_full_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED

(* Admitted: the joint twin of body_for_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_for_case_full:
  !cx id typ it n body.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx it s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx it) ==>
    body_stmt_full_ok cx (For id typ it n body)
Proof
  cheat
QED

(* Admitted: the joint twin of body_if_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_if_case_full:
  !cx e ss1 ss2.
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss1) /\
    (!s'' tv t s'3' x t'.
       eval_expr cx e s'' = (INL tv,t) /\ push_scope s'3' = (INL x,t') ==>
       body_stmts_full_ok cx ss2) /\ body_expr_full_ok cx e ==>
    body_stmt_full_ok cx (If e ss1 ss2)
Proof
  cheat
QED

(* Admitted: the joint twin of body_ifexp_case_ptr_at (bodyPtrExprCases). *)
Theorem body_ifexp_case_full:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_full_ok cx e3) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (IfExp v5 e1 e2 e3)
Proof
  cheat
QED

(* Admitted: the joint twin of body_intcall_case_ptr_at (bodyPtrIntCallCase). *)
Theorem body_intcall_case_full:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8'
         s'11' rtv t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\ all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_full_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_full_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_full_ok cx es) ==>
    body_expr_full_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  cheat
QED

(* Admitted: the joint twin of body_log_case_ptr_at (bodyPtrLogCases). *)
Theorem body_log_case_full:
  !cx id es. body_exprs_full_ok cx es ==> body_stmt_full_ok cx (Log id es)
Proof
  cheat
QED

(* Pass, by stmtSimPass's joint fragment. *)
Theorem body_pass_case_full:
  !cx. body_stmt_full_ok cx Pass
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def, compile_pass_frag_full]
QED

(* Admitted: the joint twin of body_pop_case_ptr_at (bodyPtrExprCases). *)
Theorem body_pop_case_full:
  !cx v10 bt. body_base_target_full_ok cx bt ==> body_expr_full_ok cx (Pop v10 bt)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raise_bare_case_ptr_at (bodyPtrExitCases). *)
Theorem body_raise_bare_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseBare)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raise_reason_case_ptr_at (bodyPtrExitCases). *)
Theorem body_raise_reason_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

(* Admitted: the joint twin of body_raise_unreachable_case_ptr_at (bodyPtrExitCases). *)
Theorem body_raise_unreachable_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseUnreachable)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raw_call_calldata_case_ptr_at (bodyPtrCallCases). *)
Theorem body_raw_call_calldata_case_full:
  !cx ty flags es v19.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallCalldataTarget flags) es v19)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raw_call_case_ptr_at (bodyPtrCallCases). *)
Theorem body_raw_call_case_full:
  !cx ty flags es v18.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (RawCallTarget flags) es v18)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raw_log_case_ptr_at (bodyPtrCallCases). *)
Theorem body_raw_log_case_full:
  !cx v20 es v21.
    body_exprs_full_ok cx es ==> body_expr_full_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED

(* Admitted: the joint twin of body_raw_revert_case_ptr_at (bodyPtrCallCases). *)
Theorem body_raw_revert_case_full:
  !cx v22 es v23.
    body_exprs_full_ok cx es ==> body_expr_full_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED

(* Return e, by the frame's own joint Return fragment and e's case. *)
Theorem body_return_case_full:
  !cx e. body_expr_full_ok cx e ==> body_stmt_full_ok cx (Return (SOME e))
Proof
  rw[body_stmt_full_ok_def, frame_ret_ok_full_def, gas_shadow_stmt_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum (qspecl_then [`cenv`, `env`, `lctx`, `SOME e`, `es`] mp_tac) >>
  simp[same_frame_refl] >> disch_then irule >>
  fs[body_expr_full_ok_def] >> metis_tac[]
QED

(* Return, by the frame's own joint Return fragment. *)
Theorem body_return_none_case_full:
  !cx. body_stmt_full_ok cx (Return NONE)
Proof
  rw[body_stmt_full_ok_def, frame_ret_ok_full_def, gas_shadow_stmt_def] >>
  first_x_assum (qspecl_then [`cenv`, `env`, `lctx`, `NONE`, `es`] mp_tac) >>
  simp[same_frame_refl]
QED

(* Admitted: the joint twin of body_selfdestruct_case_ptr_at (bodyPtrCallCases). *)
Theorem body_selfdestruct_case_full:
  !cx v24 es v25.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  cheat
QED

(* Admitted: the joint twin of body_send_case_ptr_at (bodyPtrCallCases). *)
Theorem body_send_case_full:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Call v12 (Send has_gas) es v13)
Proof
  cheat
QED

(* Admitted: the joint twin of body_stmts_cons_case_ptr_at (bodyPtrCtrlCases). *)
Theorem body_stmts_cons_case_full:
  !cx s ss.
    (!s'' x t. eval_stmt cx s s'' = (INL x,t) ==> body_stmts_full_ok cx ss) /\
    body_stmt_full_ok cx s ==>
    body_stmts_full_ok cx (s::ss)
Proof
  cheat
QED

(* The empty list, by stmtSimZero's joint fragment. *)
Theorem body_stmts_nil_case_full:
  !cx. body_stmts_full_ok cx []
Proof
  rw[body_stmts_full_ok_def, stmt_frag_nil_full]
QED

(* Admitted: the joint twin of body_structlit_case_ptr_at (bodyPtrExprCases). *)
Theorem body_structlit_case_full:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_full_ok cx (MAP SND kes)) ==>
    body_expr_full_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  cheat
QED

(* Admitted: the joint twin of body_subscript_case_ptr_at (bodyPtrExprCases). *)
Theorem body_subscript_case_full:
  !cx v8 e1 e2.
    (!s'' res t. eval_expr cx e1 s'' = (INL res,t) ==> body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 ==>
    body_expr_full_ok cx (Subscript v8 e1 e2)
Proof
  cheat
QED

(* Admitted: the joint twin of body_type_builtin_case_ptr_at (bodyPtrExprCases). *)
Theorem body_type_builtin_case_full:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 tb typ es)
Proof
  cheat
QED

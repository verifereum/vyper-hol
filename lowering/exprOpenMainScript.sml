(*
 * compile_expr keeps its block open
 *
 * TOP-LEVEL:
 *   compile_expr_open_general — a well-typed expression that evaluates
 *     compiles, at any annotated type, without terminating its block:
 *     bodySimStmtCases's compile_expr_open
 *   supported_immutable_bound — a supported immutable is bound
 *     in ce_module_vars
 *)

Theory exprOpenMain
Ancestors
  exprSimHypsDefs
  exprOpenDispatch exprOpenFirstOperand exprOpenChild exprOpenCases
  exprOpenPrimitives exprOpenCopies exprOpenTerminals exprOpenBuiltins
  bodySim  supportedExprs supportedExprForms supportedTypes
  exprLowering exprCallBounds compileEnv vyperAST vyperTypeSystem list
  supportedDecls vyperTypeInvariants
  whitelistExprOpen whitelistCheckerTypes exprSimTopLevelProps
  vyperTypeGlobalLookupSoundness allocLimits supportedExprTraverse
  vyperInterpreter vyperState

Theorem supported_variable_decl_mem[local]:
  !tops src id vis mut ty slot.
    supported_variable_decl tops (src, id) = SOME (vis, mut, ty, slot) ==>
    src = NONE /\ MEM (VariableDecl vis mut id ty slot) tops
Proof
  Induct >> simp[supported_variable_decl_def] >> Cases >>
  rw[supported_variable_decl_def] >> metis_tac[]
QED

(* Context consistency installs the declaration in bare_globals;
   expr_sim_inv supplies its compiler location. *)
Theorem supported_immutable_bound:
  !tops ctx cenv cx env es nsid ty.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    supported_immutable_type tops nsid = SOME ty ==>
    ?off. FLOOKUP cenv.ce_module_vars nsid = SOME (ImmutableLoc off)
Proof
  rpt gen_tac >> PairCases_on `nsid` >> strip_tac >>
  qpat_x_assum `supported_immutable_type _ _ = _` mp_tac >>
  simp[supported_immutable_type_def] >>
  Cases_on `supported_variable_decl tops (nsid0, nsid1)` >> simp[] >>
  rename1 `supported_variable_decl tops (nsid0, nsid1) = SOME decl` >>
  PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >> gvs[] >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   bare_globals_complete env.bare_globals cx` by
    fs[body_inv_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `?t. FLOOKUP env.bare_globals (NONE, nsid1) = SOME t` by
    metis_tac[bare_globals_complete_def] >>
  fs[expr_sim_inv_def] >> metis_tac[]
QED

Theorem compile_expr_open_general:
  !e tops ctx cenv cx env es tv es1 aty sa vv sb.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env e es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx e es = (INL tv,es1) /\
    compile_expr cenv aty e sa = (vv,sb) /\
    ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >> strip_tac >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  Cases_on `e`
  >~ [`compile_expr _ _ (Name _ _) _ = _`]
    >- (irule compile_expr_name_open >>
        goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
        gvs[expr_body_pre_def] >> metis_tac[])
  >~ [`compile_expr _ _ (TopLevelName _ _) _ = _`]
    >- suspend "toplevel"
  >~ [`compile_expr _ _ (Literal _ _) _ = _`]
    >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
        simp[Once compile_expr_def] >> strip_tac >>
        drule_all compile_literal_vv_open >> simp[])
  >~ [`compile_expr _ _ (FlagMember _ _ _) _ = _`]
    >- metis_tac[compile_flag_member_open]
  >~ [`compile_expr _ _ (Builtin _ _ _) _ = _`] >- suspend "builtin"
  >~ [`compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "type_builtin" >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _ = _`]
    >- metis_tac[compile_ifexp_open]
  >~ [`compile_expr_body _ _ _ _ _ (Pop _ _) _ = _`]
    >- metis_tac[compile_pop_body_open]
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _ = _`]
    >- (strip_tac >> irule compile_struct_literal_body_open >>
        goal_assum (drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`)) >>
        gvs[expr_body_pre_def] >> metis_tac[])
  >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _ = _`]
    >- (simp[compile_expr_body_def] >> metis_tac[compile_subscript_open])
  >~ [`compile_expr_body _ _ _ _ _ (Attribute _ _ _) _ = _`]
    >- (simp[compile_expr_body_def] >> metis_tac[compile_attribute_open]) >>
  simp[compile_expr_body_def] >> strip_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  fs[expr_body_pre_def, expr_has_evm_run_thm] >>
  metis_tac[compile_call_open]
QED

Resume compile_expr_open_general[toplevel]:
  rename1 `TopLevelName ann nsid` >>
  qpat_x_assum `!y. _` kall_tac >>
  PairCases_on `nsid` >>
  `expr_sim_inv cenv cx env es /\
   well_typed_expr env (TopLevelName ann (nsid0,nsid1))` by
    fs[expr_body_pre_def] >>
  Cases_on `get_module_code cx nsid0`
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, vyperStateTheory.lookup_global_def,
           vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
           vyperStateTheory.raise_def]) >>
  rename1 `get_module_code cx nsid0 = SOME ts` >>
  Cases_on `find_var_decl_by_name nsid1 ts`
  >- (`FLOOKUP env.bare_globals (nsid0,nsid1) = SOME ann` by
        (irule toplevel_find_NONE_bare_global >>
         fs[expr_sim_inv_def] >> metis_tac[]) >>
      `?off. FLOOKUP cenv.ce_module_vars (nsid0,nsid1) = SOME (ImmutableLoc off)` by
        (fs[expr_sim_inv_def] >> metis_tac[]) >>
      gvs[compile_expr_def]) >>
  rename1 `find_var_decl_by_name nsid1 ts = SOME di` >> PairCases_on `di` >>
  Cases_on `di0`
  >~ [`HashMapVarDecl`]
    >- (fs[expr_sim_inv_def] >>
        metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]) >>
  drule_all eval_toplevel_decl_bound >> strip_tac >> gvs[compile_expr_def]
QED

Resume compile_expr_open_general[builtin]:
  rename1 `compile_expr cenv aty (Builtin ann bi args) sa = (vv,sb)` >>
  `!arg rest. args = arg::rest /\ (!n. bi <> Slice n) ==>
     !cty v st. lower_value
       (expr_child_callback (list_size expr_size args) compile_expr)
       cenv cty arg sa = (v,st) ==> ~block_is_terminated st` by
    (rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
     drule_at (Pat `lower_value _ _ _ _ _ = _`) lower_value_child_open >>
     simp[] >> disch_then irule >>
     rpt gen_tac >> strip_tac >>
     drule eval_builtin_head_success >> strip_tac >>
     drule expr_body_pre_builtin_head >>
     impl_tac >- simp[] >>
     disch_tac >>
     qpat_x_assum `!y. expr_size y < _ ==> _` irule >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     simp[expr_size_def] >> metis_tac[expr_list_member_bound, MEM]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`) compile_builtin_body_open >>
  disch_then irule >>
  simp[builtin_child_callback_def, expr_size_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  suspend "builtin_dispatch"
QED

Resume compile_expr_open_general[type_builtin]:
  rename1 `compile_expr cenv aty (TypeBuiltin ann tb rty args) sa = (vv,sb)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, type_child_callback_def, expr_size_def,
       vyperASTTheory.expr_type_def] >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  Cases_on `tb`
  >~ [`Empty`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`MaxValue`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`MinValue`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`Epsilon`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`AbiEncode`] >- metis_tac[compile_type_dispatch_abi_open]
  >~ [`AbiDecode`] >- metis_tac[compile_type_dispatch_abi_open]
  >~ [`Extract32`]
    >- metis_tac[compile_extract32_open] >>
  `LENGTH args = 1` by
    (fs[expr_body_pre_def, well_typed_expr_def] >>
     drule well_typed_type_builtin_args_arity >> simp[]) >>
  Cases_on `args` >>
  gvs[] >>
  rename1 `TypeBuiltin _ _ _ (arg_e::rest)` >> Cases_on `rest` >>
  gvs[] >>
  drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)
    compile_type_dispatch_convert_open >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) lower_value_child_open >>
  simp[] >> disch_then irule >> rpt gen_tac >> strip_tac >>
  drule eval_type_builtin_head_success >> strip_tac >>
  drule expr_body_pre_type_builtin_head >> disch_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` irule >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[expr_size_def] >> metis_tac[]
QED

Resume compile_expr_open_general[builtin_dispatch]:
  `well_typed_builtin_app ann bi (MAP expr_type args)` by
    fs[expr_body_pre_def, well_typed_expr_def] >>
  drule well_typed_builtin_app_arity >> disch_tac >>
  Cases_on `bi` >> gvs[]
  >~ [`Len`] >- metis_tac[compile_len_open]
  >~ [`CalldataLen`] >- metis_tac[compile_calldatalen_open]
  >~ [`Keccak256`] >- metis_tac[compile_keccak256_open]
  >~ [`Sha256`] >- metis_tac[compile_sha256_open]
  >~ [`Ceil`] >- metis_tac[compile_ceil_open]
  >~ [`Floor`] >- metis_tac[compile_floor_open]
  >~ [`MethodId`] >- metis_tac[compile_method_id_open]
  >~ [`Concat`] >- metis_tac[compile_concat_open]
  >~ [`Slice`] >- metis_tac[compile_slice_open]
  >~ [`Not`] >- metis_tac[compile_dispatch_not_open]
  >~ [`Neg`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Abs`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`AddMod`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`MulMod`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`PowMod256`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Env`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`BlockHash`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`BlobHash`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECRecover`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECAdd`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECMul`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Uint2Str`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`CalldataSlice`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`MakeArray elem bound`]
    >- (Cases_on `elem` >>
        drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
          compile_dispatch_make_array_open >>
        fs[well_typed_builtin_app_def, EVERY_MAP, EVERY_MEM] >> metis_tac[]) >>
  gvs[LENGTH_EQ_NUM_compute]
  >~ [`Bop op`]
    >- (rename1 `compile_builtin_dispatch_body _ _ _ _ (Bop op) [arg_e;arg2_e] sa = (v,st)` >>
        `op <> ExpMod` by
          (strip_tac >> gvs[well_typed_builtin_app_def, well_typed_binop_def]) >>
        gvs[SF ETA_ss] >>
        qspecl_then
          [`expr_child_callback (list_size expr_size [arg_e;arg2_e]) compile_expr`,
           `cenv`, `ann`, `aty`, `op`, `arg_e`, `arg2_e`, `sa`, `v`, `st`]
          mp_tac compile_dispatch_bop_open >>
        simp[expr_size_def, SF ETA_ss] >> disch_then irule >> strip_tac >>
        first_assum (qspec_then `expr_type arg_e` mp_tac) >> simp[])
  >~ [`AsWeiValue`]
    >- (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
          compile_dispatch_as_wei_value_open >> simp[] >>
        disch_then irule >> rpt strip_tac >> gvs[SF ETA_ss] >> metis_tac[]) >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ (Acc item) _ _ = _` >>
  `item <> Code` by fs[expr_body_pre_def, alloc_limits_expr_def] >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    compile_dispatch_acc_open >> simp[] >> disch_then irule >>
  rpt strip_tac >> gvs[SF ETA_ss] >> metis_tac[]
QED

Finalise compile_expr_open_general


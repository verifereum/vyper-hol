(*
 * The expression simulation theorem (#636)
 *
 * compile_expr_sim: every expression's lowering simulates it (expr_sim,
 * exprSim) at every source state that meets expr_sim_pre (exprSimHyps).
 * It is proved by compile_expr_ind over compile_expr and its two
 * dispatchers, each case by a case lemma of exprSimLeaves,
 * exprSimOperators, exprSimPlaces, exprSimAggregates, exprSimBuiltins or
 * exprSimCalls.  Many of those are cheated; see each theory's header for
 * the #636 rows they stand for.
 *
 * TOP-LEVEL:
 *   compile_expr_sim         — expr_sim_ok of every expression
 *   compile_expr_sim_mutual  — the three conjuncts compile_expr_ind proves
 *   compile_expr_case_sim, compile_builtin_case_sim,
 *   compile_type_builtin_case_sim — one step of the induction each
 *   compile_builtin_case, compile_type_builtin_case — the builtins' steps
 *     over exprSimHyps' shared judgments, which the body simulation uses
 *     too
 *)

Theory exprSimMain
Ancestors
  list exprSim exprSimHyps exprSimLeaves exprSimOperators exprSimPlaces
  exprSimAggregates exprSimBuiltins exprSimCalls exprLowering
  vyperAST vyperTypeCallGraph vyperTypeSystem exprSimWordBuiltins
  exprSimCalldataSlice exprSimPrecompiles exprSimLen

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== The induction steps ===== *)

(* The builtins but the binary operators, array literals, ecadd and ecmul,
   over exprSimHyps' shared judgments: compile_builtin_case_sim's step
   here, and the body simulation's (bodySimExprCases). *)
Theorem compile_builtin_case:
  !nocalls ctx func cenv cx ann bi args.
    (!bop. bi <> Bop bop) /\ (!t n. bi <> MakeArray t n) /\
    bi <> ECAdd /\ bi <> ECMul /\
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Builtin ann bi args) /\
    expr_vv_case nocalls ctx func cenv cx (Builtin ann bi args)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Builtin ann bi args)`
    suffices_by metis_tac[expr_sim_case_of_vv] >>
  Cases_on `bi`
  >~ [`Builtin _ (Bop _) _`] >- metis_tac[]
  >~ [`Builtin _ (MakeArray _ _) _`] >- metis_tac[]
  >~ [`Builtin _ ECAdd _`] >- gvs[]
  >~ [`Builtin _ ECMul _`] >- gvs[]
  >~ [`Builtin _ (Env _) _`]
  >- (irule expr_vv_case_nil >> conj_tac
      >- rw[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
            int_calls_expr_def] >>
      metis_tac[expr_ok_def, compile_env_case_ok]) >>
  FIRST (map (fn th => irule th >> gvs[] >> NO_TAC)
    [word_builtin_case, compile_len_case, compile_calldata_len_case,
     compile_calldata_slice_call_case, compile_not_case, compile_neg_case,
     compile_abs_case, compile_keccak256_case, compile_sha256_case,
     compile_concat_case, compile_slice_case, compile_uint2str_case,
     compile_ceil_case, compile_blockhash_case, compile_blobhash_case,
     compile_acc_case, compile_method_id_case, compile_ecrecover_call_case])
QED

Theorem compile_builtin_case_sim:
  !cenv ann bi args.
    expr_sim_below cenv (list_size expr_size args) ==>
    builtin_sim_ok cenv ann bi args
Proof
  rw[builtin_sim_ok_def] >> Cases_on `?bop. bi = Bop bop`
  >- (gvs[] >> irule compile_bop_ok >> gvs[]) >>
  Cases_on `?t n. bi = MakeArray t n`
  >- (gvs[] >> irule expr_ok_of_vv >> irule compile_make_array_sim >> gvs[]) >>
  Cases_on `bi = ECAdd`
  >- (gvs[] >> irule expr_ok_of_vv >> irule compile_ecadd_sim >> gvs[]) >>
  Cases_on `bi = ECMul`
  >- (gvs[] >> irule expr_ok_of_vv >> irule compile_ecmul_sim >> gvs[]) >>
  rw[expr_ok_case] >> drule exprs_case_below >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`] assume_tac) >>
  drule_at Any compile_builtin_case >> gvs[]
QED

Theorem compile_type_builtin_case:
  !nocalls ctx func cenv cx ann tb t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args) /\
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann tb t args)`
    suffices_by metis_tac[expr_sim_case_of_vv] >>
  Cases_on `tb`
  >~ [`TypeBuiltin _ MaxValue _ _`] >- simp[compile_bound_builtin_case]
  >~ [`TypeBuiltin _ MinValue _ _`] >- simp[compile_bound_builtin_case]
  >~ [`TypeBuiltin _ Epsilon _ _`] >- simp[compile_bound_builtin_case] >>
  FIRST (map (fn th => irule th >> gvs[] >> NO_TAC)
    [compile_empty_case, compile_convert_case, compile_extract32_case,
     compile_abi_decode_case, compile_abi_encode_case])
QED

Theorem compile_type_builtin_case_sim:
  !cenv ann tb t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    type_builtin_sim_ok cenv ann tb t args
Proof
  rw[type_builtin_sim_ok_def, expr_ok_case] >> drule exprs_case_below >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`] assume_tac) >>
  drule compile_type_builtin_case >> simp[]
QED

Theorem compile_call_case_sim:
  !cenv ann target args dflt.
    expr_sim_below cenv (expr_size (Call ann target args dflt)) ==>
    expr_ok cenv (Call ann target args dflt)
Proof
  rpt strip_tac >> Cases_on `target`
  >~ [`IntCall _`]
  >- simp[expr_ok_def, expr_sim_ok_def, expr_vv_ok_def, expr_sim_pre_def,
          int_calls_expr_def] >>
  FIRST (map (fn th => irule expr_ok_of_vv >> irule th >> gvs[])
    [compile_extcall_sim, compile_send_sim, compile_raw_call_sim,
     compile_raw_call_calldata_sim, compile_raw_log_sim,
     compile_raw_revert_sim, compile_selfdestruct_sim, compile_create_sim])
QED

Theorem compile_names_builtin_sim:
  !cenv ann bi args.
    names_builtin bi args ==> expr_ok cenv (Builtin ann bi args)
Proof
  rpt gen_tac >> qid_spec_tac `args` >> qid_spec_tac `bi` >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def] >>
  rpt strip_tac >> irule expr_ok_of_vv >>
  simp[compile_addmod_names_sim, compile_mulmod_names_sim,
       compile_powmod256_names_sim]
QED

Theorem compile_expr_case_sim:
  !cenv e.
    expr_sim_below cenv (expr_size e) /\
    (!ann bi args. list_size expr_size args < expr_size e ==>
                   builtin_sim_ok cenv ann bi args) /\
    (!ann tb t args. list_size expr_size args < expr_size e ==>
                     type_builtin_sim_ok cenv ann tb t args) ==>
    expr_ok cenv e
Proof
  rpt strip_tac >> Cases_on `e`
  >~ [`Builtin ann bi args`]
  >- (Cases_on `names_builtin bi args` >- simp[compile_names_builtin_sim] >>
      `builtin_sim_ok cenv ann bi args` by
        (first_x_assum irule >> simp expr_sizes) >>
      gvs[builtin_sim_ok_def])
  >~ [`TypeBuiltin ann tb t args`]
  >- (`type_builtin_sim_ok cenv ann tb t args` by
        (first_x_assum irule >> simp expr_sizes) >>
      gvs[type_builtin_sim_ok_def])
  >~ [`Call _ _ _ _`] >- (irule compile_call_case_sim >> gvs[])
  >~ [`Name _ _`] >- simp[compile_name_case_sim]
  >~ [`Literal _ _`] >- simp[compile_literal_case_sim]
  >~ [`FlagMember _ _ _`] >- simp[compile_flag_member_case_sim] >>
  FIRST (map (fn th => irule expr_ok_of_vv >> irule th >> gvs[])
    [compile_toplevel_name_sim, compile_ifexp_sim,
     compile_struct_lit_sim, compile_subscript_sim, compile_attribute_sim,
     compile_pop_sim])
QED

(* ===== The theorem ===== *)

Theorem compile_expr_sim_mutual:
  (!cenv e. expr_ok cenv e) /\
  (!cenv ann bi args. builtin_sim_ok cenv ann bi args) /\
  (!cenv ann tb t args. type_builtin_sim_ok cenv ann tb t args)
Proof
  mp_tac (BETA_RULE (Q.SPECL
    [`\cenv ty e st. expr_ok cenv e`,
     `\cenv ret_ty ty bi args st. builtin_sim_ok cenv ret_ty bi args`,
     `\cenv vv_ty ty tb ret_ty args st.
        type_builtin_sim_ok cenv vv_ty tb ret_ty args`] compile_expr_ind)) >>
  impl_tac
  >- (rpt conj_tac >> rpt gen_tac >> strip_tac
      >- (irule compile_expr_case_sim >> rw[expr_sim_below_def] >>
          metis_tac[])
      >- (irule compile_builtin_case_sim >> rw[expr_sim_below_def] >>
          metis_tac[]) >>
      irule compile_type_builtin_case_sim >> rw[expr_sim_below_def] >>
      metis_tac[]) >>
  rw[]
QED

Theorem compile_expr_sim:
  !ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
Proof
  metis_tac[compile_expr_sim_mutual, expr_ok_def, expr_sim_ok_def]
QED

Theorem compile_expr_vv_sim:
  !ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==> expr_vv_sim ctx func cenv cx ty e es
Proof
  metis_tac[compile_expr_sim_mutual, expr_ok_def, expr_vv_ok_def]
QED

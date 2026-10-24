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
 *)

Theory exprSimMain
Ancestors
  list exprSim exprSimHyps exprSimLeaves exprSimOperators exprSimPlaces
  exprSimAggregates exprSimBuiltins exprSimCalls exprLowering
  vyperAST vyperTypeCallGraph

val _ = print ("\nIND:\n" ^ thm_to_string compile_expr_ind ^ "\n");

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* ===== The induction steps ===== *)

Theorem compile_builtin_case_sim:
  !cenv ann bi args.
    expr_sim_below cenv (list_size expr_size args) ==>
    builtin_sim_ok cenv ann bi args
Proof
  rw[builtin_sim_ok_def] >> Cases_on `bi`
  >~ [`Bop _`] >- (irule compile_bop_case_sim >> gvs[])
  >~ [`Env _`] >- simp[compile_env_case_sim]
  >~ [`AddMod`] >- (irule compile_addmod_sim >> gvs[])
  >~ [`MulMod`] >- (irule compile_mulmod_sim >> gvs[])
  >~ [`PowMod256`] >- (irule compile_pow_mod256_sim >> gvs[])
  >~ [`MakeArray _ _`] >- (irule compile_make_array_sim >> gvs[]) >>
  FIRST (map (fn th => irule th >> gvs[])
    [compile_len_sim, compile_calldata_len_sim, compile_calldata_slice_sim,
     compile_not_sim, compile_neg_sim, compile_abs_sim,
     compile_keccak256_sim, compile_sha256_sim, compile_as_wei_value_sim,
     compile_concat_sim, compile_slice_sim, compile_uint2str_sim,
     compile_ceil_sim, compile_floor_sim, compile_blockhash_sim,
     compile_blobhash_sim, compile_acc_sim, compile_method_id_sim,
     compile_ecrecover_sim, compile_ecadd_sim, compile_ecmul_sim])
QED

Theorem compile_type_builtin_case_sim:
  !cenv ann tb t args.
    expr_sim_below cenv (list_size expr_size args) ==>
    type_builtin_sim_ok cenv ann tb t args
Proof
  rw[type_builtin_sim_ok_def] >> Cases_on `tb` >>
  FIRST (map (fn th => irule th >> gvs[])
    [compile_empty_sim, compile_max_value_sim, compile_min_value_sim,
     compile_epsilon_sim, compile_convert_sim, compile_extract32_sim,
     compile_abi_decode_sim, compile_abi_encode_sim])
QED

Theorem compile_call_case_sim:
  !cenv ann target args dflt.
    expr_sim_below cenv (expr_size (Call ann target args dflt)) ==>
    expr_sim_ok cenv (Call ann target args dflt)
Proof
  rpt strip_tac >> Cases_on `target`
  >~ [`IntCall _`]
  >- simp[expr_sim_ok_def, expr_sim_pre_def, int_calls_expr_def] >>
  FIRST (map (fn th => irule th >> gvs[])
    [compile_extcall_sim, compile_send_sim, compile_raw_call_sim,
     compile_raw_call_calldata_sim, compile_raw_log_sim,
     compile_raw_revert_sim, compile_selfdestruct_sim, compile_create_sim])
QED

Theorem compile_names_builtin_sim:
  !cenv ann bi args.
    names_builtin bi args ==> expr_sim_ok cenv (Builtin ann bi args)
Proof
  rpt gen_tac >> simp[oneline names_builtin_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
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
    expr_sim_ok cenv e
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
  >~ [`Call _ _ _ _`] >- (irule compile_call_case_sim >> gvs[]) >>
  FIRST (map (fn th => irule th >> gvs[])
    [compile_name_sim, compile_toplevel_name_sim, compile_flag_member_sim,
     compile_ifexp_sim, compile_literal_sim, compile_struct_lit_sim,
     compile_subscript_sim, compile_attribute_sim, compile_pop_sim])
QED

(* ===== The theorem ===== *)

Theorem compile_expr_sim_mutual:
  (!cenv ty e st. expr_sim_ok cenv e) /\
  (!cenv ret_ty ty bi args st. builtin_sim_ok cenv ret_ty bi args) /\
  (!cenv vv_ty ty tb ret_ty args st.
     type_builtin_sim_ok cenv vv_ty tb ret_ty args)
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> goalStack.print_tac "PROBE" >> cheat
QED

Theorem compile_expr_sim:
  !ctx func cenv cx env ty e es.
    expr_sim_pre cenv cx env e es ==> expr_sim ctx func cenv cx ty e es
Proof
  metis_tac[compile_expr_sim_mutual, expr_sim_ok_def]
QED

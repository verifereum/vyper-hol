Theory exprSimAbiDecodeCounterexample
Ancestors
  exprSimAbiDecodePrefixExecution exprSimAbiDecodeRealizeCounted
  exprSimAbiDecodeRealizeEntry exprSimAbiDecodeRealizeTarget
  exprSimHypsDefs exprSimDefs exprLoweringProps compileEnv vyperAST
  exprSimAbiDecodeRealizeSource exprSimAbiDecodeRealizeFunction

Theorem abi_decode_counterexample_body_pre:
  expr_body_pre (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx k)
    abi_decode_realize_env (abi_decode_realize_expr k) abi_decode_realize_state
Proof
  `abi_decode_realize_ce (abi_decode_realize_entry_ce ce) =
    abi_decode_realize_entry_ce ce` by
    simp[abi_decode_realize_ce_def, abi_decode_realize_entry_ce_def] >>
  metis_tac[abi_decode_realize_live_body_pre]
QED

Theorem abi_decode_counterexample_sim_impossible:
  ~expr_vv_sim
    (abi_decode_realize_context (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_function (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx (2 ** 251 - 2))
    (expr_type (abi_decode_realize_expr (2 ** 251 - 2)))
    (abi_decode_realize_expr (2 ** 251 - 2)) abi_decode_realize_state
Proof
  rewrite_tac[expr_vv_sim_def] >> strip_tac >>
  strip_assume_tac (Q.INST [`ce` |-> `ce`, `k` |-> `2 ** 251 - 2`,
                           `entry` |-> `entry`] abi_decode_realize_entry_package) >>
  qpat_x_assum `!sa sb vv s0. _`
    (qspecl_then [`initial_compile_state entry`, `sb`, `vv`,
                 `abi_decode_realize_entry_state entry`] mp_tac) >>
  simp[abi_decode_realize_entry_stmt, abi_decode_realize_entry_state_def,
       venomStateTheory.init_venom_state_def,
       vyperCompilerTheory.initial_compile_state_def] >>
  strip_tac >> drule abi_decode_realize_outcome_needs_normal >>
  strip_tac >> gvs[] >>
  `sb = abi_decode_realize_final (abi_decode_realize_entry_ce ce)
     (2 ** 251 - 2) entry` by
    simp[abi_decode_realize_final_def] >>
  gvs[] >>
  mp_tac (SRULE[abi_decode_realize_entry_state_def,
                venomStateTheory.init_venom_state_def]
    (Q.INST [`ce` |-> `abi_decode_realize_entry_ce ce`,
             `ctx` |-> `abi_decode_realize_context (abi_decode_realize_entry_ce ce)
                         (2 ** 251 - 2) entry`]
      abi_decode_realize_overflow_no_normal)) >>
  metis_tac[]
QED

Theorem abi_decode_counterexample_case_impossible:
  ~expr_vv_case T
    (abi_decode_realize_context (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_function (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx (2 ** 251 - 2))
    (abi_decode_realize_expr (2 ** 251 - 2))
Proof
  rewrite_tac[expr_vv_case_def] >> strip_tac >>
  first_x_assum (qspecl_then [`abi_decode_realize_env`,
    `expr_type (abi_decode_realize_expr (2 ** 251 - 2))`,
    `abi_decode_realize_state`] mp_tac) >>
  simp[abi_decode_counterexample_body_pre, abi_decode_realize_no_calls,
       abi_decode_counterexample_sim_impossible]
QED

Theorem abi_decode_counterexample_instance:
  exprs_case T
    (abi_decode_realize_context (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_function (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx (2 ** 251 - 2))
    [abi_decode_realize_arg] /\
  ~expr_vv_case T
    (abi_decode_realize_context (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_function (abi_decode_realize_entry_ce ce) (2 ** 251 - 2) entry)
    (abi_decode_realize_entry_ce ce) (abi_decode_realize_live_cx (2 ** 251 - 2))
    (abi_decode_realize_expr (2 ** 251 - 2))
Proof
  simp[abi_decode_realize_child, abi_decode_counterexample_case_impossible]
QED

Theorem compile_abi_decode_case_false:
  ~(!nocalls ctx func cenv cx ann unwrap t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiDecode unwrap) t args))
Proof
  strip_tac >>
  strip_assume_tac abi_decode_counterexample_instance >>
  gvs[abi_decode_realize_expr_def] >> metis_tac[]
QED

(* Certification audit: report inherited oracle dependencies, not an admission. *)
val _ = print ("COUNTEREXAMPLE TAG: " ^
  String.concatWith "," (#1 (Tag.dest_tag (Thm.tag compile_abi_decode_case_false))) ^ "\n");

(* Bare top-level augmented words, including widths outside scalar targets. *)
Theory augAssignPlaceTopMemory
Ancestors
  bodyMemAugAssignTopWord bodyAugAssignOther bodyMemoryPreds
  exprSimProps exprSimSource supportedStmts vyperState

Theorem aug_place_toplevel_mem:
  (!s p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  body_inv tops ctx cenv cx /\
  supported_aug_target tops bindings (TopLevelNameTarget (src,id)) /\
  supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) ==>
    occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  call_evaluation_safe cx
    (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) es
Proof
  strip_tac >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  drule_all augassign_rhs_pre >> strip_tac >>
  drule_all augassign_toplevel_success >> strip_tac >>
  `body_expr_mem_ok cx e` by metis_tac[] >>
  drule_all augassign_toplevel_metadata >> strip_tac >>
  irule compile_augassign_toplevel_mem >> simp[] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `body_expr_mem_ok cx e`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
        `es with gas_obs := gs`] mp_tac) >>
      simp[expr_body_pre_gas_obs]) >>
  metis_tac[]
QED

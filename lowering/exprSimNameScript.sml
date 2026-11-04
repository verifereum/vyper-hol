(* Counted simulation for local names. *)
Theory exprSimName
Ancestors
  exprSimNameWord exprSimNameValue exprSimMemoryForce
  exprSimDefs exprSimHypsDefs loweringPosts
  exprLowering compileEnv vyperAST vyperTypeSystem vyperTypeInvariants
  vyperTypeEnv vyperTyping vyperState finite_map context

Theorem compile_name_other_sim:
  !ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Name ann id) es /\
    ~(is_word_type ann /\
      ?entry. lookup_scopes id es.scopes = SOME entry /\
              word_value entry.value) ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_of_vv_sim_memory >> conj_tac
  >~ [`expr_vv_sim`] >- metis_tac[compile_name_vv_sim, expr_vv_ok_def] >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  simp[compile_expr_def, compile_name_vv_def, comp_return_def,
       contextTheory.mk_ptr_def]
QED

Theorem compile_name_sim:
  !cenv ann id. expr_sim_ok cenv (Name ann id)
Proof
  rw[expr_sim_ok_def] >>
  Cases_on `is_word_type ann /\
            ?entry. lookup_scopes id es.scopes = SOME entry /\
                    word_value entry.value`
  >- (gvs[] >>
      `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
        gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
      irule compile_name_word_sim >> metis_tac[]) >>
  irule compile_name_other_sim >> metis_tac[]
QED

Theorem compile_name_case_sim:
  !cenv ann id. expr_ok cenv (Name ann id)
Proof
  simp[expr_ok_def, compile_name_sim, compile_name_vv_sim]
QED


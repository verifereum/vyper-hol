(* Nonword forcing discards the additional capacity guarantee of the room interface. *)
Theory bodyNonwordForceMemory
Ancestors
  bodyRhsRoomMemory exprSimMemDefs exprSimHyps exprSimDefs exprLowering
  compileEnv

Theorem body_nonword_expr_sim_mem_of_vv_sim_mem:
  expr_body_pre cenv cx env e es /\
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  ~is_word_type (expr_type e) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> rewrite_tac[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_expr cenv ty e sa` >>
  gvs[lower_value_def, comp_bind_def, comp_return_def, pairTheory.UNCURRY] >>
  irule gas_outcome_post_mono >>
  irule_at Any expr_sim_mem_room >> simp[] >>
  first_assum (irule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  rpt strip_tac >> gvs[]
QED

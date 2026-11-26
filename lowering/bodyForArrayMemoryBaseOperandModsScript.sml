(* The memory-array operand stays a data operand even at zero extent. *)
Theory bodyForArrayMemoryBaseOperandMods
Ancestors
  exprSimSubscriptArrayOrigin exprReasonOperand exprBodyPreProps exprSimHypsDefs
  loweringPosts exprLowering compileEnv context vyperTypeSystem vyperAST finite_map

Theorem for_array_memory_base_nonlabel_mods:
  expr_body_pre_mods mods c cx env e es /\ expr_type e = ArrayT sty bd /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
  !lbl. vv_operand vv <> Label lbl
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
          ?q sz. FLOOKUP c.ce_vars id = SOME (PtrVar (Var q) sz)` by
    fs[expr_sim_inv_mods_def] >>
  Cases_on `vv` >> gvs[vv_operand_def,vv_location_def]
  >- (rename1 `compile_expr c (ArrayT sty bd) e sa = (StackValue _ bop,sb)` >>
      `lower_value compile_expr c (ArrayT sty bd) e sa = (bop,sb)` by
        simp[lower_value_def,unwrap_value_def,comp_return_def,comp_bind_def] >>
      drule_all lower_compile_expr_not_label >> simp[]) >>
  irule compile_array_pointer_not_label >> simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_type _ = ArrayT _ _`)) >>
  qexists `env` >> simp[]
QED

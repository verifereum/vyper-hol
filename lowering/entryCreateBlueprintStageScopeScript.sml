(* Scoped blueprint simulation uses the target, constructor, keyword and
   preparation cursors in the compiler's evaluation order. *)
Theory entryCreateBlueprintStageScope
Ancestors
  entryCreateFocusSpec builtinCreate emitHelper emitHelperProps
  compileEnv abiEncoderProps context exprLoweringProps fragExec venomInst
  createSizeItinerary createSizeOperandPre exprSimFullBundleProps s1PrefixDefs
  exprSimSource exprBodyPreProps exprSimHypsDefs
  vyperAST vyperInterpreter gasExplicitSites bodyFullPreds vyperState
  exprLowering gasShadow list rich_list arithmetic

(* The successful fall-through and the failed assertion use the same
   four installed slots, including for a folded offset. *)
Theorem blueprint_check_layout:
  compile_create_blueprint_check lit target off a = (code,b) ==>
  b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  MAP (\i. i.inst_opcode) (emitted_insts a b) =
    (if lit then [EXTCODESIZE; SUB; SGT; ASSERT]
     else [EXTCODESIZE; GT; SUB; ASSERT]) /\
  EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a b)
Proof
  Cases_on `lit` >>
  simp[compile_create_blueprint_check_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> qpat_x_assum `_ = b` (SUBST_ALL_TAC o SYM) >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, frag_ids_def, is_terminator_def]
QED

(* DALLOCA and both copies are straight-line; the CREATE itself belongs to
   the following dispatch band, not to this preparation slice. *)
Theorem blueprint_append_layout:
  create_blueprint_append_itinerary target off code data len a app bufop total_op ==>
  (LAST app).cs_current_bb = a.cs_current_bb /\
  (LAST app).cs_current_insts = a.cs_current_insts ++ emitted_insts a (LAST app) /\
  MAP (\i. i.inst_opcode) (emitted_insts a (LAST app)) =
    (if len = Lit 0w then [ADD; DALLOCA; EXTCODECOPY]
     else [ADD; DALLOCA; EXTCODECOPY; ADD; MCOPY]) /\
  EVERY (\i. i.inst_id IN frag_ids a (LAST app) /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode)
    (emitted_insts a (LAST app))
Proof
  Cases_on `len = Lit 0w` >>
  simp[create_blueprint_append_itinerary_def, compile_alloc_dynamic_def,
       compile_copy_memory_dynamic_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  pure_rewrite_tac[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, frag_ids_def, is_terminator_def]
QED

(* The target consumes the same entry and ghosts as the outer call. The
   shadow endpoint here is the target cut, not the end of the call. *)
Theorem blueprint_scoped_target:
  args = target::rest /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_full_pre (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx ty
    (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) es
    (st0,sa,sb,hsa,hsb,op,s,G,tn) /\
  lower_value compile_expr ce (expr_type target) target sa = (addr,a) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type target) (gas_shadow_expr target)
    hsa = (addr,ha) /\
  expr_sim_full_code (ctx,hctx,func,hfunc) (sa,a,hsa,ha) /\
  (expr_body_pre ce cx env target es /\ body_const_cells_agree [(NONE,tops)] cx env es ==>
    expr_sim_scoped (DF,lo,d,ctx,hctx,PG,func,hfunc) ce cx (expr_type target) target es) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx hctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa a (bind (eval_expr cx target) (read_result cx)) (es,s,G,tn)
    (expr_sim_full_post (DF,lo,d,ctx,func) ce cx target (es,sa,a,s,addr,G,tn))
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `expr_body_pre ce cx env target es` by
    (irule create_call_operand_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     fs[expr_body_pre_def]) >>
  qpat_x_assum `_ ==> expr_sim_scoped _ _ _ _ _ _` (drule_all_then mp_tac) >>
  simp[expr_sim_scoped_def] >> disch_then irule >>
  `gas_admissible (bind (eval_expr cx target) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  qexistsl_tac [`hsa`,`ha`] >> fs[expr_sim_full_pre_def, expr_sim_full_code_def] >>
  rpt strip_tac >> res_tac
QED

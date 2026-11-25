(* A Len visit belongs either to the VV child or to its installed load. *)
Theory entryCreateBuiltinLenVisit
Ancestors
  entryCreateNativeFirstExit entryCreateAdminSequence entryCreateIntervalLayout
  entryCreateBodyCut entryCreateFocusSpec createSizeCutCode
  exprSimLen exprSimSource exprLoweringProps exprSimUnwrap exprSimHypsDefs exprLowering exprBopLowering
  exprSimFullBundleProps s1PrefixDefs gasShadowCompileStmtHelpers gasShadowState
  gasShadow gasExplicitSites builtinSimple context compileEnv emitHelper fragExec
  vyperStorageTrace vyperInterpreter vyperState vyperAST venomInst list

Theorem len_load_cut_code[local]:
  compile_builtin_len ctor imm x loc sm = (op,sb) ==>
  create_cut_code {} sm sb
Proof
  `create_cut_code {} sm (SND (compile_builtin_len ctor imm x loc sm))` by
    (Cases_on `loc` >>
     simp[compile_builtin_len_def, compile_ptr_load_def, create_cut_code_emit_op,
          create_cut_targets_def, compile_imm_load_word_def] >>
     Cases_on `ctor` >> Cases_on `imm` >>
     simp[create_cut_code_emit_op, create_cut_targets_def] >>
     irule create_cut_code_bind >> simp[create_cut_code_emit_op, create_cut_targets_def]) >>
  strip_tac >> gvs[]
QED

Theorem len_split_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} sa sm /\ fn_has_code sa sm f /\
  create_cut_code {} sm sb /\ fn_has_code sm sb f /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts sm sb) /\
  create_operand_cut sa sm E ctx f tops cx st0 (eval_expr cx e) (es,s) ==>
  create_operand_cut sa sb E ctx f tops cx st0
    (bind (eval_expr cx (Builtin ann Len [e])) (read_result cx)) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (simp[len_source, bind_assoc, read_result_def, bind_return] >>
      irule create_cut_bind_left >>
      simp[storage_trace_frame_bind_all, storage_trace_frame_array_length,
           storage_trace_frame_return] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  (* No replay is needed on the right: the suffix cut holds for every
     source, so test it against the very result and horizon of this query. *)
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut sm sb E ctx f tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >> simp[]) >>
  qpat_x_assum `create_operand_cut sm sb _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED

Theorem len_value_cut_from_layout:
  (!ctor imm x loc m b out.
    compile_builtin_len ctor imm x loc m = (out,b) ==>
    b.cs_current_bb = m.cs_current_bb /\
    b.cs_current_insts = m.cs_current_insts ++ emitted_insts m b /\
    EVERY (\i. i.inst_id IN frag_ids m b /\ ~is_terminator i.inst_opcode /\
               i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (emitted_insts m b)) /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Builtin ann Len args) es /\
  create_layout sa sb /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (Builtin ann Len args)
    es (st0,sa,sb,sha,shb,op,s,G,tn) /\
  (!vv sm shm.
    builtin_args_length_ok Len (LENGTH args) /\
    expr_body_pre ce cx env (HD args) es /\ create_layout sa sm /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty (HD args)
      es (st0,sa,sm,sha,shm,vv,s,G,tn) ==>
    create_cut_code {} sa sm /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx (HD args)) (es,s)) ==>
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (bind (eval_expr cx (Builtin ann Len args)) (read_result cx)) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule len_pre_args >> strip_tac >> gvs[] >>
  `expr_body_pre ce cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >> fs[expr_body_pre_def]) >>
  fs[expr_sim_full_pre_def] >>
  Cases_on `compile_expr ce ty e sa` >>
  rename1 `compile_expr ce ty e sa = (vv,sm)` >>
  Cases_on `compile_builtin_len ce.ce_is_ctor ce.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of SOME l => l | NONE => LocMemory) sm` >>
  gvs[lower_value_def, compile_expr_len, comp_bind_def, as_stack_val_pair,
      unwrap_value_def, comp_return_def] >>
  `gas_shadow_compiles (compile_expr ce ty e)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  rename1 `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (svv,shm)` >>
  `svv = vv /\ gas_shadow_state sm shm` by
    (qpat_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[] >> metis_tac[]) >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def, compile_expr_len] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  rename1 `compile_expr ce ty e sa = (arg,sm)` >>
  qmatch_goalsub_rename_tac `create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx f` >>
  `cs_extends sa sm /\ cs_extends sha shm` by metis_tac[compile_expr_extends] >>
  `cs_extends sm sb /\ cs_extends shm shb` by metis_tac[len_load_extends] >>
  `fn_has_code sa sm f /\ fn_has_code sm sb f /\ fn_has_code sha shm shf` by
    metis_tac[fn_has_code_split] >>
  `create_layout sa sm` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,shf) ce cx ty e es
    (st0,sa,sm,sha,shm,arg,s,G,tn)` by
    (simp[expr_vv_sim_full_pre_def] >> metis_tac[len_operand_admissible]) >>
  qpat_x_assum `!vv sm shm. _` (qspecl_then [`arg`,`sm`,`shm`] mp_tac) >>
  simp[vyperContextTheory.builtin_args_length_ok_def] >> strip_tac >>
  `create_cut_code {} sm sb` by metis_tac[len_load_cut_code] >>
  irule len_split_cut >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `sm` >> simp[] >>
  qpat_assum `!ctor imm x loc m b out. _` (drule_then strip_assume_tac) >>
  fs[EVERY_MEM]
QED

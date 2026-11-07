Theory bodyPtrStructLitOwnershipDeploy
Ancestors
  bodyPtrStructLitOwnershipConstructorEntry bodyPtrStructLitOwnershipConstructorTail
  bodyPtrStructLitOwnershipFunctionLists bodyPtrStructLitOwnershipRuntime
  bodyPtrStructLitOwnershipBodyRun bodyPtrStructLitOwnershipFrame
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipGuarded
  bodyPtrStructLitLoopShapeDynBody loweringShapeProps loweringShapeDefs
  moduleLowering compileEnv context

Theorem alloc_run_compile_stmts_shape_frame:
  !ce lc ty stmts R.
  ce.ce_alloca_locals /\ loop_ctx_shape_ok lc /\
  ~supported_stmts_expr_exists expr_shape_root stmts /\ shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_stmts ce lc ty stmts)
    (\u s. shape_state s /\ R s /\ fresh_outputs s)
Proof
  rpt strip_tac >> irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
  irule_at Any (cj 2 compile_stmt_shape) >>
  qexistsl [`R`, `\u s. shape_state s /\ fresh_outputs s`] >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_stmts_shape_fresh >> simp[]
QED

Theorem alloc_run_constructor_body_tail:
  !ce stmts imm lbl nr key tr rt ilen ints.
  ce.ce_alloca_locals /\ ~supported_stmts_expr_exists expr_shape_root stmts /\
  jump_label_ok lbl /\
  EVERY (\(l,env,params,rb,n,k,t,view,ctor,sz,b,r).
    internal_fn_shape_ok (l,env,params,rb,n,k,t,view,ctor,sz,b,r) /\ internal_label_ok l) ints ==>
  alloc_run (\s. shape_state s /\ plain_operand s imm /\ cenv_shape_ok s ce)
    (do compile_stmts ce NoLoop NoneT stmts;
        cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key tr F else return ());
        compile_constructor_epilogue rt ilen imm;
        compile_internal_fn_bodies ints od)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ plain_operand s imm` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_stmts_shape_frame >>
      qexists `\s. plain_operand s imm` >> simp[loop_ctx_shape_ok_def, shape_stable_def] >>
      metis_tac[plain_operand_mono]) >>
  gen_tac >> simp[] >>
  qsuff_tac `alloc_run (\s. shape_state s /\ plain_operand s imm)
    (do (do cs <- comp_get;
            (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
            new_block lbl;
            (if nr then compile_nonreentrant_unlock key tr F else return ());
            compile_constructor_epilogue rt ilen imm od);
        compile_internal_fn_bodies ints od)
    (\u s. shape_state s /\ fresh_outputs s)`
  >- simp[comp_ignore_bind_def, comp_bind_assoc] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ fresh_outputs s` >> conj_tac
  >- (gen_tac >> simp[SF ETA_ss] >> irule alloc_run_conseq >>
      irule_at Any alloc_run_compile_internal_fn_bodies >> simp[]) >>
  simp[GSYM comp_ignore_bind_def, alloc_run_constructor_tail_shape_fresh]
QED

Theorem alloc_run_generate_deploy:
  !has_ctor rt ilen args data_size ints ce stmts pay nr key tr.
  (has_ctor ==> cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals /\
    ~supported_stmts_expr_exists expr_shape_root stmts /\
    EVERY (\(lbl,env,params,rb,n,k,t,view,ctor,sz,b,r).
      internal_fn_shape_ok (lbl,env,params,rb,n,k,t,view,ctor,sz,b,r) /\ internal_label_ok lbl) ints) ==>
  alloc_run shape_state (compile_generate_deploy has_ctor rt ilen args data_size ints ce stmts pay nr key tr)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt gen_tac >> Cases_on `has_ctor` >> simp[]
  >- (strip_tac >>
      qsuff_tac `alloc_run shape_state
        (do (if ~pay then do cv <- emit_op CALLVALUE []; no_val <- emit_op ISZERO [cv];
                            emit_void ASSERT [no_val] od else return ());
            entry <- (do imm <- (if ilen > 0 then
                         do r <- compile_fixed_region_with_id ilen; return (SND r).buf_operand od
                       else return (Lit 0w));
                         ce' <- compile_register_constructor_args
                           (ce with ce_imm_alloca := (if ilen > 0 then SOME imm else NONE)) args 0 data_size;
                         (if nr then compile_nonreentrant_lock key tr F else return ());
                         lbl <- fresh_label "ctor_exit"; return (imm,ce',lbl) od);
            (\(imm,ce',lbl).
              do compile_stmts (ce' with ce_ctor_exit_label := SOME lbl) NoLoop NoneT stmts;
                 cs <- comp_get;
                 (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
                 new_block lbl;
                 (if nr then compile_nonreentrant_unlock key tr F else return ());
                 compile_constructor_epilogue rt ilen imm;
                 compile_internal_fn_bodies ints od) entry od)
        (\u s. shape_state s /\ fresh_outputs s)`
      >- simp[compile_generate_deploy_def, comp_ignore_bind_def, comp_bind_assoc,
              loop_comp_return_bind] >>
      simp[comp_ignore_bind_def] >> irule alloc_run_bind >> qexists `\u s. shape_state s` >> reverse conj_tac
      >- (once_rewrite_tac[GSYM payable_check_eq] >>
          irule alloc_run_conseq >> irule_at Any alloc_run_payable_check_frame >>
          qexists `\s. T` >> simp[shape_stable_def]) >>
      gen_tac >> simp[] >> irule alloc_run_bind >>
      qexists `\(imm,ce',lbl) s. shape_state s /\ plain_operand s imm /\ jump_label_ok lbl /\
        cenv_shape_ok s (ce' with ce_ctor_exit_label := SOME lbl) /\ ce'.ce_alloca_locals` >>
      reverse conj_tac >- (simp[GSYM comp_ignore_bind_def, SF ETA_ss] >> irule alloc_run_constructor_entry >> simp[]) >>
      gen_tac >> PairCases_on `v` >> simp[] >>
      irule alloc_run_conseq >> irule_at Any alloc_run_pure_pre >>
      qexistsl [`jump_label_ok v2 /\ v1.ce_alloca_locals`,
        `\u s. shape_state s /\ fresh_outputs s`,
        `\s. shape_state s /\ plain_operand s v0 /\
          cenv_shape_ok s (v1 with ce_ctor_exit_label := SOME v2)`] >> simp[] >>
      strip_tac >> irule (SRULE [comp_ignore_bind_def] alloc_run_constructor_body_tail) >> simp[]) >>
  simp[compile_generate_deploy_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ fresh_outputs s` >> reverse conj_tac
  >- simp[alloc_run_simple_deploy_shape_fresh] >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theory bodyPtrStructLitOwnershipInternalFunction
Ancestors
  bodyPtrStructLitOwnershipEntryPc bodyPtrStructLitOwnershipGuarded
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipBodyRun
  bodyPtrStructLitOwnershipLock bodyPtrStructLitOwnershipStmtHelpers
  bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness loweringShapeProps loweringShapeDefs
  bodyPtrStructLitLoopShapeDynBody supportedStmtTraverse moduleLowering compileEnv context

Theorem alloc_run_internal_exit:
  alloc_run fresh_outputs
    (do cs <- comp_get;
        (if block_is_terminated cs then return ()
         else do (if nr then compile_nonreentrant_unlock key tr view else return ());
                 (case rt of NONE => emit_inst RET [pc] []
                           | SOME _ => emit_inst INVALID [] []) od);
        return () od)
    (\u s. fresh_outputs s)
Proof
  simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[alloc_run_def, comp_get_def, alloc_frame_refl] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> conj_tac
  >- (gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  Cases_on `block_is_terminated v`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[] >> irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  reverse conj_tac
  >- (Cases_on `nr` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_nonreentrant_unlock] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> Cases_on `rt` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_internal_temporary_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s)
    (case rt of SOME ty =>
       if (ret_count:num) > 0 then do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()
     | NONE => return ())
    (\u s. shape_state s /\ R s)
Proof
  strip_tac >> Cases_on `rt`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[] >> IF_CASES_TAC
  >- (simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
      irule_at Any alloc_run_alloc_buffer_frame >> simp[] >>
      gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_internal_body_suffix:
  !ce alloc_ce ret_count nr key tr view body rt pc.
  ce.ce_alloca_locals /\ ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (do (case rt of SOME ty =>
           if ret_count > 0 then do compile_alloc_buffer (type_memory_bytes alloc_ce ty); return () od
           else return ()
         | NONE => return ());
        (if nr then compile_nonreentrant_lock key tr view else return ());
        compile_stmts ce NoLoop (case rt of SOME t => t | NONE => BaseT BoolT) body;
        cs <- comp_get;
        (if block_is_terminated cs then return ()
         else do (if nr then compile_nonreentrant_unlock key tr view else return ());
                 (case rt of NONE => emit_inst RET [pc] []
                           | SOME _ => emit_inst INVALID [] []) od);
        return () od)
    (\u s. fresh_outputs s)
Proof
  rpt strip_tac >> simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- simp[GSYM comp_ignore_bind_def, alloc_run_internal_temporary_frame,
          cenv_shape_ok_stable] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (Cases_on `nr`
      >- (simp[] >> irule alloc_run_conseq >>
          irule_at Any alloc_run_nonreentrant_lock_frame >>
          qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_compile_stmts_shape_fresh >> simp[loop_ctx_shape_ok_def]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_internal_exit) >> simp[]
QED

Theorem alloc_run_compile_internal_function:
  !ce params has_ret_buf nr key tr view is_ctor imm_len body rt.
  cenv_static_ok ce /\ ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ internal_label_ok s.cs_current_bb)
    (compile_internal_function ce params has_ret_buf nr key tr view is_ctor imm_len body rt)
    (\u s. fresh_outputs s)
Proof
  rpt gen_tac >> strip_tac >> rename1 `compile_internal_function ce params has_ret_buf nr key tr view is_ctor imm_len stmts rt` >>
  qsuff_tac `alloc_run (\s. shape_state s /\ internal_label_ok s.cs_current_bb)
    (do entry <-
      (do entry <-
        (do rb <- (if has_ret_buf then do op <- emit_op PARAM [Lit 0w]; return (SOME op) od else return NONE);
            r <- compile_internal_param_decls params (if has_ret_buf then 1 else 0);
            pc <- emit_op RETPC_PARAM [Lit (n2w (SND r))]; return (rb,FST r,pc) od);
        (\(rb,captured,pc).
          do imm <- (if is_ctor /\ imm_len > 0 then
                do r <- compile_fixed_region_with_id imm_len; return (SOME (SND r).buf_operand) od
              else return NONE);
             ce' <- materialize_internal_params
               (ce with <|ce_return_buf := (case (rb,ce.ce_return_buf) of
                  (SOME op,SOME (MemLoc off sz)) => SOME (PtrVar op sz) | _ => ce.ce_return_buf);
                 ce_return_pc := SOME (PtrVar pc 0)|>) captured;
             return (ce',imm,pc) od) entry od);
      (\(ce',imm,pc).
        do (case rt of SOME ty => if ce.ce_returns_count > 0 then
              do compile_alloc_buffer (type_memory_bytes ce ty); return () od else return () | NONE => return ());
           (if nr then compile_nonreentrant_lock key tr view else return ());
           compile_stmts (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) NoLoop
             (case rt of SOME t => t | NONE => BaseT BoolT) stmts;
           cs <- comp_get;
           (if block_is_terminated cs then return () else
             do (if nr then compile_nonreentrant_unlock key tr view else return ());
                (case rt of NONE => emit_inst RET [pc] [] | SOME _ => emit_inst INVALID [] []) od);
           return () od) entry od) (\u s. fresh_outputs s)`
  >- (simp[compile_internal_function_def, comp_ignore_bind_def, comp_bind_assoc,
           loop_comp_return_bind]) >>
  irule alloc_run_bind >>
  qexists `\(ce',imm,pc) s. shape_state s /\
    cenv_shape_ok s (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_internal_entry_prefix_pc_frame >>
      qexists `\s. T` >> simp[shape_stable_def, pairTheory.FORALL_PROD]) >>
  gen_tac >> PairCases_on `v` >> simp[comp_ignore_bind_def] >>
  irule (SRULE [comp_ignore_bind_def] alloc_run_internal_body_suffix) >> simp[]
QED

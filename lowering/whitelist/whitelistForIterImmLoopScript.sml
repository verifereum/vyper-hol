(* Compiler cuts for immutable-source counted iteration.  Source preparation
   uses LocCode; the memory-only array loop contracts cannot certify it. *)
Theory whitelistForIterImmLoop
Ancestors
  whitelistForIterImmCopy whitelistForIterImmFrame whitelistForIterDynLoop
  exprSimTopLevelImmutable stmtLowering exprLoweringProps compileEnv context
  vyperAST list finite_map
Libs
  monadsyntax

Theorem compile_for_immutable_stages:
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  compile_stmt cenv lctx ty
    (For id et (Array (TopLevelName (ArrayT et bd) (src,name))) n stmts) st =
    ((),st') ==>
  ?lvo st1 bc entry cond bod incr exit idx offo toto epo sa sb0 sb1 sj.
    (if (case bd of Dynamic _ => T | Fixed _ => F) then
       compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
     else return (Lit (n2w (bound_length bd)))) st = (lvo,st1) /\
    (do bc <- declare_local cenv id et;
        emit_local_alloca bc id;
        entry <- fresh_label "iter_entry";
        cond <- fresh_label "iter_cond";
        bod <- fresh_label "iter_body";
        incr <- fresh_label "iter_incr";
        exit <- fresh_label "iter_exit";
        emit_inst JMP [Label entry] [];
        new_block entry;
        idx <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx];
        (if (case bd of Dynamic _ => T | Fixed _ => F) then
           do invalid <- emit_op GT [lvo; Lit (n2w (bound_length bd))];
              valid <- emit_op ISZERO [invalid];
              emit_void ASSERT [valid]
           od
         else return ());
        emit_inst JMP [Label cond] [];
        new_block cond;
        done <- emit_op EQ [Var idx; lvo];
        emit_inst JNZ [done; Label exit; Label bod] [];
        new_block bod;
        offv <- emit_op MUL [Var idx;
                   Lit (n2w (elem_size_in_location cenv LocCode et))];
        tot <- (if (case bd of Dynamic _ => T | Fixed _ => F) then
                  emit_op ADD [Lit 32w; offv]
                else return offv);
        ep <- emit_op ADD [Lit (n2w off); tot];
        return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
     od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
    (case FLOOKUP bc.ce_vars id of
       SOME (MemLoc dst _) =>
         compile_iter_elem_copy cenv epo (Lit (n2w dst))
           (elem_size_in_location cenv LocCode et) LocCode F et et
     | SOME (PtrVar ptr_op _) =>
         compile_iter_elem_copy cenv epo ptr_op
           (elem_size_in_location cenv LocCode et) LocCode F et et
     | _ => emit_void INVALID []) sa = ((),sb0) /\
    compile_stmts bc (InLoop exit incr) ty stmts sb0 = ((),sb1) /\
    emit_jmp_if_not_terminated incr sb1 = ((),sj) /\
    (do new_block incr;
        next <- emit_op ADD [Var idx; Lit 1w];
        emit_inst ASSIGN [next] [idx];
        emit_inst JMP [Label cond] [];
        new_block exit;
        return ()
     od) sj = ((),st')
Proof
  strip_tac >> drule compile_toplevel_immutable_ptr >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  Cases_on `bd` >>
  simp[Once compile_stmt_def, expr_type_def, LET_THM, vv_location_def,
       vv_operand_def, mk_ptr_def, is_slot_addressed_def,
       compile_ptr_load_def, word_scale_def, bound_length_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]
QED

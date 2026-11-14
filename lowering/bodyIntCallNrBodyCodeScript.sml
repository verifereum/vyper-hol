(* Compiler intervals for guarded internal functions, independent of the guard flag. *)
Theory bodyIntCallNrBodyCode
Ancestors
  bodyIntCallActualEntryFields bodyIntCallPackageBodyCode externalEntryShape
  intCallCallee stmtSimProps moduleLowering compileEnv fragExec loweringPosts
  venomInst emitHelper bodyExprPreFacts

Theorem internal_function_guarded_body_states:
  compile_internal_function ce params has_rb nr key trans view ctor ilen ss rt
    entry = ((),final) ==>
  ?ce2 rpc imm prelock body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,rpc,imm),prelock) /\
    (if nr then compile_nonreentrant_lock key trans view prelock
     else ((),prelock)) = ((),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else (comp_bind
       (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
       (\u. case rt of NONE => emit_inst RET [rpc] []
                      | SOME ty => emit_inst INVALID [] [])) body_end) = ((),final)
Proof
  rewrite_tac[compile_internal_function_entry_factorization] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, comp_get_def,
       compile_stmts_env] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_internal_function_entry _ _ _ _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `stmts_env root NoLoop ty ss start` >>
  Cases_on `stmts_env root NoLoop ty ss start` >>
  rename1 `_ = (body_env,body_end)` >>
  qexistsl [`start`, `body_env`, `body_end`] >>
  Cases_on `nr` >> gvs[comp_return_def] >>
  Cases_on `block_is_terminated body_end` >> gvs[comp_return_def, comp_bind_def]
QED

Theorem internal_function_guarded_suffix:
  (if block_is_terminated sb then ((),sb)
   else (comp_bind
     (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
     (\u. case rt of NONE => emit_inst RET [rpc] []
                    | SOME ty => emit_inst INVALID [] [])) sb) = ((),sf) ==>
  cs_extends sb sf /\
  (~block_is_terminated sb ==>
    ?su. (if nr then compile_nonreentrant_unlock key trans view sb
          else ((),sb)) = ((),su) /\
      (case rt of NONE => emit_inst RET [rpc] [] su
                | SOME ty => emit_inst INVALID [] [] su) = ((),sf))
Proof
  Cases_on `block_is_terminated sb` >> simp[]
  >- (strip_tac >> gvs[cs_extends_refl]) >>
  Cases_on `nr` >> Cases_on `view` >> Cases_on `trans` >> Cases_on `rt` >>
  simp[contextTheory.compile_nonreentrant_unlock_def,
    comp_bind_def, comp_return_def, emit_void_def, emit_inst_def,
    fresh_id_def, emit_def] >>
  disch_then (SUBST1_TAC o SYM) >> simp[] >>
  irule cs_extends_same_block >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem internal_function_guarded_body_code:
  compile_internal_function ce params has_rb nr key trans view ctor ilen ss rt
    entry = ((),final) /\ fn_has_code entry final func ==>
  ?ce2 rpc imm prelock body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,rpc,imm),prelock) /\
    (if nr then compile_nonreentrant_lock key trans view prelock
     else ((),prelock)) = ((),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    cs_extends entry prelock /\ cs_extends prelock body_start /\
    cs_extends body_start body_end /\ cs_extends body_end final /\
    fn_has_code entry prelock func /\ fn_has_code prelock body_start func /\
    fn_has_code body_start body_end func /\ fn_has_code body_end final func /\
    (~block_is_terminated body_end ==>
      ?su. (if nr then compile_nonreentrant_unlock key trans view body_end
            else ((),body_end)) = ((),su) /\
        (case rt of NONE => emit_inst RET [rpc] [] su
                  | SOME ty => emit_inst INVALID [] [] su) = ((),final))
Proof
  strip_tac >> drule internal_function_guarded_body_states >> strip_tac >>
  drule internal_function_guarded_suffix >> strip_tac >>
  `cs_extends entry prelock` by
    (drule compile_internal_entry_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends prelock body_start` by
    (Cases_on `nr` >> gvs[cs_extends_refl] >>
     mp_tac compile_nonreentrant_lock_labels >>
     disch_then (qspecl_then [`key`, `trans`, `view`, `prelock`] mp_tac) >> simp[]) >>
  `cs_extends body_start body_end` by
    (drule (SRULE[cs_mono_def] stmts_env_cs_mono) >> simp[]) >>
  `cs_extends body_start final /\ cs_extends prelock final` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code prelock body_start func /\ fn_has_code body_start final func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  `fn_has_code body_start body_end func /\ fn_has_code body_end final func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >> simp[]
QED

(* Restrict selected callee code to its actual entry, body, and epilogue. *)
Theory bodyIntCallPackageBodyCode
Ancestors
  bodyIntCallBodyTrace bodyIntCallActualEntryFields bodyExprPreFacts
  stmtSimProps moduleLowering compileEnv fragExec loweringPosts venomInst

Theorem internal_function_body_code:
  compile_internal_function ce params has_rb F nkey trans view ctor ilen
    ss rt entry = ((),final) /\ fn_has_code entry final func ==>
  ?ce2 pc imm body_start body_env body_end.
    compile_internal_function_entry ce params has_rb ctor ilen rt entry =
      ((ce2,pc,imm),body_start) /\
    stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
      NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case rt of NONE => emit_inst RET [pc] [] body_end
                   | SOME ty => emit_inst INVALID [] [] body_end) = ((),final) /\
    cs_extends entry body_start /\ cs_extends body_start body_end /\
    cs_extends body_end final /\
    fn_has_code entry body_start func /\
    fn_has_code body_start body_end func /\ fn_has_code body_end final func
Proof
  strip_tac >> drule compile_internal_function_entry_body_states >> strip_tac >>
  `cs_extends entry body_start` by
    (drule compile_internal_entry_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends body_start body_end` by
    (drule (SRULE[cs_mono_def] stmts_env_cs_mono) >> simp[]) >>
  `cs_extends body_end final` by
    (Cases_on `block_is_terminated body_end` >> gvs[]
     >- simp[cs_extends_refl] >>
     Cases_on `rt` >> gvs[] >> drule cs_extends_emit_inst >> simp[]) >>
  `cs_extends body_start final` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code body_start body_end func /\ fn_has_code body_end final func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_internal_function_entry _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `stmts_env _ _ _ _ _ = _`)) >> simp[]
QED

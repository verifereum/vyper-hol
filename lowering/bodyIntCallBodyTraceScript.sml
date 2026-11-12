(* Compiler boundaries of the internal body, in both deployment modes. *)
Theory bodyIntCallBodyTrace
Ancestors
  intCallCallee stmtSimProps moduleLowering vyperCompiler compileEnv venomInst

Theorem compile_internal_function_entry_body_states:
  compile_internal_function cenv params has_buf F nkey use_trans is_view
    is_ctor imm_len ss ret entry = ((),final) ==>
  ?cenv2 pc imm body_start body_env body_end.
    compile_internal_function_entry cenv params has_buf is_ctor imm_len ret
      entry = ((cenv2,pc,imm),body_start) /\
    stmts_env
      (cenv2 with <| ce_imm_alloca := imm; ce_alloca_locals := T |>) NoLoop
      (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case ret of
       NONE => emit_inst RET [pc] [] body_end
     | SOME t => emit_inst INVALID [] [] body_end) = ((),final)
Proof
  rewrite_tac[compile_internal_function_entry_factorization] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def, comp_get_def,
       compile_stmts_env] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_internal_function_entry _ _ _ _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  qmatch_goalsub_abbrev_tac `stmts_env ce NoLoop ty ss start` >>
  Cases_on `stmts_env ce NoLoop ty ss start` >>
  rename1 `_ = (body_env,body_end)` >> gvs[] >>
  Cases_on `block_is_terminated body_end` >> gvs[] >>
  Cases_on `ret` >> gvs[comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[]
QED

Theorem compile_internal_function_body_states:
  ~(is_ctor /\ imm_len > 0) /\
  compile_internal_function cenv params has_buf F nkey use_trans is_view
    is_ctor imm_len ss ret entry = ((),final) ==>
  ?cenv2 pc body_start body_env body_end.
    compile_internal_prologue cenv params has_buf ret entry =
      ((cenv2,pc),body_start) /\
    stmts_env
      (cenv2 with <| ce_imm_alloca := NONE; ce_alloca_locals := T |>) NoLoop
      (case ret of SOME t => t | NONE => BaseT BoolT) ss body_start =
      (body_env,body_end) /\
    (if block_is_terminated body_end then ((),body_end)
     else case ret of
       NONE => emit_inst RET [pc] [] body_end
     | SOME t => emit_inst INVALID [] [] body_end) = ((),final)
Proof
  strip_tac >> drule compile_internal_function_entry_body_states >>
  strip_tac >>
  drule compile_internal_function_entry_no_reservation >>
  disch_then (fn th => gvs[th, comp_bind_def, comp_return_def]) >>
  pairarg_tac >> gvs[] >> PairCases_on `pr` >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The immutable reservation is between the physical prefix and parameter
   materialization; do not replace this stage with the runtime prologue. *)
Theorem compile_internal_function_entry_ctor_stages:
  0 < imm_len /\
  compile_internal_function_entry cenv params has_buf T imm_len ret entry =
    ((cenv2,pc,imm),body_start) ==>
  ?prefix captured prefix_end ar reserved materialized.
    compile_internal_entry_prefix cenv params has_buf entry =
      ((prefix,captured,pc),prefix_end) /\
    compile_fixed_region_with_id imm_len prefix_end = (ar,reserved) /\
    imm = SOME (SND ar).buf_operand /\
    materialize_internal_params prefix captured reserved = (cenv2,materialized) /\
    (case ret of
       SOME ty => if cenv.ce_returns_count > 0 then
                    (do compile_alloc_buffer (type_memory_bytes cenv ty);
                        return () od) materialized
                  else ((),materialized)
     | NONE => ((),materialized)) = ((),body_start)
Proof
  simp[compile_internal_function_entry_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_internal_entry_prefix _ _ _ _ = (prefix,_)` >>
  PairCases_on `prefix` >> gvs[] >>
  Cases_on `ret` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `cenv.ce_returns_count > 0` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

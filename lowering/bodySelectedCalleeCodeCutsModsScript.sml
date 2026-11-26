(* Compiler cuts for the real and shadow packages of the selected callee. *)
Theory bodySelectedCalleeCodeCutsMods
Ancestors
  bodyFullIntCallEntryShadow entryInternalAppend entryCompileIntervals
  externalEntryShape bodyExprPreFacts gasShadowStmtEnv gasShadowCompileStmtOps
  intCallCallee fragExec exprLoweringProps gasShadowCompileBase pair
  compileEnv abiDecoderAppend arithmetic stmtSimProps gasShadowModuleOps
  gasShadowState gasShadowCompileStmtBase compileVyper moduleLowering emitHelper
  exprLowering vyperAST venomInst

Theorem capture_appends[local]:
  cs_appends (compile_internal_entry_prefix ce params has_rb)
Proof
  `!idx. cs_appends (compile_internal_param_decls params idx)` by
    (simp[cs_appends_def] >> rpt strip_tac >>
     rename1 `compile_internal_param_decls params idx st = (pr,st')` >>
     PairCases_on `pr` >> drule_then strip_assume_tac internal_param_decls_projection >>
     simp[cs_extends_def]) >>
  simp[compile_internal_entry_prefix_def] >>
  irule cs_appends_bind >> conj_tac
  >- simp[cs_appends_bind, cs_appends_emit_helpers, cs_appends_return] >>
  Cases_on `has_rb` >> simp[cs_appends_bind, cs_appends_return, cs_appends_emit_helpers]
QED

Theorem reserve_appends[local]:
  cs_appends
    (if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE)
Proof
  IF_CASES_TAC >> simp[cs_appends_return] >>
  irule cs_appends_bind >> simp[cs_appends_return] >>
  rw[cs_appends_def] >>
  qspec_then `ilen` (qspec_then `st` mp_tac) compile_fixed_region_with_id_labels >>
  simp[]
QED

Theorem scratch_appends[local]:
  cs_appends
    (case rt of NONE => comp_return ()
     | SOME ty => if 0 < ce.ce_returns_count then
         comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
           (comp_return ())
       else comp_return ())
Proof
  Cases_on `rt` >> simp[cs_appends_return] >>
  IF_CASES_TAC >> simp[cs_appends_abi_alloc_buffer, cs_appends_return,
                       cs_appends_ignore_bind]
QED

Theorem selected_entry_phases[local]:
  compile_internal_function_entry ce params has_rb ctor ilen rt entry =
    ((ce2,pc,imm),prologue) ==>
  ?ce1 caps capture reserved materialized.
    compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
    (if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE) capture = (imm,reserved) /\
    materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
    (case rt of NONE => comp_return ()
     | SOME ty => if 0 < ce.ce_returns_count then
         comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
           (comp_return ())
       else comp_return ()) materialized = ((),prologue) /\
    cs_extends entry capture /\ cs_extends capture reserved /\
    cs_extends reserved materialized /\ cs_extends materialized prologue
Proof
  Cases_on `compile_internal_entry_prefix ce params has_rb entry` >>
  rename1 `_ = (prefix,capture)` >> PairCases_on `prefix` >>
  qabbrev_tac `reserve = if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE` >>
  qabbrev_tac `scratch = case rt of NONE => comp_return ()
      | SOME ty => if 0 < ce.ce_returns_count then
           comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce ty))
             (comp_return ())
         else comp_return ()` >>
  Cases_on `reserve capture` >> rename1 `reserve capture = (im,reserved)` >>
  Cases_on `materialize_internal_params prefix0 prefix1 reserved` >>
  rename1 `materialize_internal_params _ _ _ = (cm,materialized)` >>
  Cases_on `scratch materialized` >> rename1 `scratch materialized = (u,last)` >>
  Cases_on `u` >>
  `cs_extends entry capture` by
    (drule (SRULE [cs_appends_def] capture_appends) >> simp[]) >>
  `cs_extends capture reserved` by
    (qunabbrev_tac `reserve` >> drule (SRULE [cs_appends_def] reserve_appends) >> simp[]) >>
  `cs_extends reserved materialized` by
    (qspecl_then [`prefix1`, `prefix0`, `reserved`] mp_tac
       materialize_internal_params_labels >> simp[]) >>
  `cs_extends materialized last` by
    (qunabbrev_tac `scratch` >> drule (SRULE [cs_appends_def] scratch_appends) >> simp[]) >>
  strip_tac >>
  gvs[compile_internal_function_entry_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  unabbrev_all_tac >> gvs[GREATER_DEF, comp_ignore_bind_def]
QED

Theorem lock_appends[local]:
  cs_appends (if nr then compile_nonreentrant_lock key trans view else comp_return ())
Proof
  Cases_on `nr` >> simp[cs_appends_nonreentrant, cs_appends_return]
QED

Theorem suffix_appends[local]:
  cs_appends (comp_ignore_bind
    (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
    (case rt of NONE => emit_inst RET [pc] [] | SOME _ => emit_inst INVALID [] []))
Proof
  irule cs_appends_ignore_bind >> conj_tac
  >- (Cases_on `nr` >> simp[cs_appends_nonreentrant, cs_appends_return]) >>
  Cases_on `rt` >> simp[cs_appends_emit_helpers]
QED

Theorem selected_body_intervals[local]:
  compile_internal_function ce params has_rb nr key trans view ctor ilen ss rt entry = ((),final) /\
  compile_internal_function_entry ce params has_rb ctor ilen rt entry = ((ce2,pc,imm),prologue) /\
  (if nr then compile_nonreentrant_lock key trans view else comp_return ()) prologue = ((),a) /\
  stmts_env (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
    NoLoop (case rt of SOME ty => ty | NONE => BaseT BoolT) ss a = (out,z) /\
  fn_has_code entry final fn ==>
  cs_extends entry prologue /\ cs_extends prologue a /\ cs_extends a z /\ cs_extends z final /\
  fn_has_code entry prologue fn /\ fn_has_code prologue a fn /\
  fn_has_code a z fn /\ fn_has_code z final fn /\
  (if block_is_terminated z then ((),z)
   else comp_ignore_bind
     (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
     (case rt of NONE => emit_inst RET [pc] [] | SOME _ => emit_inst INVALID [] []) z) = ((),final)
Proof
  strip_tac >>
  `cs_extends entry prologue` by
    (drule (SRULE [cs_appends_def] cs_appends_internal_function_entry) >> simp[]) >>
  `cs_extends prologue a` by
    (drule (SRULE [cs_appends_def] lock_appends) >> simp[]) >>
  `cs_extends a z` by
    (drule (SRULE [cs_mono_def] stmts_env_cs_mono) >> simp[]) >>
  `(if block_is_terminated z then ((),z)
    else comp_ignore_bind
      (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
      (case rt of NONE => emit_inst RET [pc] [] | SOME _ => emit_inst INVALID [] []) z) = ((),final)` by
    (qpat_x_assum `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_internal_function_entry_factorization, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, comp_get_def, compile_stmts_env] >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `block_is_terminated z` >> simp[] >>
     Cases_on `rt` >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  `cs_extends z final` by
    (Cases_on `block_is_terminated z` >> gvs[cs_extends_refl] >>
     drule (SRULE [cs_appends_def] suffix_appends) >> simp[]) >>
  `cs_extends entry a /\ cs_extends entry z` by metis_tac[cs_extends_trans] >>
  `fn_has_code entry z fn /\ fn_has_code z final fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code entry a fn /\ fn_has_code a z fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code entry prologue fn /\ fn_has_code prologue a fn` by metis_tac[fn_has_code_split] >>
  simp[]
QED

Theorem selected_shadow_body_eqs[local]:
  gas_shadow_state prologue prologueS /\
  (if nr then compile_nonreentrant_lock key trans view else comp_return ()) prologue = ((),a) /\
  stmts_env body_ce NoLoop ty ss a = (out,z) ==>
  ?aS zS.
    (if nr then compile_nonreentrant_lock key trans view else comp_return ()) prologueS = ((),aS) /\
    gas_shadow_state a aS /\ gas_shadow_state z zS /\
    stmts_env (gas_shadow_env T body_ce) NoLoop ty (MAP gas_shadow_stmt ss) aS =
      (gas_shadow_env T out,zS)
Proof
  strip_tac >>
  qabbrev_tac `lock = if nr then compile_nonreentrant_lock key trans view else comp_return ()` >>
  `gas_shadow_compiles lock lock` by
    (Cases_on `nr` >> simp[Abbr `lock`, gas_shadow_compiles_nonreentrant_lock,
                           gas_shadow_compiles_return]) >>
  Cases_on `lock prologueS` >> rename1 `lock prologueS = (u,aS)` >> Cases_on `u` >>
  `gas_shadow_state a aS` by
    (fs[gas_shadow_compiles_def] >> first_x_assum (qspecl_then [`prologue`, `prologueS`] mp_tac) >> simp[]) >>
  Cases_on `stmts_env (gas_shadow_env T body_ce) NoLoop ty (MAP gas_shadow_stmt ss) aS` >>
  rename1 `_ = (outS,zS)` >>
  qspecl_then [`ss`,`body_ce`,`NoLoop`,`ty`] mp_tac
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  simp[gas_shadow_compiles_env_def] >>
  disch_then (qspecl_then [`a`,`aS`] mp_tac) >> gvs[]
QED

Theorem selected_callee_code_cuts_mods:
  compile_internal_function ce params has_rb nr key trans view ctor ilen ss rt entry = ((),final) /\
  fn_has_code entry final callee /\
  compile_internal_function (gas_shadow_env T ce) params has_rb nr key trans view ctor ilen
    (MAP gas_shadow_stmt ss) rt entryS = ((),finalS) /\
  gas_shadow_state entry entryS /\ fn_has_code entryS finalS sf ==>
  ?ce1 caps pc capture imm reserved ce2 materialized prologue body_ce ty a out z aS zS.
    compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,pc),capture) /\
    (if ctor /\ 0 < ilen then
       comp_bind (compile_fixed_region_with_id ilen)
         (\ar. comp_return (SOME (SND ar).buf_operand))
     else comp_return NONE) capture = (imm,reserved) /\
    materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
    (case rt of NONE => comp_return ()
     | SOME t => if 0 < ce.ce_returns_count then
         comp_ignore_bind (compile_alloc_buffer (type_memory_bytes ce t))
           (comp_return ())
       else comp_return ()) materialized = ((),prologue) /\
    body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> /\
    ty = (case rt of SOME t => t | NONE => BaseT BoolT) /\
    (if nr then compile_nonreentrant_lock key trans view else comp_return ()) prologue = ((),a) /\
    stmts_env body_ce NoLoop ty ss a = (out,z) /\
    (if block_is_terminated z then ((),z)
     else comp_ignore_bind
       (if nr then compile_nonreentrant_unlock key trans view else comp_return ())
       (case rt of NONE => emit_inst RET [pc] [] | SOME _ => emit_inst INVALID [] []) z) = ((),final) /\
    fn_has_code entry capture callee /\ fn_has_code capture reserved callee /\
    fn_has_code reserved materialized callee /\ fn_has_code materialized prologue callee /\
    fn_has_code prologue a callee /\ fn_has_code a z callee /\ fn_has_code z final callee /\
    gas_shadow_state a aS /\ gas_shadow_state z zS /\
    stmts_env (gas_shadow_env T body_ce) NoLoop ty (MAP gas_shadow_stmt ss) aS =
      (gas_shadow_env T out,zS) /\ fn_has_code aS zS sf
Proof
  strip_tac >>
  Cases_on `compile_internal_function_entry ce params has_rb ctor ilen rt entry` >>
  rename1 `_ = (info,prologue)` >> PairCases_on `info` >>
  rename1 `_ = ((ce2,pc,imm),prologue)` >>
  drule_then strip_assume_tac selected_entry_phases >>
  qabbrev_tac `lock = if nr then compile_nonreentrant_lock key trans view else comp_return ()` >>
  Cases_on `lock prologue` >> rename1 `lock prologue = (u,a)` >> Cases_on `u` >>
  qabbrev_tac `body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>` >>
  qabbrev_tac `ty = case rt of SOME t => t | NONE => BaseT BoolT` >>
  Cases_on `stmts_env body_ce NoLoop ty ss a` >> rename1 `_ = (out,z)` >>
  unabbrev_all_tac >>
  drule_all_then strip_assume_tac selected_body_intervals >>
  drule_all_then strip_assume_tac (Q.INST [`sd` |-> `T`] intcall_shadow_entry_cut) >>
  drule_all_then strip_assume_tac selected_shadow_body_eqs >>
  `gas_shadow_env T (ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) =
    (gas_shadow_env T ce2) with <|ce_imm_alloca := imm; ce_alloca_locals := T|>` by
    simp[gas_shadow_env_def] >>
  qpat_assum `gas_shadow_env T (_ with <|ce_imm_alloca := _; ce_alloca_locals := T|>) = _`
    (fn eq => qpat_assum `stmts_env (gas_shadow_env T _) _ _ (MAP gas_shadow_stmt _) _ = _`
      (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  `fn_has_code aS zS sf` by
    (drule_all (Q.INST [`ce` |-> `gas_shadow_env T ce`,
                        `ss` |-> `MAP gas_shadow_stmt ss`] selected_body_intervals) >> simp[]) >>
  `cs_extends entry reserved /\ cs_extends entry materialized` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code entry materialized callee /\ fn_has_code materialized prologue callee` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code entry reserved callee /\ fn_has_code reserved materialized callee` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code entry capture callee /\ fn_has_code capture reserved callee` by
    metis_tac[fn_has_code_split] >>
  map_every qexists_tac
    [`ce1`, `caps`, `pc`, `capture`, `imm`, `reserved`, `ce2`,
     `materialized`, `prologue`,
     `ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|>`,
     `case rt of SOME t => t | NONE => BaseT BoolT`,
     `a`, `out`, `z`, `aS`, `zS`] >> simp[]
QED

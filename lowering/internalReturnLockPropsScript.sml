(* TOP-LEVEL: explicit internal returns release their mutating transient guard
   before RET, including bare early returns and single-value returns. *)
Theory internalReturnLockProps
Ancestors
  stmtLowering nonreentrantEquiv transientLockProps
  emitHelperProps exprLoweringProps emitHelper compileEnv context
  venomExecSemantics venomState venomInst
  vyperAST list rich_list

Theorem compile_return_unlock_source_correct:
  state_rel cenv cx vs ss /\
  cenv.ce_nonreentrant = (T,key,T,is_view) /\
  compile_return_unlock cenv st = ((),st') ==>
  ?vs' ss'.
    (if is_view then vyperState$return () else
       vyperInterpreter$release_nonreentrant_lock cx.txn.target key) vs =
      (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel cenv cx vs' ss'
Proof
  rpt strip_tac >> fs[compile_return_unlock_def] >>
  qpat_x_assum `cenv.ce_nonreentrant = _` SUBST_ALL_TAC >> fs[] >>
  drule_all compile_nonreentrant_unlock_source_correct >> simp[]
QED

Theorem compile_internal_bare_return_unlock_code:
  cenv.ce_return_pc = SOME (PtrVar rpc byte_size) /\
  cenv.ce_nonreentrant = (T,key,T,F) /\
  compile_stmt cenv lctx ty (Return NONE) st = ((),st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id TSTORE [Lit (n2w key);Lit 0w] [];
     mk_inst (st.cs_next_id + 1) RET [rpc] []]
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def] >>
  simp[compile_return_unlock_def, compile_nonreentrant_unlock_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       emitted_insts_def, DROP_LENGTH_APPEND] >>
  strip_tac >> gvs[DROP_LENGTH_APPEND]
QED

Theorem compile_internal_value_return_unlock_code:
  cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  cenv.ce_nonreentrant = (T,key,T,F) /\
  compile_internal_return_from_env cenv ty src_ty value rpc st = ((),st') ==>
  emitted_insts st st' =
    [mk_inst st.cs_next_id TSTORE [Lit (n2w key);Lit 0w] [];
     mk_inst (st.cs_next_id + 1) RET [value;rpc] []]
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, compile_internal_return_def,
       compile_return_unlock_def, compile_nonreentrant_unlock_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_void_def, emit_inst_def, fresh_id_def, emit_def,
       emitted_insts_def, DROP_LENGTH_APPEND] >>
  strip_tac >> gvs[DROP_LENGTH_APPEND]
QED

Theorem eval_operand_tstore[simp]:
  eval_operand op (tstore key value ss) = eval_operand op ss
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, tstore_def]
QED

Theorem eval_operands_tstore[simp]:
  eval_operands ops (tstore key value ss) = eval_operands ops ss
Proof
  Induct_on `ops` >> simp[eval_operands_def]
QED

Theorem eval_operands_append[local]:
  eval_operands (left ++ right) ss =
    case eval_operands left ss of
      NONE => NONE
    | SOME words => OPTION_MAP (APPEND words) (eval_operands right ss)
Proof
  Induct_on `left`
  >- (Cases_on `eval_operands right ss` >> simp[eval_operands_def]) >>
  simp[eval_operands_def] >>
  Cases_on `eval_operand h ss` >> simp[] >>
  Cases_on `eval_operands left ss` >> simp[] >>
  Cases_on `eval_operands right ss` >> simp[]
QED

Theorem step_RET_values[local]:
  !values ss words rpc pc id.
  eval_operands values ss = SOME words /\ eval_operand rpc ss = SOME pc ==>
  step_inst_base (mk_inst id RET (values ++ [rpc]) []) ss =
    IntRet <| iret_values := words; iret_adopt_fmp := NONE |> ss
Proof
  rpt strip_tac >> Cases_on `words` >>
  simp[step_inst_base_def, mk_inst_def, eval_operands_append,
       eval_operands_def, FRONT_DEF, FRONT_APPEND]
QED

Theorem transient_unlock_return_execution:
  !values ss words rpc pc id key.
  eval_operands values ss = SOME words /\ eval_operand rpc ss = SOME pc ==>
  run_inst_seq
    [mk_inst id TSTORE [Lit key;Lit 0w] [];
     mk_inst (id + 1) RET (values ++ [rpc]) []] ss =
    IntRet <| iret_values := words; iret_adopt_fmp := NONE |>
      (tstore key 0w ss)
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst (id + 1) RET (values ++ [rpc]) [])
     (tstore key 0w ss) =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |>
       (tstore key 0w ss)` by
    (irule step_RET_values >> simp[]) >>
  simp[run_inst_seq_def, step_TSTORE_lit]
QED

Theorem compile_internal_bare_return_releases:
  cenv.ce_return_pc = SOME (PtrVar rpc byte_size) /\
  cenv.ce_nonreentrant = (T,key,T,F) /\
  compile_stmt cenv lctx ty (Return NONE) st = ((),st') /\
  eval_operand rpc ss = SOME pc ==>
  run_inst_seq (emitted_insts st st') ss =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (tstore (n2w key) 0w ss)
Proof
  strip_tac >> drule_all compile_internal_bare_return_unlock_code >> strip_tac >>
  asm_rewrite_tac [] >>
  irule (SRULE [eval_operands_def]
    (Q.SPEC `[]` transient_unlock_return_execution)) >> simp[]
QED

Theorem compile_internal_value_return_releases:
  cenv.ce_return_buf = NONE /\ cenv.ce_returns_count = 1 /\
  cenv.ce_nonreentrant = (T,key,T,F) /\
  compile_internal_return_from_env cenv ty src_ty value rpc st = ((),st') /\
  eval_operand value ss = SOME word /\ eval_operand rpc ss = SOME pc ==>
  run_inst_seq (emitted_insts st st') ss =
    IntRet <| iret_values := [word]; iret_adopt_fmp := NONE |>
      (tstore (n2w key) 0w ss)
Proof
  strip_tac >> drule_all compile_internal_value_return_unlock_code >> strip_tac >>
  asm_rewrite_tac [] >>
  irule (SRULE [eval_operands_def]
    (Q.SPEC `[value]` transient_unlock_return_execution)) >>
  simp[eval_operands_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("internal return theorem is not kernel closed: " ^ name)
  end) (DB.thms "internalReturnLockProps");

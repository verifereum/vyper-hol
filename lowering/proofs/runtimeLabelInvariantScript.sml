(* Operand exclusions and instruction checks for raw lowering. *)
Theory runtimeLabelInvariant
Ancestors
  loweringShapeDefs moduleLowering compileEnv context exprLowering
  stmtLowering emitHelper venomInst list exprCallBounds

Definition rb_operand_ok_def:
  rb_operand_ok op <=> op <> Label "runtime_begin"
End

(* Only the two reserved source labels may be excluded. *)
Definition rb_operand_ok_for_def:
  rb_operand_ok_for (source_checks : string set # bool) op <=>
    case op of
      Label l => ((l <> "runtime_begin" \/ "runtime_begin" NOTIN FST source_checks) /\
                (l <> "code_end" \/ "code_end" NOTIN FST source_checks))
    | _ => T
End

Theorem rb_operand_ok_legacy:
  rb_operand_ok_for ({"runtime_begin"}, F) = rb_operand_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> simp[rb_operand_ok_for_def, rb_operand_ok_def]
QED

Definition rb_state_ok_def:
  rb_state_ok st <=>
    EVERY (\i. EVERY rb_operand_ok i.inst_operands) (state_insts st)
End

Definition source_codecopy_arity_ok_def[simp]:
  source_codecopy_arity_ok checks opc (ops : operand list) <=>
    (SND checks /\ opc = CODECOPY ==> LENGTH ops = 3)
End

Theorem cond_opcode_eq_codecopy[simp]:
  ((if c then op1 else op2) = CODECOPY) <=>
    (if c then op1 = CODECOPY else op2 = CODECOPY)
Proof
  Cases_on `c` >> simp[]
QED

Definition source_inst_ok_def:
  source_inst_ok checks inst <=>
    EVERY (rb_operand_ok_for checks) inst.inst_operands /\
    source_codecopy_arity_ok checks inst.inst_opcode inst.inst_operands
End

Definition rb_state_ok_for_def:
  rb_state_ok_for source_checks st <=>
    EVERY (source_inst_ok source_checks) (state_insts st)
End

Theorem rb_state_ok_legacy:
  rb_state_ok_for ({"runtime_begin"}, F) = rb_state_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_state_ok_for_def, rb_state_ok_def, rb_operand_ok_legacy, source_inst_ok_def, source_codecopy_arity_ok_def, EVERY_MEM]
QED

Definition rb_step_def:
  rb_step Q (action : 'a compiler) <=>
    !st. rb_state_ok st ==>
      let (v,st') = action st in rb_state_ok st' /\ Q v
End

Definition rb_step_for_def:
  rb_step_for source_checks Q (action : 'a compiler) <=>
    !st. (rb_state_ok_for source_checks) st ==>
      let (v,st') = action st in (rb_state_ok_for source_checks) st' /\ Q v
End

Theorem rb_step_legacy:
  rb_step_for ({"runtime_begin"}, F) = rb_step
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_step_for_def, rb_step_def, rb_state_ok_legacy]
QED

Definition rb_buffer_ok_def:
  rb_buffer_ok buf <=> rb_operand_ok buf.buf_operand
End

Definition rb_buffer_ok_for_def:
  rb_buffer_ok_for source_checks buf <=> (rb_operand_ok_for source_checks) buf.buf_operand
End

Theorem rb_buffer_ok_legacy:
  rb_buffer_ok_for ({"runtime_begin"}, F) = rb_buffer_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_buffer_ok_for_def, rb_buffer_ok_def, rb_operand_ok_legacy]
QED

Definition rb_ptr_ok_def:
  rb_ptr_ok p <=> rb_operand_ok p.ptr_operand /\
    (case p.ptr_buf of NONE => T | SOME b => rb_buffer_ok b)
End

Definition rb_ptr_ok_for_def:
  rb_ptr_ok_for source_checks p <=> (rb_operand_ok_for source_checks) p.ptr_operand /\
    (case p.ptr_buf of NONE => T | SOME b => (rb_buffer_ok_for source_checks) b)
End

Theorem rb_ptr_ok_legacy[local]:
  rb_ptr_ok_for ({"runtime_begin"}, F) = rb_ptr_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_ptr_ok_for_def, rb_ptr_ok_def, rb_buffer_ok_legacy, rb_operand_ok_legacy]
QED

Definition rb_value_ok_def:
  rb_value_ok (StackValue ty op) = rb_operand_ok op /\
  rb_value_ok (LocatedValue ty p) = rb_ptr_ok p
End

Definition rb_value_ok_for_def:
  rb_value_ok_for source_checks (StackValue ty op) = (rb_operand_ok_for source_checks) op /\
  rb_value_ok_for source_checks (LocatedValue ty p) = (rb_ptr_ok_for source_checks) p
End

Theorem rb_value_ok_legacy:
  rb_value_ok_for ({"runtime_begin"}, F) = rb_value_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> simp[rb_value_ok_for_def, rb_value_ok_def, rb_operand_ok_legacy, rb_ptr_ok_legacy]
QED

Definition rb_location_ok_def:
  rb_location_ok (PtrVar op n) = rb_operand_ok op /\
  rb_location_ok (MemLoc off n) = T /\
  rb_location_ok (StorageLoc slot) = T /\
  rb_location_ok (TransientLoc slot) = T /\
  rb_location_ok (ImmutableLoc off) = T
End

Definition rb_location_ok_for_def:
  rb_location_ok_for source_checks (PtrVar op n) = (rb_operand_ok_for source_checks) op /\
  rb_location_ok_for source_checks (MemLoc off n) = T /\
  rb_location_ok_for source_checks (StorageLoc slot) = T /\
  rb_location_ok_for source_checks (TransientLoc slot) = T /\
  rb_location_ok_for source_checks (ImmutableLoc off) = T
End

Theorem rb_location_ok_legacy:
  rb_location_ok_for ({"runtime_begin"}, F) = rb_location_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> simp[rb_location_ok_for_def, rb_location_ok_def, rb_operand_ok_legacy]
QED

Definition rb_env_ok_def:
  rb_env_ok env <=>
    (!k loc. FLOOKUP env.ce_vars k = SOME loc ==> rb_location_ok loc) /\
    (!k loc. FLOOKUP env.ce_module_vars k = SOME loc ==> rb_location_ok loc) /\
    (case env.ce_return_buf of NONE => T | SOME loc => rb_location_ok loc) /\
    (case env.ce_return_pc of NONE => T | SOME loc => rb_location_ok loc) /\
    (case env.ce_imm_alloca of NONE => T | SOME op => rb_operand_ok op) /\
    (case env.ce_ctor_exit_label of NONE => T
       | SOME l => rb_operand_ok (Label l))
End

Definition rb_env_ok_for_def:
  rb_env_ok_for source_checks env <=>
    (!k loc. FLOOKUP env.ce_vars k = SOME loc ==> (rb_location_ok_for source_checks) loc) /\
    (!k loc. FLOOKUP env.ce_module_vars k = SOME loc ==> (rb_location_ok_for source_checks) loc) /\
    (case env.ce_return_buf of NONE => T | SOME loc => (rb_location_ok_for source_checks) loc) /\
    (case env.ce_return_pc of NONE => T | SOME loc => (rb_location_ok_for source_checks) loc) /\
    (case env.ce_imm_alloca of NONE => T | SOME op => (rb_operand_ok_for source_checks) op) /\
    (case env.ce_ctor_exit_label of NONE => T
       | SOME l => (rb_operand_ok_for source_checks) (Label l))
End

Theorem rb_env_ok_legacy:
  rb_env_ok_for ({"runtime_begin"}, F) = rb_env_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_env_ok_for_def, rb_env_ok_def, rb_location_ok_legacy, rb_operand_ok_legacy]
QED

Definition rb_loop_ok_def:
  rb_loop_ok NoLoop = T /\
  rb_loop_ok (InLoop exit incr) =
    (rb_operand_ok (Label exit) /\ rb_operand_ok (Label incr))
End

Definition rb_loop_ok_for_def:
  rb_loop_ok_for source_checks NoLoop = T /\
  rb_loop_ok_for source_checks (InLoop exit incr) =
    ((rb_operand_ok_for source_checks) (Label exit) /\ (rb_operand_ok_for source_checks) (Label incr))
End

Theorem rb_loop_ok_legacy[local]:
  rb_loop_ok_for ({"runtime_begin"}, F) = rb_loop_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> simp[rb_loop_ok_for_def, rb_loop_ok_def, rb_operand_ok_legacy]
QED

Definition rb_expr_callback_def:
  rb_expr_callback bound cfn <=>
    !env ty e. expr_size e + cenv_defaults_size env < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env ty e)
End

Definition rb_expr_callback_for_def:
  rb_expr_callback_for source_checks bound cfn <=>
    !env ty e. expr_size e + cenv_defaults_size env < bound /\ (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ty e)
End

Theorem rb_expr_callback_legacy[local]:
  rb_expr_callback_for ({"runtime_begin"}, F) = rb_expr_callback
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_expr_callback_for_def, rb_expr_callback_def, rb_env_ok_legacy, rb_step_legacy, rb_value_ok_legacy]
QED

Definition rb_builtin_callback_def:
  rb_builtin_callback bound cfn <=>
    !env ret_ty ty bi args.
      list_size expr_size args + cenv_defaults_size env < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env ret_ty ty bi args)
End

Definition rb_builtin_callback_for_def:
  rb_builtin_callback_for source_checks bound cfn <=>
    !env ret_ty ty bi args.
      list_size expr_size args + cenv_defaults_size env < bound /\ (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env ret_ty ty bi args)
End

Theorem rb_builtin_callback_legacy[local]:
  rb_builtin_callback_for ({"runtime_begin"}, F) = rb_builtin_callback
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_builtin_callback_for_def, rb_builtin_callback_def, rb_env_ok_legacy, rb_step_legacy, rb_value_ok_legacy]
QED

Definition rb_type_callback_def:
  rb_type_callback bound cfn <=>
    !env vv_ty ty tb ret_ty args.
      list_size expr_size args + cenv_defaults_size env < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env vv_ty ty tb ret_ty args)
End

Definition rb_type_callback_for_def:
  rb_type_callback_for source_checks bound cfn <=>
    !env vv_ty ty tb ret_ty args.
      list_size expr_size args + cenv_defaults_size env < bound /\ (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (cfn env vv_ty ty tb ret_ty args)
End

Theorem rb_type_callback_legacy[local]:
  rb_type_callback_for ({"runtime_begin"}, F) = rb_type_callback
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_type_callback_for_def, rb_type_callback_def, rb_env_ok_legacy, rb_step_legacy, rb_value_ok_legacy]
QED

Definition rb_expr_contract_def:
  rb_expr_contract <=>
    (!env ty e. rb_env_ok env ==>
      rb_step rb_value_ok (compile_expr env ty e)) /\
    (!env ret_ty ty bi args. rb_env_ok env ==>
      rb_step rb_value_ok (compile_builtin_dispatch env ret_ty ty bi args)) /\
    (!env vv_ty ty tb ret_ty args. rb_env_ok env ==>
      rb_step rb_value_ok
        (compile_type_builtin_dispatch env vv_ty ty tb ret_ty args))
End

Definition rb_expr_contract_for_def:
  rb_expr_contract_for source_checks <=>
    (!env ty e. (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_expr env ty e)) /\
    (!env ret_ty ty bi args. (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks) (compile_builtin_dispatch env ret_ty ty bi args)) /\
    (!env vv_ty ty tb ret_ty args. (rb_env_ok_for source_checks) env ==>
      (rb_step_for source_checks) (rb_value_ok_for source_checks)
        (compile_type_builtin_dispatch env vv_ty ty tb ret_ty args))
End

Theorem rb_expr_contract_legacy:
  rb_expr_contract_for ({"runtime_begin"}, F) = rb_expr_contract
Proof

  simp[rb_expr_contract_for_def, rb_expr_contract_def, rb_env_ok_legacy, rb_step_legacy, rb_value_ok_legacy]
QED

Definition rb_stmt_contract_def:
  rb_stmt_contract <=>
    (!env lctx ty s. rb_env_ok env /\ rb_loop_ok lctx ==>
      rb_step (K T) (compile_stmt env lctx ty s)) /\
    (!env lctx ty ss. rb_env_ok env /\ rb_loop_ok lctx ==>
      rb_step (K T) (compile_stmts env lctx ty ss))
End

Definition rb_stmt_contract_for_def:
  rb_stmt_contract_for source_checks <=>
    (!env lctx ty s. (rb_env_ok_for source_checks) env /\ (rb_loop_ok_for source_checks) lctx ==>
      (rb_step_for source_checks) (K T) (compile_stmt env lctx ty s)) /\
    (!env lctx ty ss. (rb_env_ok_for source_checks) env /\ (rb_loop_ok_for source_checks) lctx ==>
      (rb_step_for source_checks) (K T) (compile_stmts env lctx ty ss))
End

Theorem rb_stmt_contract_legacy:
  rb_stmt_contract_for ({"runtime_begin"}, F) = rb_stmt_contract
Proof

  simp[rb_stmt_contract_for_def, rb_stmt_contract_def, rb_env_ok_legacy, rb_loop_ok_legacy, rb_step_legacy]
QED

Theorem rb_step_return_for:
  Q x ==> (rb_step_for source_checks) Q (comp_return x)
Proof
  simp[rb_step_for_def, comp_return_def]
QED

Theorem rb_step_bind_for:
  (rb_step_for source_checks) P m /\ (!x. P x ==> (rb_step_for source_checks) Q (f x)) ==>
  (rb_step_for source_checks) Q (comp_bind m f)
Proof
  rw[rb_step_for_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem rb_operand_basic_for[simp]:
  (rb_operand_ok_for source_checks) (Var v) /\ (rb_operand_ok_for source_checks) (Lit n) /\
  ((rb_operand_ok_for source_checks) (Label l) <=> ((l <> "runtime_begin" \/ "runtime_begin" NOTIN FST source_checks) /\
                (l <> "code_end" \/ "code_end" NOTIN FST source_checks)))
Proof
  simp[rb_operand_ok_for_def]
QED

Theorem rb_emit_for[local]:
  source_inst_ok source_checks inst ==> (rb_step_for source_checks) (K T) (emit inst)
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, emit_def,
       state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_new_block_for:
  (rb_step_for source_checks) (K T) (new_block label)
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, new_block_def,
       state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_fresh_label_for:
  (rb_step_for source_checks) (\l. (rb_operand_ok_for source_checks) (Label l)) (fresh_label suffix)
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, fresh_label_def,
       fresh_label_output_def, state_insts_def, all_blocks_def]
QED

Theorem rb_fresh_var_for:
  (rb_step_for source_checks) (K T) fresh_var
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, fresh_var_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_fresh_id_for[local]:
  (rb_step_for source_checks) (K T) fresh_id
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, fresh_id_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_emit_inst_for:
  EVERY (rb_operand_ok_for source_checks) ops /\ source_codecopy_arity_ok source_checks opc ops ==> (rb_step_for source_checks) (K T) (emit_inst opc ops outs)
Proof
  strip_tac >> rewrite_tac[emit_inst_def] >>
  irule rb_step_bind_for >> qexists_tac `K T` >>
  simp[rb_fresh_id_for] >> gen_tac >>
  irule rb_emit_for >> gvs[source_inst_ok_def, mk_inst_def]
QED

Theorem rb_base_ptr_for:
  (rb_buffer_ok_for source_checks) b ==> (rb_ptr_ok_for source_checks) (base_ptr b)
Proof
  simp[rb_buffer_ok_for_def, rb_ptr_ok_for_def, base_ptr_def]
QED

Theorem rb_mk_ptr_for:
  (rb_operand_ok_for source_checks) op ==> (rb_ptr_ok_for source_checks) (mk_ptr op loc)
Proof
  simp[rb_ptr_ok_for_def, mk_ptr_def]
QED

Theorem rb_value_operand_for:
  (rb_value_ok_for source_checks) v ==> (rb_operand_ok_for source_checks) (vv_operand v)
Proof
  Cases_on `v` >> simp[rb_value_ok_for_def, rb_ptr_ok_for_def, vv_operand_def]
QED

Theorem rb_internal_fn_label_for:
  (rb_operand_ok_for source_checks) (Label (internal_fn_label id name tys ctor))
Proof
  simp[internal_fn_label_def]
QED

(* Package predicates inspect only operand and branch-label sources. *)
Definition rb_external_package_ok_def:
  rb_external_package_ok
    (lbl,env,pos,min_cds,payable,nr,key,trans,view,body,ret) <=>
      rb_env_ok env /\ ~env.ce_is_ctor /\ rb_operand_ok (Label lbl)
End

Definition rb_external_package_ok_for_def:
  rb_external_package_ok_for source_checks
    (lbl,env,pos,min_cds,payable,nr,key,trans,view,body,ret) <=>
      (rb_env_ok_for source_checks) env /\ ~env.ce_is_ctor /\ (rb_operand_ok_for source_checks) (Label lbl)
End

Theorem rb_external_package_ok_legacy:
  rb_external_package_ok_for ({"runtime_begin"}, F) = rb_external_package_ok
Proof
  rw[FUN_EQ_THM] >>
  PairCases_on `x` >> simp[rb_external_package_ok_for_def, rb_external_package_ok_def, rb_env_ok_legacy, rb_operand_ok_legacy, rb_operand_ok_def]
QED

Definition rb_internal_package_ok_def:
  rb_internal_package_ok
    (lbl,env,params,has_buf,nr,key,trans,view,ctor,imm_len,body,ret) <=>
      rb_env_ok env /\ ~env.ce_is_ctor /\ ~ctor /\ rb_operand_ok (Label lbl)
End

Definition rb_internal_package_ok_for_def:
  rb_internal_package_ok_for source_checks
    (lbl,env,params,has_buf,nr,key,trans,view,ctor,imm_len,body,ret) <=>
      (rb_env_ok_for source_checks) env /\ ~env.ce_is_ctor /\ ~ctor /\ (rb_operand_ok_for source_checks) (Label lbl)
End

Theorem rb_internal_package_ok_legacy[local]:
  rb_internal_package_ok_for ({"runtime_begin"}, F) = rb_internal_package_ok
Proof
  rw[FUN_EQ_THM] >>
  PairCases_on `x` >> simp[rb_internal_package_ok_for_def, rb_internal_package_ok_def, rb_env_ok_legacy, rb_operand_ok_legacy, rb_operand_ok_def]
QED

Definition rb_fallback_ok_def:
  rb_fallback_ok NONE = T /\
  rb_fallback_ok (SOME (env,payable,nr,key,trans,view,body,ret)) =
    (rb_env_ok env /\ ~env.ce_is_ctor)
End

Definition rb_fallback_ok_for_def:
  rb_fallback_ok_for source_checks NONE = T /\
  rb_fallback_ok_for source_checks (SOME (env,payable,nr,key,trans,view,body,ret)) =
    ((rb_env_ok_for source_checks) env /\ ~env.ce_is_ctor)
End

Theorem rb_fallback_ok_legacy[local]:
  rb_fallback_ok_for ({"runtime_begin"}, F) = rb_fallback_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> TRY (PairCases_on `x'`) >> simp[rb_fallback_ok_for_def, rb_fallback_ok_def, rb_env_ok_legacy]
QED

Definition rb_runtime_inputs_ok_def:
  rb_runtime_inputs_ok selectors externals internals fallback <=>
    EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) selectors /\
    EVERY rb_external_package_ok externals /\
    EVERY rb_internal_package_ok internals /\ rb_fallback_ok fallback
End

Definition rb_runtime_inputs_ok_for_def:
  rb_runtime_inputs_ok_for source_checks selectors externals internals fallback <=>
    EVERY (\(sel,lbl,tz). (rb_operand_ok_for source_checks) (Label lbl)) selectors /\
    EVERY (rb_external_package_ok_for source_checks) externals /\
    EVERY (rb_internal_package_ok_for source_checks) internals /\ (rb_fallback_ok_for source_checks) fallback
End

Theorem rb_runtime_inputs_ok_legacy:
  rb_runtime_inputs_ok_for ({"runtime_begin"}, F) = rb_runtime_inputs_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_runtime_inputs_ok_for_def, rb_runtime_inputs_ok_def, rb_external_package_ok_legacy, rb_fallback_ok_legacy, rb_internal_package_ok_legacy, rb_operand_ok_legacy, rb_operand_ok_def]
QED

Definition rb_group_ok_def:
  rb_group_ok (ExternalSingle (sel,lbl,tz) package) =
    (rb_operand_ok (Label lbl) /\ rb_external_package_ok package) /\
  rb_group_ok (ExternalDefaults common entries specs offset) =
    (rb_env_ok common.ec_env /\ ~common.ec_env.ce_is_ctor /\
     rb_operand_ok (Label common.ec_common_label) /\
     EVERY (\(sel,lbl,min_cds,k). rb_operand_ok (Label lbl)) entries)
End

Definition rb_group_ok_for_def:
  rb_group_ok_for source_checks (ExternalSingle (sel,lbl,tz) package) =
    ((rb_operand_ok_for source_checks) (Label lbl) /\ (rb_external_package_ok_for source_checks) package) /\
  rb_group_ok_for source_checks (ExternalDefaults common entries specs offset) =
    ((rb_env_ok_for source_checks) common.ec_env /\ ~common.ec_env.ce_is_ctor /\
     (rb_operand_ok_for source_checks) (Label common.ec_common_label) /\
     EVERY (\(sel,lbl,min_cds,k). (rb_operand_ok_for source_checks) (Label lbl)) entries)
End

Theorem rb_group_ok_legacy:
  rb_group_ok_for ({"runtime_begin"}, F) = rb_group_ok
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >> TRY (PairCases_on `p`) >> simp[rb_group_ok_for_def, rb_group_ok_def, rb_env_ok_legacy, rb_external_package_ok_legacy, rb_operand_ok_legacy, rb_operand_ok_def]
QED

Definition rb_grouped_runtime_inputs_ok_def:
  rb_grouped_runtime_inputs_ok groups internals fallback <=>
    EVERY rb_group_ok groups /\ EVERY rb_internal_package_ok internals /\
    rb_fallback_ok fallback
End

Definition rb_grouped_runtime_inputs_ok_for_def:
  rb_grouped_runtime_inputs_ok_for source_checks groups internals fallback <=>
    EVERY (rb_group_ok_for source_checks) groups /\ EVERY (rb_internal_package_ok_for source_checks) internals /\
    (rb_fallback_ok_for source_checks) fallback
End

Theorem rb_grouped_runtime_inputs_ok_legacy:
  rb_grouped_runtime_inputs_ok_for ({"runtime_begin"}, F) = rb_grouped_runtime_inputs_ok
Proof
  rw[FUN_EQ_THM] >>
  simp[rb_grouped_runtime_inputs_ok_for_def, rb_grouped_runtime_inputs_ok_def, rb_fallback_ok_legacy, rb_group_ok_legacy, rb_internal_package_ok_legacy]
QED

Theorem rb_emit_void_for:
  EVERY (rb_operand_ok_for source_checks) ops /\ source_codecopy_arity_ok source_checks opc ops ==> (rb_step_for source_checks) (K T) (emit_void opc ops)
Proof
  strip_tac >> rewrite_tac[emit_void_def] >>
  irule rb_step_bind_for >> qexists_tac `K T` >>
  simp[rb_fresh_id_for] >> gen_tac >>
  irule rb_emit_for >> gvs[source_inst_ok_def, mk_inst_def]
QED

Theorem rb_emit_op_for:
  EVERY (rb_operand_ok_for source_checks) ops /\ source_codecopy_arity_ok source_checks opc ops ==> (rb_step_for source_checks) (rb_operand_ok_for source_checks) (emit_op opc ops)
Proof
  strip_tac >> gvs[rb_step_for_def, rb_state_ok_for_def, source_inst_ok_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, mk_inst_def, state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_step_weaken_for:
  (rb_step_for source_checks) P m /\ (!x. P x ==> Q x) ==> (rb_step_for source_checks) Q m
Proof
  rw[rb_step_for_def] >> Cases_on `m st` >> gvs[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem rb_step_ignore_bind_for:
  (rb_step_for source_checks) P m /\ (rb_step_for source_checks) Q n ==> (rb_step_for source_checks) Q (comp_ignore_bind m n)
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule rb_step_bind_for >> qexists_tac `P` >> simp[]
QED

Theorem rb_invalid_expr_call_for[local]:
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (invalid_expr_call ty)
Proof
  simp[rb_step_for_def, rb_state_ok_for_def, source_inst_ok_def, invalid_expr_call_def,
       rb_value_ok_for_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, mk_inst_def, state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_expr_child_callback_for:
  (rb_expr_callback_for source_checks) bound cfn /\ (rb_env_ok_for source_checks) env ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (expr_child_callback bound cfn env ty e)
Proof
  rw[rb_expr_callback_for_def] >>
  Cases_on `expr_size e + cenv_defaults_size env < bound` >>
  gvs[rb_step_for_def, expr_child_callback_def] >>
  metis_tac[rb_invalid_expr_call_for, rb_step_for_def]
QED

Theorem rb_builtin_child_callback_for:
  (rb_builtin_callback_for source_checks) bound cfn /\ (rb_env_ok_for source_checks) env ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (builtin_child_callback bound cfn env ret_ty ty bi args)
Proof
  rw[rb_builtin_callback_for_def] >>
  Cases_on `list_size expr_size args + cenv_defaults_size env < bound` >>
  gvs[rb_step_for_def, builtin_child_callback_def] >>
  metis_tac[rb_invalid_expr_call_for, rb_step_for_def]
QED

Theorem rb_type_child_callback_for:
  (rb_type_callback_for source_checks) bound cfn /\ (rb_env_ok_for source_checks) env ==>
  (rb_step_for source_checks) (rb_value_ok_for source_checks) (type_child_callback bound cfn env vv_ty ty tb ret_ty args)
Proof
  rw[rb_type_callback_for_def] >>
  Cases_on `list_size expr_size args + cenv_defaults_size env < bound` >>
  gvs[rb_step_for_def, type_child_callback_def] >>
  metis_tac[rb_invalid_expr_call_for, rb_step_for_def]
QED

(* Negative probes: PtrVar and StackValue may contain labels; the invariant
   must reject the reserved label rather than assuming all inputs are plain. *)
Theorem rb_reserved_rejected:
  ~rb_operand_ok (Label "runtime_begin") /\
  ~rb_location_ok (PtrVar (Label "runtime_begin") n) /\
  ~rb_value_ok (StackValue ty (Label "runtime_begin")) /\
  ~rb_ptr_ok (mk_ptr (Label "runtime_begin") loc)
Proof
  simp[rb_operand_ok_def, rb_location_ok_def, rb_value_ok_def,
       rb_ptr_ok_def, mk_ptr_def]
QED

Theorem rb_env_ok_without_defaults_for:
  !ce name. (rb_env_ok_for source_checks) ce ==> (rb_env_ok_for source_checks) (cenv_without_defaults ce name)
Proof
  simp[cenv_without_defaults_def, rb_env_ok_for_def] >> metis_tac[]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem rb_step_return:
  Q x ==> rb_step Q (comp_return x)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_step_return_for))
QED

Theorem rb_step_bind:
  rb_step P m /\ (!x. P x ==> rb_step Q (f x)) ==>
  rb_step Q (comp_bind m f)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_step_bind_for))
QED

Theorem rb_operand_basic[simp]:
  rb_operand_ok (Var v) /\ rb_operand_ok (Lit n) /\
  (rb_operand_ok (Label l) <=> l <> "runtime_begin")
Proof
  simp[rb_operand_ok_def]
QED

Theorem rb_emit:
  EVERY rb_operand_ok inst.inst_operands ==> rb_step (K T) (emit inst)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_inst_ok_def,
     source_codecopy_arity_ok_def,
     rb_operand_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_for))
QED

Theorem rb_new_block:
  rb_step (K T) (new_block label)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_new_block_for))
QED

Theorem rb_fresh_label:
  rb_step (\l. rb_operand_ok (Label l)) (fresh_label suffix)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fresh_label_for))
QED

Theorem rb_fresh_var:
  rb_step (K T) fresh_var
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fresh_var_for))
QED

Theorem rb_fresh_id:
  rb_step (K T) fresh_id
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_fresh_id_for))
QED

Theorem rb_emit_inst:
  EVERY rb_operand_ok ops ==> rb_step (K T) (emit_inst opc ops outs)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_inst_for))
QED

Theorem rb_base_ptr:
  rb_buffer_ok b ==> rb_ptr_ok (base_ptr b)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_buffer_ok_legacy,
     rb_ptr_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_base_ptr_for))
QED

Theorem rb_mk_ptr:
  rb_operand_ok op ==> rb_ptr_ok (mk_ptr op loc)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_ptr_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_mk_ptr_for))
QED

Theorem rb_value_operand:
  rb_value_ok v ==> rb_operand_ok (vv_operand v)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_value_operand_for))
QED

Theorem rb_internal_fn_label:
  rb_operand_ok (Label (internal_fn_label id name tys ctor))
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_internal_fn_label_for))
QED

Theorem rb_emit_void:
  EVERY rb_operand_ok ops ==> rb_step (K T) (emit_void opc ops)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_void_for))
QED

Theorem rb_emit_op:
  EVERY rb_operand_ok ops ==> rb_step rb_operand_ok (emit_op opc ops)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_operand_ok_legacy,
     rb_step_legacy,
     source_codecopy_arity_ok_def, pairTheory.SND]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_emit_op_for))
QED

Theorem rb_step_weaken:
  rb_step P m /\ (!x. P x ==> Q x) ==> rb_step Q m
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_step_weaken_for))
QED

Theorem rb_step_ignore_bind:
  rb_step P m /\ rb_step Q n ==> rb_step Q (comp_ignore_bind m n)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_step_ignore_bind_for))
QED

Theorem rb_invalid_expr_call:
  rb_step rb_value_ok (invalid_expr_call ty)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_invalid_expr_call_for))
QED

Theorem rb_expr_child_callback:
  rb_expr_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (expr_child_callback bound cfn env ty e)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_expr_callback_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_expr_child_callback_for))
QED

Theorem rb_builtin_child_callback:
  rb_builtin_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (builtin_child_callback bound cfn env ret_ty ty bi args)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_builtin_callback_legacy,
     rb_env_ok_legacy,
     rb_step_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_builtin_child_callback_for))
QED

Theorem rb_type_child_callback:
  rb_type_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (type_child_callback bound cfn env vv_ty ty tb ret_ty args)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy,
     rb_step_legacy,
     rb_type_callback_legacy,
     rb_value_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_type_child_callback_for))
QED

Theorem rb_env_ok_without_defaults:
  !ce name. rb_env_ok ce ==> rb_env_ok (cenv_without_defaults ce name)
Proof
  ACCEPT_TAC (SIMP_RULE std_ss
    [rb_env_ok_legacy]
    (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`] rb_env_ok_without_defaults_for))
QED

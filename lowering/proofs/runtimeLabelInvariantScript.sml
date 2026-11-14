(* Weak proof-only operand exclusion interface for runtime lowering. *)
Theory runtimeLabelInvariant
Ancestors
  loweringShapeDefs moduleLowering compileEnv context exprLowering
  stmtLowering emitHelper venomInst list exprCallBounds

Definition rb_operand_ok_def:
  rb_operand_ok op <=> op <> Label "runtime_begin"
End

Definition rb_state_ok_def:
  rb_state_ok st <=>
    EVERY (\i. EVERY rb_operand_ok i.inst_operands) (state_insts st)
End

Definition rb_step_def:
  rb_step Q (action : 'a compiler) <=>
    !st. rb_state_ok st ==>
      let (v,st') = action st in rb_state_ok st' /\ Q v
End

Definition rb_buffer_ok_def:
  rb_buffer_ok buf <=> rb_operand_ok buf.buf_operand
End

Definition rb_ptr_ok_def:
  rb_ptr_ok p <=> rb_operand_ok p.ptr_operand /\
    (case p.ptr_buf of NONE => T | SOME b => rb_buffer_ok b)
End

Definition rb_value_ok_def:
  rb_value_ok (StackValue ty op) = rb_operand_ok op /\
  rb_value_ok (LocatedValue ty p) = rb_ptr_ok p
End

Definition rb_location_ok_def:
  rb_location_ok (PtrVar op n) = rb_operand_ok op /\
  rb_location_ok (MemLoc off n) = T /\
  rb_location_ok (StorageLoc slot) = T /\
  rb_location_ok (TransientLoc slot) = T /\
  rb_location_ok (ImmutableLoc off) = T
End

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

Definition rb_loop_ok_def:
  rb_loop_ok NoLoop = T /\
  rb_loop_ok (InLoop exit incr) =
    (rb_operand_ok (Label exit) /\ rb_operand_ok (Label incr))
End

Definition rb_expr_callback_def:
  rb_expr_callback bound cfn <=>
    !env ty e. expr_size e < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env ty e)
End

Definition rb_builtin_callback_def:
  rb_builtin_callback bound cfn <=>
    !env ret_ty ty bi args.
      list_size expr_size args < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env ret_ty ty bi args)
End

Definition rb_type_callback_def:
  rb_type_callback bound cfn <=>
    !env vv_ty ty tb ret_ty args.
      list_size expr_size args < bound /\ rb_env_ok env ==>
      rb_step rb_value_ok (cfn env vv_ty ty tb ret_ty args)
End

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

Definition rb_stmt_contract_def:
  rb_stmt_contract <=>
    (!env lctx ty s. rb_env_ok env /\ rb_loop_ok lctx ==>
      rb_step (K T) (compile_stmt env lctx ty s)) /\
    (!env lctx ty ss. rb_env_ok env /\ rb_loop_ok lctx ==>
      rb_step (K T) (compile_stmts env lctx ty ss))
End

Theorem rb_step_return:
  Q x ==> rb_step Q (comp_return x)
Proof
  simp[rb_step_def, comp_return_def]
QED

Theorem rb_step_bind:
  rb_step P m /\ (!x. P x ==> rb_step Q (f x)) ==>
  rb_step Q (comp_bind m f)
Proof
  rw[rb_step_def, comp_bind_def] >>
  Cases_on `m st` >> gvs[] >>
  first_x_assum drule >> simp[]
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
  simp[rb_step_def, rb_state_ok_def, emit_def,
       state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_new_block:
  rb_step (K T) (new_block label)
Proof
  simp[rb_step_def, rb_state_ok_def, new_block_def,
       state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_fresh_label:
  rb_step (\l. rb_operand_ok (Label l)) (fresh_label suffix)
Proof
  simp[rb_step_def, rb_state_ok_def, fresh_label_def,
       fresh_label_output_def, state_insts_def, all_blocks_def]
QED

Theorem rb_fresh_var:
  rb_step (K T) fresh_var
Proof
  simp[rb_step_def, rb_state_ok_def, fresh_var_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_fresh_id:
  rb_step (K T) fresh_id
Proof
  simp[rb_step_def, rb_state_ok_def, fresh_id_def,
       state_insts_def, all_blocks_def]
QED

Theorem rb_emit_inst:
  EVERY rb_operand_ok ops ==> rb_step (K T) (emit_inst opc ops outs)
Proof
  strip_tac >> rewrite_tac[emit_inst_def] >>
  irule rb_step_bind >> qexists_tac `K T` >>
  simp[rb_fresh_id, rb_emit, mk_inst_def]
QED

Theorem rb_base_ptr:
  rb_buffer_ok b ==> rb_ptr_ok (base_ptr b)
Proof
  simp[rb_buffer_ok_def, rb_ptr_ok_def, base_ptr_def]
QED

Theorem rb_mk_ptr:
  rb_operand_ok op ==> rb_ptr_ok (mk_ptr op loc)
Proof
  simp[rb_ptr_ok_def, mk_ptr_def]
QED

Theorem rb_value_operand:
  rb_value_ok v ==> rb_operand_ok (vv_operand v)
Proof
  Cases_on `v` >> simp[rb_value_ok_def, rb_ptr_ok_def, vv_operand_def]
QED

Theorem rb_internal_fn_label:
  rb_operand_ok (Label (internal_fn_label id name tys ctor))
Proof
  simp[internal_fn_label_def]
QED

(* Package predicates inspect only operand and branch-label sources. *)
Definition rb_external_package_ok_def:
  rb_external_package_ok
    (lbl,env,pos,min_cds,payable,nr,key,trans,view,body,ret) <=>
      rb_env_ok env /\ ~env.ce_is_ctor /\ rb_operand_ok (Label lbl)
End

Definition rb_internal_package_ok_def:
  rb_internal_package_ok
    (lbl,env,params,has_buf,nr,key,trans,view,ctor,imm_len,body,ret) <=>
      rb_env_ok env /\ ~env.ce_is_ctor /\ ~ctor /\ rb_operand_ok (Label lbl)
End

Definition rb_fallback_ok_def:
  rb_fallback_ok NONE = T /\
  rb_fallback_ok (SOME (env,payable,nr,key,trans,view,body,ret)) =
    (rb_env_ok env /\ ~env.ce_is_ctor)
End

Definition rb_runtime_inputs_ok_def:
  rb_runtime_inputs_ok selectors externals internals fallback <=>
    EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) selectors /\
    EVERY rb_external_package_ok externals /\
    EVERY rb_internal_package_ok internals /\ rb_fallback_ok fallback
End

Definition rb_group_ok_def:
  rb_group_ok (ExternalSingle (sel,lbl,tz) package) =
    (rb_operand_ok (Label lbl) /\ rb_external_package_ok package) /\
  rb_group_ok (ExternalDefaults common entries specs offset) =
    (rb_env_ok common.ec_env /\ ~common.ec_env.ce_is_ctor /\
     rb_operand_ok (Label common.ec_common_label) /\
     EVERY (\(sel,lbl,min_cds,k). rb_operand_ok (Label lbl)) entries)
End

Definition rb_grouped_runtime_inputs_ok_def:
  rb_grouped_runtime_inputs_ok groups internals fallback <=>
    EVERY rb_group_ok groups /\ EVERY rb_internal_package_ok internals /\
    rb_fallback_ok fallback
End

Theorem rb_emit_void:
  EVERY rb_operand_ok ops ==> rb_step (K T) (emit_void opc ops)
Proof
  strip_tac >> rewrite_tac[emit_void_def] >>
  irule rb_step_bind >> qexists_tac `K T` >>
  simp[rb_fresh_id, rb_emit, mk_inst_def]
QED

Theorem rb_emit_op:
  EVERY rb_operand_ok ops ==> rb_step rb_operand_ok (emit_op opc ops)
Proof
  simp[rb_step_def, rb_state_ok_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, mk_inst_def, state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_step_weaken:
  rb_step P m /\ (!x. P x ==> Q x) ==> rb_step Q m
Proof
  rw[rb_step_def] >> Cases_on `m st` >> gvs[] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem rb_step_ignore_bind:
  rb_step P m /\ rb_step Q n ==> rb_step Q (comp_ignore_bind m n)
Proof
  rewrite_tac[comp_ignore_bind_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `P` >> simp[]
QED

Theorem rb_invalid_expr_call:
  rb_step rb_value_ok (invalid_expr_call ty)
Proof
  simp[rb_step_def, rb_state_ok_def, invalid_expr_call_def,
       rb_value_ok_def, emit_inst_def, comp_bind_def, fresh_id_def,
       emit_def, mk_inst_def, state_insts_def, all_blocks_def, EVERY_APPEND]
QED

Theorem rb_expr_child_callback:
  rb_expr_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (expr_child_callback bound cfn env ty e)
Proof
  rw[rb_expr_callback_def] >>
  Cases_on `expr_size e < bound` >>
  gvs[rb_step_def, expr_child_callback_def] >>
  metis_tac[rb_invalid_expr_call, rb_step_def]
QED

Theorem rb_builtin_child_callback:
  rb_builtin_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (builtin_child_callback bound cfn env ret_ty ty bi args)
Proof
  rw[rb_builtin_callback_def] >>
  Cases_on `list_size expr_size args < bound` >>
  gvs[rb_step_def, builtin_child_callback_def] >>
  metis_tac[rb_invalid_expr_call, rb_step_def]
QED

Theorem rb_type_child_callback:
  rb_type_callback bound cfn /\ rb_env_ok env ==>
  rb_step rb_value_ok (type_child_callback bound cfn env vv_ty ty tb ret_ty args)
Proof
  rw[rb_type_callback_def] >>
  Cases_on `list_size expr_size args < bound` >>
  gvs[rb_step_def, type_child_callback_def] >>
  metis_tac[rb_invalid_expr_call, rb_step_def]
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

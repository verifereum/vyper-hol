(* Shared, state-independent projections: shape correctness additionally tracks
   allocation and opaque return PCs, which these symbolic-source facts do not
   need.  In particular, arbitrary PtrVar payloads are NOT assumed safe.
   Pointwise callback contracts below can be assumed only for the recursive
   calls supplied by an induction hypothesis, not for the current expression. *)
Theory runtimeSymSrcInterfaces
Ancestors
  runtimeSymSrcEmissionProbe loweringShapeDefs compileEnv context emitHelper
  list venomInst exprLowering stmtLowering supportedExprs supportedStmts
  supportedExprForms exprOracleStorageInterfaces
  supportedExprTraverse supportedStmtTraverse stackPlanTypes finite_map

Definition runtime_sym_inst_def:
  runtime_sym_inst i <=>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]) /\
    ~MEM (Label "code_end") i.inst_operands /\
    ~MEM (Label "runtime_begin") i.inst_operands
End

Definition runtime_sym_loc_def:
  runtime_sym_loc (PtrVar op sz) = ~is_label_operand op /\
  runtime_sym_loc (MemLoc off sz) = T /\
  runtime_sym_loc (StorageLoc slot) = T /\
  runtime_sym_loc (TransientLoc slot) = T /\
  runtime_sym_loc (ImmutableLoc off) = T
End

Definition runtime_sym_label_def:
  runtime_sym_label l <=> l <> "code_end" /\ l <> "runtime_begin"
End

Definition runtime_sym_env_def:
  runtime_sym_env ce <=>
    (!n loc. FLOOKUP ce.ce_vars n = SOME loc ==> runtime_sym_loc loc) /\
    (!n loc. FLOOKUP ce.ce_module_vars n = SOME loc ==> runtime_sym_loc loc) /\
    (!loc. ce.ce_return_buf = SOME loc ==> runtime_sym_loc loc) /\
    (!loc. ce.ce_return_pc = SOME loc ==> runtime_sym_loc loc) /\
    (!op. ce.ce_imm_alloca = SOME op ==> ~is_label_operand op) /\
    (!l. ce.ce_ctor_exit_label = SOME l ==> runtime_sym_label l)
End

Definition runtime_sym_value_def:
  runtime_sym_value (StackValue ty op) = ~is_label_operand op /\
  runtime_sym_value (LocatedValue ty p) =
    (~is_label_operand p.ptr_operand /\
     !b. p.ptr_buf = SOME b ==> ~is_label_operand b.buf_operand)
End

Definition runtime_sym_loop_def:
  runtime_sym_loop NoLoop = T /\
  runtime_sym_loop (InLoop b c) = (runtime_sym_label b /\ runtime_sym_label c)
End

(* Repeated higher-order hypotheses share these pointwise contracts.  Source
   traversal is part of each contract; it is not a condition on opcode shape. *)
Definition runtime_sym_expr_contract_def:
  runtime_sym_expr_contract tops cfn ce (ty : type) e <=>
    !s v s'. runtime_sym_env ce /\
      (supported_expr tops e \/ supported_place_expr tops e \/
       supported_effect_place_expr tops e) /\
      ~supported_expr_exists is_self_code e /\
      EVERY runtime_sym_inst (state_insts s) /\ cfn ce ty e s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_builtin_contract_def:
  runtime_sym_builtin_contract tops bfn ce ret_ty (ty : type) bi args <=>
    !s v s'. runtime_sym_env ce /\
      supported_expr tops (Builtin ret_ty bi args) /\
      ~supported_expr_exists is_self_code (Builtin ret_ty bi args) /\
      EVERY runtime_sym_inst (state_insts s) /\
      bfn ce ret_ty ty bi args s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_type_builtin_contract_def:
  runtime_sym_type_builtin_contract tops tfn ce vv_ty (ty : type) tb ret_ty args <=>
    !s v s'. runtime_sym_env ce /\
      supported_expr tops (TypeBuiltin vv_ty tb ret_ty args) /\
      ~supported_expr_exists is_self_code (TypeBuiltin vv_ty tb ret_ty args) /\
      EVERY runtime_sym_inst (state_insts s) /\
      tfn ce vv_ty ty tb ret_ty args s = (v,s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
End

Definition runtime_sym_stmt_contract_def:
  runtime_sym_stmt_contract tops bindings sfn ce lc (ty : type) stmt <=>
    !s s'. runtime_sym_env ce /\ runtime_sym_loop lc /\
      supported_stmt tops bindings stmt /\
      ~supported_stmt_expr_exists is_self_code stmt /\
      EVERY runtime_sym_inst (state_insts s) /\ sfn ce lc (ty : type) stmt s = ((),s') ==>
      EVERY runtime_sym_inst (state_insts s')
End

Definition runtime_sym_stmts_contract_def:
  runtime_sym_stmts_contract tops bindings sfn ce lc (ty : type) stmts <=>
    !s s'. runtime_sym_env ce /\ runtime_sym_loop lc /\
      supported_stmts tops bindings stmts /\
      ~supported_stmts_expr_exists is_self_code stmts /\
      EVERY runtime_sym_inst (state_insts s) /\ sfn ce lc (ty : type) stmts s = ((),s') ==>
      EVERY runtime_sym_inst (state_insts s')
End

Theorem runtime_sym_plain_operand:
  plain_operand st op ==> ~is_label_operand op
Proof
  simp[plain_operand_def]
QED

Theorem runtime_sym_nonlabel_reserved:
  ~is_label_operand op ==> op <> Label l
Proof
  Cases_on `op` >> simp[is_label_operand_def]
QED

Theorem runtime_sym_value_operand:
  runtime_sym_value v ==> ~is_label_operand (vv_operand v)
Proof
  Cases_on `v` >> simp[runtime_sym_value_def, vv_operand_def]
QED

Theorem runtime_sym_env_local:
  runtime_sym_env ce /\ FLOOKUP ce.ce_vars n = SOME loc ==>
  runtime_sym_loc loc
Proof
  simp[runtime_sym_env_def] >> metis_tac[]
QED

Theorem runtime_sym_env_module:
  runtime_sym_env ce /\ FLOOKUP ce.ce_module_vars n = SOME loc ==>
  runtime_sym_loc loc
Proof
  simp[runtime_sym_env_def] >> metis_tac[]
QED

Theorem runtime_sym_env_update:
  runtime_sym_env ce /\ runtime_sym_loc loc ==>
  runtime_sym_env (ce with ce_vars updated_by (\m. m |+ (n,loc)))
Proof
  rw[runtime_sym_env_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem runtime_sym_env_module_update:
  runtime_sym_env ce /\ runtime_sym_loc loc ==>
  runtime_sym_env (ce with ce_module_vars updated_by (\m. m |+ (n,loc)))
Proof
  rw[runtime_sym_env_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem runtime_sym_ordinary_inst:
  opc <> CODESIZE /\ opc <> CODECOPY /\ EVERY (\op. ~is_label_operand op) ops ==>
  runtime_sym_inst (mk_inst id opc ops outs)
Proof
  simp[runtime_sym_inst_def, mk_inst_def, EVERY_MEM] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_ordinary_emit:
  opc <> CODESIZE /\ opc <> CODECOPY /\ EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts (SND (emit (mk_inst id opc ops outs) s)))
Proof
  simp[runtime_sym_emit] >> metis_tac[runtime_sym_ordinary_inst]
QED

Theorem runtime_sym_compile_name:
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_name_vv ce ty n s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `FLOOKUP ce.ce_vars n`
  >- (strip_tac >> gvs[compile_name_vv_def, comp_return_def, comp_ignore_bind_def,
          comp_bind_def, emit_inst_def, fresh_id_def, emit_def,
          runtime_sym_value_def, is_label_operand_def,
          state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
          EVERY_APPEND, runtime_sym_inst_def, mk_inst_def]) >>
  Cases_on `x` >> simp[compile_name_vv_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[comp_return_def, runtime_sym_value_def, mk_ptr_def,
      is_label_operand_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
      emit_def, state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def] >>
  drule_all runtime_sym_env_local >> simp[runtime_sym_loc_def]
QED

Theorem runtime_sym_unwrap_stack:
  runtime_sym_value (StackValue ty op) /\
  EVERY runtime_sym_inst (state_insts s) /\
  unwrap_value ce (StackValue ty op) s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  simp[unwrap_value_def, comp_return_def, runtime_sym_value_def] >>
  rpt strip_tac >> gvs[]
QED

(* Whitelist decomposition, rather than extra constraints on the frozen
   theorem, supplies the source domain for recursive callback applications. *)
Theorem runtime_sym_builtin_domain:
  supported_expr tops (Builtin ty bi args) <=>
  supported_builtin_form tops ty bi args /\ EVERY (supported_pure_expr tops) args
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       supported_pure_exprs_every]
QED

Theorem runtime_sym_type_builtin_domain:
  supported_expr tops (TypeBuiltin ty tb rt args) <=>
  supported_type_builtin_form tops ty tb rt args /\
  EVERY (supported_pure_expr tops) args
Proof
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       supported_pure_exprs_every]
QED

Theorem runtime_sym_argument_guards:
  ~supported_exprs_exists p args /\
  ~supported_exprs_exists q args /\ MEM e args ==>
  ~supported_expr_exists p e /\ ~supported_expr_exists q e
Proof
  simp[supported_exprs_exists_not_every, EVERY_MEM] >> metis_tac[]
QED

(* A paired exclusion boundary avoids copying the same traversal proof for
   self-code exclusion and arity/shape exclusion in each recursive consumer. *)
Theorem runtime_sym_argument_el_guards:
  ~supported_exprs_exists p args /\
  ~supported_exprs_exists q args /\ n < LENGTH args ==>
  ~supported_expr_exists p (EL n args) /\
  ~supported_expr_exists q (EL n args)
Proof
  metis_tac[runtime_sym_argument_guards, MEM_EL]
QED

Theorem runtime_sym_supported_argument:
  EVERY (supported_pure_expr tops) args /\ MEM e args ==>
  supported_expr tops e
Proof
  simp[EVERY_MEM, supported_expr_def] >> metis_tac[]
QED

Theorem runtime_sym_bop_selections:
  supported_expr tops (Builtin ty (Bop op) args) ==>
  LENGTH args = 2 /\ MEM (HD args) args /\ MEM (EL 1 args) args /\
  supported_expr tops (HD args) /\ supported_expr tops (EL 1 args)
Proof
  namedCases_on `args` ["", "a rest"] >>
  simp[runtime_sym_builtin_domain, supported_builtin_form_def] >>
  namedCases_on `rest` ["", "b tail"] >>
  simp[runtime_sym_builtin_domain, supported_builtin_form_def] >>
  Cases_on `tail` >>
  simp[runtime_sym_builtin_domain, supported_builtin_form_def, supported_expr_def]
QED

Theorem runtime_sym_convert_selection:
  supported_expr tops (TypeBuiltin ty Convert rt args) ==>
  LENGTH args = 1 /\ MEM (HD args) args /\ supported_expr tops (HD args)
Proof
  namedCases_on `args` ["", "a rest"] >>
  simp[runtime_sym_type_builtin_domain, supported_type_builtin_form_def] >>
  Cases_on `rest` >>
  simp[runtime_sym_type_builtin_domain, supported_type_builtin_form_def,
       supported_expr_def]
QED

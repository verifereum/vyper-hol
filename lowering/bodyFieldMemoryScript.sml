(* Contained field capacity for actual memory projections. *)
Theory bodyFieldMemory
Ancestors
  loweringPosts
  bodyFieldMemoryProps bodyFieldValueMemory bodyFieldForceMemory
  exprSimAttributeProps exprSimFieldLayout exprSimProps exprSimVVFrame
  bodyNameValueMemory
  bodyNameMemoryFacts
  exprSimSource
  exprSimAttributeFields bodyAllocMemory
  valueEncoding compileEnv venomState words list rich_list finite_map
  exprSimAttribute exprSimHash exprSimLiteralBuffer exprOperandVar
  exprSimBuffer exprSimAggregateChildren exprSimDefs context
  exprLowering exprLoweringProps emitHelper emitHelperProps fragExec fragExecMem instMemFrontier
  allocaHistoryFragment venomInst vyperAST vyperTyping vyperInterpreter
  exprSimHyps vyperTypeSystem vyperTypeInvariants allocLimits
  bodyMemoryDefs exprSimUnwrap vyperState exprSimLen vyperTypeExprSoundness

Theorem compile_attribute_name_body_capacity_mem:
  expr_body_pre cenv cx env (Attribute ann (Name (StructT sid) id) fld) es /\
  compile_expr cenv ty (Attribute ann (Name (StructT sid) id) fld) sa = (vv,sb) /\
  eval_expr cx (Attribute ann (Name (StructT sid) id) fld) es = (res,es') /\
  expr_vv_res_ok res /\
  res <> INR (Error (RuntimeError "convert empty bytes to signed")) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec_mem ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s)
    (\s. (?tv. res = INL tv /\
               vv_post ctx func cenv cx (Attribute ann (Name (StructT sid) id) fld)
                 es sa sb s0 es' tv vv s) /\
         vv_loc vv = LocMemory /\
         (?ftv w. evaluate_type (get_tenv cx) ann = SOME ftv /\
                  eval_operand (vv_operand vv) s = SOME w /\
                  w2n w + type_memory_size ftv <= s.vs_alloca_next) /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  cheat
QED


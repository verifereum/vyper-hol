Theory bodyPtrPopGlobalFields
Ancestors
  bodyPtrPopGlobalInternal bodyPtrPopGlobalLoweringInputs
  bodyPtrPopStructLegality bodyPtrPopDynAssignProbe compileEnv finite_map vyperValue

Theorem pop_global_body_return_pc:
  pop_global_body_env.ce_return_pc = SOME (PtrVar (Var "%5") 0)
Proof
  EVAL_TAC
QED

Theorem pop_global_body_return_buf:
  pop_global_body_env.ce_return_buf = NONE
Proof
  EVAL_TAC
QED

Theorem pop_global_body_return_count:
  pop_global_body_env.ce_returns_count = 1
Proof
  EVAL_TAC
QED

Theorem pop_global_body_nonreentrant:
  pop_global_body_env.ce_nonreentrant = (F,0,F,F)
Proof
  EVAL_TAC
QED

Theorem pop_global_body_raw_return:
  pop_global_body_env.ce_raw_return = F
Proof
  EVAL_TAC
QED

Theorem pop_global_body_imm_alloca:
  pop_global_body_env.ce_imm_alloca = NONE
Proof
  EVAL_TAC
QED

Theorem pop_global_body_alloca_locals:
  pop_global_body_env.ce_alloca_locals = T
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_A:
  FLOOKUP pop_global_body_env.ce_module_vars (NONE,"A") = SOME (StorageLoc 0w)
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_B:
  FLOOKUP pop_global_body_env.ce_module_vars (NONE,"B") = SOME (StorageLoc 4w)
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_A_type:
  pop_global_body_env.ce_module_var_type (NONE,"A") = SOME pop_struct_ty
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_B_type:
  pop_global_body_env.ce_module_var_type (NONE,"B") = SOME pop_struct_ty
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_A_hashmap:
  pop_global_body_env.ce_hashmap_info (NONE,"A") = NONE
Proof
  EVAL_TAC
QED

Theorem pop_global_body_global_B_hashmap:
  pop_global_body_env.ce_hashmap_info (NONE,"B") = NONE
Proof
  EVAL_TAC
QED

Theorem pop_global_body_struct_fields:
  get_struct_fields pop_global_body_env.ce_struct_fields "Box" =
    [("a",pop_dyn_assign_ty,128)]
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_global_body_struct_bytes:
  type_memory_bytes pop_global_body_env pop_struct_ty = 128
Proof
  EVAL_TAC
QED


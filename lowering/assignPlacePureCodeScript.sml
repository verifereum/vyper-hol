Theory assignPlacePureCode
Ancestors
  assignPlacePureFacts stmtSimAssignMem stmtSimProps stmtLowering exprLowering compileEnv

Theorem assign_place_pure_code_parts:
  stmt_env ce lctx ty (Assign (BaseTarget bt) e) sa = (ce',sf) /\
  ~expr_can_mutate ce (target_to_expr bt) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  ce' = ce /\
  ?vv sm tr st op su.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    compile_get_target_ptr compile_expr ce bt sm = (tr,st) /\
    unwrap_value ce vv st = (op,su) /\
    (case FST (SND tr) of
       SOME loc => compile_assign_value ce (FST tr) loc op
         (is_word_type (case SND (SND tr) of SOME (ValPT t) => t | _ => lowered_value_type ce e))
         (vv_location vv)
         (case SND (SND tr) of SOME (ValPT t) => t | _ => lowered_value_type ce e)
         (lowered_value_type ce e)
         (case (case SND (SND tr) of SOME (ValPT t) => t | _ => lowered_value_type ce e) of
            ArrayT et (Dynamic _) =>
              SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
          | _ => NONE)
         (type_memory_bytes ce (case SND (SND tr) of SOME (ValPT t) => t | _ => lowered_value_type ce e))
     | NONE => emit_void INVALID []) su = ((),sf)
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  Cases_on `compile_get_target_ptr compile_expr ce bt sm` >>
  rename1 `compile_get_target_ptr _ _ _ _ = (tr,st)` >>
  Cases_on `unwrap_value ce vv st` >>
  simp[]
QED

Theorem assign_place_pure_empty_code:
  stmt_env ce lctx ty (Assign (BaseTarget bt) e) sa = (ce',sf) /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  ce' = ce /\
  ?tr st. compile_get_target_ptr compile_expr ce bt sa = (tr,st) /\
    compile_store_at_loc ce.ce_imm_alloca (FST tr) (Lit 0w) (FST (SND tr)) st = ((),sf)
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_get_target_ptr compile_expr ce bt sa` >> simp[]
QED

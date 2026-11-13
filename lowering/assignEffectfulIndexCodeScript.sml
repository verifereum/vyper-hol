(* Assignment compiler boundaries.  In particular, the RHS representation is
   lowered_value_type, not necessarily the source annotation. *)
Theory assignEffectfulIndexCode
Ancestors
  stmtLowering exprLowering compileEnv

Theorem assign_effectful_empty_code:
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  (compile_stmt ce lctx ty (Assign (BaseTarget bt) e) sa = ((),sb) <=>
   ?r st.
     compile_get_target_ptr compile_expr ce bt sa = (r,st) /\
     compile_store_at_loc ce.ce_imm_alloca (FST r) (Lit 0w)
       (FST (SND r)) st = ((),sb))
Proof
  strip_tac >>
  simp[Once compile_stmt_def, comp_bind_def] >>
  Cases_on `compile_get_target_ptr compile_expr ce bt sa` >> simp[]
QED

Theorem assign_effectful_value_code:
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  (compile_stmt ce lctx ty (Assign (BaseTarget bt) e) sa = ((),sb) <=>
   ?vv0 sr vv ss r st op su.
     compile_expr ce (expr_type e) e sa = (vv0,sr) /\
     ((expr_can_mutate ce (target_to_expr bt) /\
       compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) vv0)
         sr = (vv,ss)) \/
      (~expr_can_mutate ce (target_to_expr bt) /\ vv = vv0 /\ ss = sr)) /\
     compile_get_target_ptr compile_expr ce bt ss = (r,st) /\
     unwrap_value ce vv st = (op,su) /\
     (let dty = case SND (SND r) of SOME (ValPT t) => t
                                   | _ => lowered_value_type ce e in
      case FST (SND r) of
        SOME loc =>
          compile_assign_value ce (FST r) loc op (is_word_type dty)
            (vv_location vv) dty (lowered_value_type ce e)
            (case dty of ArrayT et (Dynamic _) =>
               SOME ((type_memory_bytes ce et + 31) DIV 32,
                     type_memory_bytes ce et)
             | _ => NONE)
            (type_memory_bytes ce dty) su = ((),sb)
      | NONE => emit_void INVALID [] su = ((),sb)))
Proof
  strip_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv0,sr)` >>
  Cases_on `expr_can_mutate ce (target_to_expr bt)`
  >- (Cases_on `compile_snapshot_vv ce T
         (vv_with_type (lowered_value_type ce e) vv0) sr` >>
      rename1 `compile_snapshot_vv _ _ _ _ = (vv,ss)` >> simp[] >>
      Cases_on `compile_get_target_ptr compile_expr ce bt ss` >>
      rename1 `compile_get_target_ptr _ _ _ _ = (tr,st)` >> simp[] >>
      Cases_on `unwrap_value ce vv st` >> simp[] >>
      Cases_on `FST (SND tr)` >> simp[]) >>
  simp[comp_return_def] >>
  Cases_on `compile_get_target_ptr compile_expr ce bt sr` >>
  rename1 `compile_get_target_ptr _ _ _ _ = (tr,st)` >> simp[] >>
  Cases_on `unwrap_value ce vv0 st` >> simp[] >>
  Cases_on `FST (SND tr)` >> simp[]
QED

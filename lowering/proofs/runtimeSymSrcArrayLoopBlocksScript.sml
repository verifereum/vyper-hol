Theory runtimeSymSrcArrayLoopBlocks
Ancestors
  runtimeSymSrcArrayIterator runtimeSymSrcInterfaces runtimeSymSrcEmission
  supportedStmts supportedExprs supportedExprTraverse exprLowering vyperAST
  runtimeSymSrcContext runtimeSymSrcContextTypedArrays runtimeSymSrcContextCopy compileEnv
  context venomInst stackPlanTypes list emitHelper loweringShapeDefs

Theorem runtime_sym_array_iterator_eval:
  runtime_sym_env ce /\ supported_iterator tops fty (Array e) n /\
  ~supported_expr_exists is_self_code e /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type e) e /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_expr ce (expr_type e) e s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `e` >> strip_tac
  >~ [`compile_expr _ _ (Name _ _) _ = _`] >-
     (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[Once compile_expr_def, compile_expr_body_def] >>
      strip_tac >> drule_all runtime_sym_compile_name >> simp[])
  >~ [`compile_expr _ _ (TopLevelName _ _) _ = _`] >-
     (drule_all runtime_sym_toplevel_name_eval >> simp[]) >>
  qpat_x_assum `supported_iterator _ _ _ _` mp_tac >>
  simp[Once supported_iterator_def] >> strip_tac >>
  fs[runtime_sym_expr_contract_def] >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_array_capacity:
  ~is_label_operand len /\ EVERY runtime_sym_inst (state_insts s) /\
  (if dyn then
     do invalid <- emit_op GT [len; Lit (n2w capacity)];
        valid <- emit_op ISZERO [invalid];
        emit_void ASSERT [valid] od
   else return ()) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `dyn` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      qpat_x_assum `emit_op GT _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      qpat_x_assum `emit_op ISZERO _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem runtime_sym_array_entry:
  runtime_sym_label entry /\ runtime_sym_label cond /\
  ~is_label_operand len /\ EVERY runtime_sym_inst (state_insts s) /\
  emit_inst JMP [Label entry] [] s = (u1,s1) /\
  new_block entry s1 = (u2,s2) /\ fresh_var s2 = (idx,s3) /\
  emit_inst ASSIGN [Lit 0w] [idx] s3 = (u3,s4) /\
  (if dyn then
     do invalid <- emit_op GT [len; Lit (n2w capacity)];
        valid <- emit_op ISZERO [invalid];
        emit_void ASSERT [valid] od
   else return ()) s4 = (u4,s5) /\
  emit_inst JMP [Label cond] [] s5 = (u5,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  qpat_x_assum `emit_inst JMP [Label entry] _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[] >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> strip_tac >>
  drule runtime_sym_fresh_var >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_assign) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_array_capacity >> strip_tac >>
  drule_all runtime_sym_jump >> simp[]
QED

Theorem runtime_sym_array_offset:
  ~is_label_operand idx_offset /\ EVERY runtime_sym_inst (state_insts s) /\
  (if 0 < offset then emit_op ADD [Lit (n2w offset); idx_offset]
   else return idx_offset) s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `0 < offset` >> simp[comp_return_def]
  >- (strip_tac >> drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[is_label_operand_def]) >>
  strip_tac >> gvs[]
QED

Theorem runtime_sym_array_address:
  emit_op ADD [arr; total_offset] s6 = (elem_op,s') ==>
  (if 0 < offset then emit_op ADD [Lit (n2w offset); idx_offset]
   else return idx_offset) s5 = (total_offset,s6) ==>
  emit_op MUL [Var idx; Lit (n2w sz)] s4 = (idx_offset,s5) ==>
  new_block body_lbl s3 = (u3,s4) ==>
  emit_inst JNZ [done_op; Label exit; Label body_lbl] [] s2 = (u2,s3) ==>
  emit_op EQ [Var idx; len] s1 = (done_op,s2) ==>
  new_block cond s = (u1,s1) ==>
  runtime_sym_label exit /\ runtime_sym_label body_lbl /\
  ~is_label_operand len /\ ~is_label_operand arr /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand elem_op
Proof
  rpt disch_tac >> fs[] >>
  qpat_x_assum `new_block cond _ = _`
    (mp_then Any mp_tac runtime_sym_copy_new_block) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op EQ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_jnz >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> strip_tac >>
  qpat_x_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_array_offset >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_array_tail:
  runtime_sym_label incr /\ runtime_sym_label cond /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_jmp_if_not_terminated incr s = (u1,s1) /\
  new_block incr s1 = (u2,s2) /\
  emit_op ADD [Var idx; Lit 1w] s2 = (new_idx,s3) /\
  emit_inst ASSIGN [new_idx] [idx] s3 = (u3,s4) /\
  emit_inst JMP [Label cond] [] s4 = (u4,s5) /\
  new_block exit s5 = (u5,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  drule_all runtime_sym_jmp_if_not_terminated >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> strip_tac >>
  drule_all runtime_sym_typed_array_tail >> simp[]
QED

Theorem runtime_sym_array_copy:
  (!src dst sz loc slots dt st s u s'.
    runtime_sym_env ce /\ ~is_label_operand src /\ ~is_label_operand dst /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_iter_elem_copy ce src dst sz loc slots dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_env ce /\ runtime_sym_env body_ce /\
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  (case FLOOKUP body_ce.ce_vars id of
     SOME (MemLoc off _) =>
       compile_iter_elem_copy ce src (Lit (n2w off)) sz loc slots dt st
   | SOME (PtrVar ptr_op _) =>
       compile_iter_elem_copy ce src ptr_op sz loc slots dt st
   | _ => emit_void INVALID []) s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> strip_tac >>
  Cases_on `FLOOKUP body_ce.ce_vars id` >> gvs[]
  >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  drule_all runtime_sym_env_local >> strip_tac >>
  Cases_on `x` >> gvs[runtime_sym_loc_def]
  >>~- ([`emit_void INVALID [] _ = _`],
         drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  first_x_assum (drule_at (Pat `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_array_length:
  runtime_sym_env ce /\ ~is_label_operand arr /\
  EVERY runtime_sym_inst (state_insts s) /\
  (if dyn then compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc arr
   else return (Lit (n2w capacity))) s = (len,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand len
Proof
  Cases_on `dyn` >> simp[comp_return_def]
  >- (strip_tac >> drule_at (Pat `compile_ptr_load _ _ _ _ _ = _`)
        runtime_sym_ptr_load >> fs[runtime_sym_env_def]) >>
  strip_tac >> gvs[is_label_operand_def]
QED

(* Resource-bearing declaration setup, using public compiler interfaces. *)
Theory bodyIntCallFamStmtMutationAnn
Ancestors
  bodyIntCallFamStmtMutationEntry bodyIntCallJointContract
  stmtSimDeclMem loweringSlice bodyPtrCallCalldata fragExec
  stmtSimProps bodySim compileEnv exprLoweringProps bodyDeclCopyMemory

Theorem intcall_annassign_word_entry:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa s /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  supported_expr fp.jc_tops e /\ stmt_exprs_ok ce (AnnAssign id ty e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id ty e) ==> occurs_abi_decode_target target fp.jc_tops) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  stmt_env ce lctx cty (AnnAssign id ty e) sa = (c,sf) /\
  is_word_type ty /\ ~has_length_word ty /\
  fn_has_code sa sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?st sA sB op p t w.
    declare_local ce id ty sa = (c,st) /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
    lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
    emit_void MSTORE [Var p;op] sB = ((),sf) /\
    fn_has_code sA sB fp.jc_func /\ fn_has_code sB sf fp.jc_func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
        (fn_insts fp.jc_func) /\
    expr_body_pre c fp.jc_cx env e es /\ body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_res fp c env es sA t /\
    ~t.vs_halted /\ t.vs_current_bb = sA.cs_current_bb /\
    t.vs_inst_idx = LENGTH sA.cs_current_insts /\
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (w2n w,w2n (n2w (type_memory_bytes ce ty) : bytes32)) /\
    fp.jc_lo <= w2n w /\ t.vs_memory = s.vs_memory /\
    (!op. op <> Var p ==> eval_operand op t = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all intcall_pending_declaration_pre >> strip_tac >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved c st` by fs[intcall_expr_res_def] >>
  `cs_extends sa st` by fs[cs_extends_def] >>
  `fn_has_code st sf fp.jc_func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `!a b op. lower_value compile_expr c (expr_type e) e a = (op,b) ==>
            cs_extends a b` by
    (rpt strip_tac >> drule lower_value_compile_expr_split >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  drule_all compile_annassign_word_parts >> strip_tac >>
  rename1 `lower_value compile_expr c (expr_type e) e sA = (op,sB)` >>
  `fn_has_code sa sA fp.jc_func /\ fn_has_code sB sf fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `id NOTIN FDOM env.var_types` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  drule_all (Q.INST [`p` |-> `STRING #"%" (toString sa.cs_next_var)`]
    intcall_declaration_alloca_prefix |> SRULE []) >> strip_tac >>
  qexistsl [`st`, `sA`, `sB`, `op`,
    `STRING #"%" (toString sa.cs_next_var)`, `t`, `w`] >> simp[]
QED

Theorem intcall_annassign_copy_entry:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa s /\
  type_stmt env ret (AnnAssign id ty e) = SOME env' /\
  supported_expr fp.jc_tops e /\ stmt_exprs_ok ce (AnnAssign id ty e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id ty e) ==> occurs_abi_decode_target target fp.jc_tops) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  stmt_env ce lctx cty (AnnAssign id ty e) sa = (c,sf) /\
  ~is_word_type ty /\ ~(has_length_word ty /\ is_empty_value_expr e) /\
  fn_has_code sa sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?st sA sV sB vv op p t w.
    declare_local ce id ty sa = (c,st) /\
    p = STRING #"%" (toString sa.cs_next_var) /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
    emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
    compile_expr c (expr_type e) e sA = (vv,sV) /\
    unwrap_value c vv sV = (op,sB) /\
    lower_value compile_expr c (expr_type e) e sA = (op,sB) /\
    compile_assign_value c (Var p) LocMemory op F (vv_location vv)
      ty (lowered_value_type ce e)
      (case ty of ArrayT elem_ty (Dynamic _) =>
         SOME ((type_memory_bytes ce elem_ty + 31) DIV 32,
               type_memory_bytes ce elem_ty) | _ => NONE)
      (type_memory_bytes ce ty) sB = ((),sf) /\
    fn_has_code sA sB fp.jc_func /\ fn_has_code sB sf fp.jc_func /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p])
        (fn_insts fp.jc_func) /\
    expr_body_pre c fp.jc_cx env e es /\ body_inv fp.jc_tops fp.jc_ctx c fp.jc_cx /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_res fp c env es sA t /\
    ~t.vs_halted /\ t.vs_current_bb = sA.cs_current_bb /\
    t.vs_inst_idx = LENGTH sA.cs_current_insts /\
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (w2n w,w2n (n2w (type_memory_bytes ce ty) : bytes32)) /\
    fp.jc_lo <= w2n w /\ t.vs_memory = s.vs_memory /\
    (!op. op <> Var p ==> eval_operand op t = eval_operand op s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  drule_all intcall_pending_declaration_pre >> strip_tac >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  `local_ptrs_reserved c st` by fs[intcall_expr_res_def] >>
  `cs_extends sa st` by fs[cs_extends_def] >>
  `fn_has_code st sf fp.jc_func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  drule_all annassign_copy_parts_mem >> strip_tac >>
  rename1 `lower_value compile_expr c (expr_type e) e sA = (op,sB)` >>
  `cs_extends sA sB` by
    (drule lower_value_compile_expr_split >> strip_tac >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends sB sf` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[stmtLoweringTheory.compile_assign_value_def] >>
     Cases_on `vv_location vv = SOME LocMemory` >>
     simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     metis_tac[ci_mono_compile_alloc_buffer, ci_mono_compile_copy_memory,
       ci_mono_compile_store_memory, ci_mono_def, pairTheory.SND,
       cs_extends_trans]) >>
  `cs_extends st sA` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code sa sA fp.jc_func /\ fn_has_code sA sB fp.jc_func /\
   fn_has_code sB sf fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `id NOTIN FDOM env.var_types` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  drule_all (Q.INST [`p` |-> `STRING #"%" (toString sa.cs_next_var)`]
    intcall_declaration_alloca_prefix |> SRULE []) >> strip_tac >>
  `fn_has_code st sA fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all loweringHaltTheory.emit_inst_fn_member >> strip_tac >>
  qexistsl [`st`, `sA`, `sV`, `sB`, `vv`, `op`,
    `STRING #"%" (toString sa.cs_next_var)`, `t`, `w`] >> gvs[]
QED

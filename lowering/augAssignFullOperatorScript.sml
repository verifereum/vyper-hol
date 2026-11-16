(* Numeric correctness and scalar certificates meet at one joint endpoint. *)
Theory augAssignFullOperator
Ancestors
  augAssignFullScalarFresh augAssignFullScalarAbort augAssignPtrScalarCertificate
  exprBopStraight freshWrites varsExt exprLoweringProps
  fragGasOriginPtr ptrDiscipline codegenRel compileEnv
  venomExecSemantics venomState list pred_set

Theorem binop_numeric_origin_ptr_continuation:
  ((?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 v1) /\
         eval_operand y ss = SOME (val_to_w256 v2) ==>
         ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
               eval_operand op ss' = SOME (val_to_w256 v)) \/
   (?msg. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError msg)) /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 v1) /\
         eval_operand y ss = SOME (val_to_w256 v2) ==>
         ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')) /\
  straight_fresh (compile_binop bop x y ty bl el) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!z. z IN A ==> op_prov G (Var z) = NONE /\ op_taint tn (Var z) = {}) /\
  ~ctx_has_dalloca ctx /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                               (emitted_insts sa sb)))) op ==>
  (?v t G' tn'.
    bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v) /\
    t = s with vs_vars := t.vs_vars /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
    (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
       op_taint tn' (Var z) = op_taint tn (Var z)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    op_prov G' op = NONE /\ op_taint tn' op = {}) \/
  (?msg t j G' tn'.
    bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError msg)) /\
    (!D lo. allocas_from lo s /\ lo <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort (t with vs_inst_idx := j),G',tn')))
Proof
  strip_tac
  >- (disj1_tac >>
      `eval_operand x (drop_fresh sa s) = SOME (val_to_w256 v1) /\
       eval_operand y (drop_fresh sa s) = SOME (val_to_w256 v2)` by
        simp[eval_operand_drop_fresh] >>
      qpat_x_assum `!x y sa sb op ss. _`
        (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
      simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK t0` >>
      drule_all straight_fresh_scalar_origin_ptr_success >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
      `eval_operand op t = SOME (val_to_w256 v)` by
        (fs[vars_ext_def] >>
         qpat_x_assum `t = t0 with vs_vars := _` SUBST1_TAC >>
         simp[eval_operand_vars_ext]) >>
      qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]) >>
  disj2_tac >>
  `eval_operand x (drop_fresh sa s) = SOME (val_to_w256 v1) /\
   eval_operand y (drop_fresh sa s) = SOME (val_to_w256 v2)` by
    simp[eval_operand_drop_fresh] >>
  qpat_x_assum `!x y sa sb op ss. _`
    (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all straight_fresh_scalar_origin_ptr_abort >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t`, `j`, `G'`, `tn'`] >> simp[]
QED

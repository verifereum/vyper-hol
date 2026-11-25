Theory entryCreateBopBytestringFold
Ancestors
  entryCreateCompositeFocus entryCreateFocusSpec exprSimLiteralWord
  exprSimWordArgs exprLowering loweringPosts bodyPtrDefs ptrDiscipline
  vyperValueOperation venomState

(* A folded digest owns no machine instruction, even if the instruction at
   its start cursor belongs to a CREATE in the continuation. *)
Theorem bop_bytestring_folded_child_site:
  bytestring_literal_hash e = SOME digest /\
  create_operand_at sa s /\ alloca_history func s /\ ~s.vs_halted /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sa
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee HG un t. ?v contents. res = INL v /\
      (v = BytesV contents \/
       ?str. v = StringV str /\ contents = MAP (n2w o ORD) str) /\
      eval_operand (Lit digest) t = SOME (word_of_bytes_be (Keccak_256_w64 contents)) /\
      op_prov HG (Lit digest) = NONE /\ op_taint un (Lit digest) = {} /\
      (!z. Lit digest = Var z ==> not_fresh_at sa z) /\ (!l. Lit digest <> Label l) /\
      stmt_state_rel H ctx func cenv cx ee t /\
      ghost_inv_at (DF H) lo d cenv cx ee HG un t /\ ~t.vs_halted /\
      t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = LENGTH sa.cs_current_insts /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s HG un /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s t))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sa E ctx func (cx_tops cx) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s)
Proof
  strip_tac >> reverse conj_tac
  >- (rw[create_operand_cut_def] >> metis_tac[create_operand_empty_scope]) >>
  Cases_on `e` >> fs[bytestring_literal_hash_def] >>
  rename1 `Literal ann lit` >>
  irule scoped_operand_pure >> simp[] >>
  qexistsl_tac [`es`, `INL (evaluate_literal lit)`] >>
  simp[literal_read_all_tails] >> gen_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  `ghost_inv_at (DF H) lo d cenv cx (es with gas_obs := []) G tn s` by
    (fs[ghost_inv_at_def] >> first_assum ACCEPT_TAC) >>
  fs[create_operand_at_def] >>
  Cases_on `lit` >>
  gvs[bytestring_literal_hash_def, evaluate_literal_def,
      eval_operand_def, op_prov_def, op_taint_def, wb_frame_refl,
      ghost_kept_at_def]
QED

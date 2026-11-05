(* Counted copy boundaries; fixed-run toolkit facts are used only for
   instruction safety and ghost updates, never to manufacture paths. *)
Theory annAssignPtrCopy
Ancestors
  annAssignPtrSetup typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline venomInst venomInstProofs
  venomExecSemantics venomState venomMemDefs venomMemProofs
  context emitHelper emitHelperProps finite_map pred_set arithmetic
  compileEnv

Theorem annassign_mcopy_path_ptr:
 !D ctx func PG G tn s bb id dst src count_op a b n.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx =
   SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
 ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) ==>
 gas_path_ptr D 0 ctx func PG G tn s 0 G
   (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
     (mcopy (w2n b) (w2n a) (w2n n) s) tn)
   (OK ((mcopy (w2n b) (w2n a) (w2n n) s) with
     vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
   (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
    simp[mk_inst_def, eval_operand_def]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s))
   (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
     (mcopy (w2n b) (w2n a) (w2n n) s) tn)
   (OK ((mcopy (w2n b) (w2n a) (w2n n) s) with
     vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_mcopy_operand >> simp[]) >>
 gvs[mcopy_operand_ghost_frame, eval_operand_def] >>
 drule (cj 2 gas_path_ptr_rules) >>
 simp[mcopy_def, write_memory_with_expansion_def] >>
 disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
 simp[mcopy_def, write_memory_with_expansion_def]
QED


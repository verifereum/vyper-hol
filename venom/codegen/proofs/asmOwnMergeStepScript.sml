(* Single-step label-renaming simulation with fixed own-code bytes. *)
Theory asmOwnMergeStep
Ancestors
  asmOptMergeJumpdests asmSymPcOwn asmSymOwnCode asmSymSem asmSem
  asmOptimizer list rich_list

Theorem rename_step_own_under:
  (∀ss ss'. rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
     res_rel x y (sym_codecopy_own p env own ss)
                 (sym_codecopy_own p env own ss')) ⇒
  ∀ss ss' inst.
  rn_rel x y ss ss' ∧ ¬sym_data_label p env x ⇒
  case sym_step_own p env own inst ss of
    SymOK t =>
      (∃t'. sym_step_own (MAP (rename_push_label x y) p) env own
              (rename_push_label x y inst) ss' = SymOK t' ∧
            rn_rel x y t t') ∨
      (INDEX_OF (AsmLabel x) p = SOME t.sym_base.as_pc ∧
       ∀j. INDEX_OF (AsmLabel y) p = SOME j ⇒
         ∃t'. sym_step_own (MAP (rename_push_label x y) p) env own
                (rename_push_label x y inst) ss' = SymOK t' ∧
              rn_rel x y (t with sym_base := t.sym_base with as_pc := j) t')
  | r => res_rel x y r
           (sym_step_own (MAP (rename_push_label x y) p) env own
             (rename_push_label x y inst) ss')
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `LIST_REL (sv_rel x y) ss.sym_stack ss'.sym_stack ∧
   ss'.sym_base = ss.sym_base` by fs[rn_rel_def] >>
  Cases_on `inst = AsmOp "JUMP" ∨ inst = AsmOp "JUMPI"`
  >- (Cases_on `sym_step_own p env own inst ss` >>
      gvs[sym_step_own_def, sym_step_op_own_def, rename_push_label_def,
          sym_step_op_def, sym_jump_def, sym_jumpi_def,
          sym_set_stack_def, AllCaseEqs()] >>
      gvs[LIST_REL_CONS1, sv_rel_val, sym_jump_dest_rename] >>
      gvs[sv_rel_def, sym_jump_dest_rename, sym_jump_dest_def,
          index_of_label_rename, res_rel_def] >>
      gvs[rn_rel_def, asm_next_def]) >>
  `sym_step_own (MAP (rename_push_label x y) p) env own
     (rename_push_label x y inst) ss' =
   sym_step_own p env own (rename_push_label x y inst) ss'`
    by (irule (GSYM sym_step_own_prog_cong) >> simp[mem_rename] >>
        Cases_on `inst` >> rw[rename_push_label_def] >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `res_rel x y (sym_step_own p env own inst ss)
     (sym_step_own p env own (rename_push_label x y inst) ss')`
    suffices_by (Cases_on `sym_step_own p env own inst ss` >>
                 simp[res_rel_def]) >>
  Cases_on `inst` >>
  simp[sym_step_own_def, sym_step_def, rename_push_label_def]
  >~ [`sym_step_op_own p env own name ss`]
  >- (rw[sym_step_op_own_def]
      >- (irule set_stack_rel >> simp[]) >>
      gvs[] >> simp[sym_step_op_def] >>
      rw[add_rel, mstore_rel, mload_rel, res_rel_def]
      >- (Cases_on `ss.sym_stack` >> Cases_on `ss'.sym_stack` >>
          gvs[res_rel_def] >> irule set_stack_rel >> simp[]) >>
      rpt CASE_TAC >> gvs[dup_swap_rel, concrete_rel])
  >~ [`sym_push_lab l d`]
  >- (irule push_lab_rel >> simp[])
  >~ [`sym_set_stack`]
  >- (rw[] >> irule set_stack_rel >> simp[sv_rel_def]) >>
  irule lift_rel >> fs[rn_rel_def]
QED

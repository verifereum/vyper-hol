(* Restricted code-end uses through SimplifyCFG chain merging. *)
Theory o1LabelFlowOwnSimplifyChain
Ancestors
  o1LabelFlowSimplifyChain codegenSymOwnRel

Theorem simplify_chain_merge_code_end_uses:
  wf_function f /\ fn_inst_wf f /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
     code_end_var f x ==>
     (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
     (i.inst_opcode = CODECOPY /\
      ?dst sz. i.inst_operands = [dst; Var x; sz] /\
               dst <> Var x /\ sz <> Var x)) /\
  MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
  !i x.
    MEM i (fn_insts (f with fn_blocks :=
      update_succ_phi_labels b.bb_label a.bb_label
        (replace_block a.bb_label (merge_blocks a b)
          (remove_block b.bb_label f.fn_blocks))
        (bb_succs (merge_blocks a b)))) /\
    MEM (Var x) i.inst_operands /\
    code_end_var (f with fn_blocks :=
      update_succ_phi_labels b.bb_label a.bb_label
        (replace_block a.bb_label (merge_blocks a b)
          (remove_block b.bb_label f.fn_blocks))
        (bb_succs (merge_blocks a b))) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\
     ?dst sz. i.inst_operands = [dst; Var x; sz] /\
              dst <> Var x /\ sz <> Var x)
Proof
  rpt strip_tac >>
  `code_end_var f x` by
    (irule chain_code_end_backward >> metis_tac[]) >>
  Cases_on `i.inst_opcode = PHI`
  >- (`?j. MEM j (fn_insts f) /\ j.inst_opcode = PHI /\
           MEM (Var x) j.inst_operands` by
        (irule chain_phi_var_source >> metis_tac[]) >>
      first_x_assum (qspecl_then [`j`, `x`] mp_tac) >> simp[]) >>
  `MEM i (fn_insts f)` by
    (irule chain_nonphi_source >> metis_tac[]) >>
  metis_tac[]
QED

Theory o1LabelFlowOwnSimplifyRepair
Ancestors simplifyCfgRestriction[qualified,ignore_grammar]
  o1LabelFlowSimplifyPreservation simplifyCfgShape
  simplifyCfgRestriction simplifyCfgFixupShape
  o1LabelFlowRetention o1LabelFlowLateSimplify

Theorem simplify_unreachable_code_end_uses:
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts (remove_unreachable_blocks f)) /\
    MEM (Var x) i.inst_operands /\ code_end_var (remove_unreachable_blocks f) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  strip_tac >>
  `!i. MEM i (fn_insts (remove_unreachable_blocks f)) ==> MEM i (fn_insts f)` by
    ((MATCH_ACCEPT_TAC simplifyCfgRestrictionTheory.scfg_restriction_insts_subset)) >>
  rpt strip_tac >>
  `code_end_var f x` by metis_tac[code_end_var_instruction_subset] >>
  metis_tac[]
QED

Theorem simplify_fix_phis_code_end_uses:
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts (fix_all_phis f)) /\
    MEM (Var x) i.inst_operands /\ code_end_var (fix_all_phis f) x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  strip_tac >>
  `!i x. MEM i (fn_insts f) /\ i.inst_opcode = PHI /\ code_end_var f x ==>
    ~MEM (Var x) i.inst_operands` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >>
  `code_end_var f x` by metis_tac[simplify_fix_phis_code_end_backward_no_phi] >>
  drule scfg_fix_all_phis_inst_mem >>
  strip_tac >>
  `i = inst` by metis_tac[fix_phi_inst_code_end_identity] >>
  gvs[] >> metis_tac[]
QED

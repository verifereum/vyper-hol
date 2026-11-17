Theory o1LabelFlowOwnSimplifyJump
Ancestors
  list venomInst simplifyCfgDefs simplifyCfgStruct simplifyCfgInvariant simplifyCfgShape
  o1LabelFlowLateSimplify simplifyCfgBypassDataflow o1LabelFlowSimplifyJump

Theorem jump_code_end_restricted_uses:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  !i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >>
  `EVERY (\i. !x. MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
    (fn_insts g)` suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  irule do_merge_jump_every >> conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by metis_tac[update_phi_bypass_var_subset] >>
      `i.inst_opcode <> PHI` by (first_x_assum drule >> simp[] >> strip_tac >> gvs[]) >>
      gvs[update_phi_bypass_def]) >>
  conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by
        metis_tac[canon_jnz_inst_var_subset, subst_label_inst_use_source] >>
      first_x_assum drule >> simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  qexistsl [`a`, `b`, `f`, `lm`, `lm'`] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem simplify_jump_code_end_uses:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  !i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\
    code_end_var g x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)
Proof
  rpt strip_tac >>
  `code_end_var f x` by metis_tac[jump_code_end_backward] >>
  drule_all jump_code_end_restricted_uses >> metis_tac[]
QED

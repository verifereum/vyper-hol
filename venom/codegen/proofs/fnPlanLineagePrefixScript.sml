Theory fnPlanLineagePrefix
Ancestors
  fnPlanLineageReplay fnPlanPrefix stackPlanGen stackPlanTypes list arithmetic

(* Last-call inversion keeps the tail of the original schedule visible. *)
Theorem generate_block_insts_prefix_suc:
  !xs k i lv dfg cfg fn lbl halt np bl ps ops q.
  generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i (SUC k) xs ps =
    SOME (ops,q) <=>
  ?pre mid inst rest step_ops.
    generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k xs ps =
      SOME (pre,mid) /\
    DROP k xs = inst::rest /\
    generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv lbl bl
       else live_vars_at lv lbl (i+k+np+1)) halt
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      lbl mid = SOME (step_ops,q) /\ ops = pre ++ step_ops
Proof
  Induct_on `xs` >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> Cases_on `k`
  >- simp[generate_block_insts_prefix_def,AllCaseEqs()] >>
  simp[generate_block_insts_prefix_def,AllCaseEqs(),PULL_EXISTS] >>
  `i + (np + (SUC n + 1)) = i + (n + (np + 2))` by decide_tac >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!k i lv dfg cfg fn lbl halt np bl ps ops q. _` kall_tac >>
  metis_tac[]
QED

Theorem generate_block_insts_prefix_cleanup_update:
  !k insts lr dfg cfg fn lbl halt np bl i ps h g b.
    generate_block_insts_prefix lr dfg cfg fn lbl halt np bl i k insts (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    OPTION_MAP (\r. (FST r, SND r with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>))
      (generate_block_insts_prefix lr dfg cfg fn lbl halt np bl i k insts ps)
Proof
  Induct >> simp[generate_block_insts_prefix_def] >>
  Cases_on `insts` >> simp[generate_block_insts_prefix_def] >> rpt gen_tac >>
  simp[generate_inst_plan_cleanup_update] >>
  qmatch_goalsub_abbrev_tac `OPTION_MAP _ step_res` >>
  Cases_on `step_res` >> simp[] >> PairCases_on `x` >> simp[] >>
  qmatch_goalsub_abbrev_tac `OPTION_MAP _ tail_res` >>
  Cases_on `tail_res` >> simp[] >> PairCases_on `x` >> simp[]
QED

Theory fnPlanLineagePrefix
Ancestors
  stackPlanGen stackPlanTypes list arithmetic

(* Exact copies from fnPlanPrefix: importing that theory would pull genBlockSim
   and frame-level simulation into planner leaves. The prefix definition is the
   indispensable definitional dependency of the copied split theorem. *)
Definition generate_block_insts_prefix_def:
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (0:num) insts ps =
    SOME ([] : stack_op list, ps) /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) [] ps = NONE /\
  generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
      n_params block_len i (SUC j) (inst :: rest) ps =
    let next_live =
      if rest = [] then live_vars_at liveness bb_label block_len
      else live_vars_at liveness bb_label (i + n_params + 1) in
    let next_is_term =
      case rest of
        [] => F
      | next_i :: _ => is_terminator next_i.inst_opcode in
    case generate_inst_plan liveness dfg cfg fn inst
           next_live is_halting next_is_term bb_label ps of
      NONE => NONE
    | SOME (step_ops, ps') =>
        case generate_block_insts_prefix liveness dfg cfg fn bb_label
               is_halting n_params block_len (i + 1) j rest ps' of
          NONE => NONE
        | SOME (rest_ops, ps'') => SOME (step_ops ++ rest_ops, ps'')
End

Theorem generate_block_insts_plan_split:
  !j insts liveness dfg cfg fn bb_label is_halting n_params block_len i ps
   ops ps_end.
    j <= LENGTH insts ==>
    (generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
       n_params block_len i insts ps = SOME (ops, ps_end) <=>
     ?pre ps_mid post.
       generate_block_insts_prefix liveness dfg cfg fn bb_label is_halting
         n_params block_len i j insts ps = SOME (pre, ps_mid) /\
       generate_block_insts_plan liveness dfg cfg fn bb_label is_halting
         n_params block_len (i + j) (DROP j insts) ps_mid =
         SOME (post, ps_end) /\
       ops = pre ++ post)
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  gen_tac >> Cases_on `insts` >- simp[] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  disch_tac >> rpt gen_tac >> disch_tac >> gvs[] >>
  simp[Once generate_block_insts_plan_def, generate_block_insts_prefix_def,
       LET_THM, AllCaseEqs(), PULL_EXISTS] >>
  `i + SUC j = i + 1 + j` by simp[] >> pop_assum SUBST1_TAC >>
  eq_tac >> strip_tac >> gvs[] >>
  rpt (first_assum $ irule_at Any) >> simp[]
QED

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

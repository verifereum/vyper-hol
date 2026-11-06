Theory fnPlanLineageNativePhases
Ancestors stackPlanGen

(* Each event records the original worker index, instruction, exact query
   context, input/output states and emitted chunk. No resources are assumed. *)
Inductive native_insts_trace:
  (!lv dfg cfg fn lbl halt np bl i ps.
    native_insts_trace lv dfg cfg fn lbl halt np bl i [] ps [] ps []) /\
  (!lv dfg cfg fn lbl halt np bl i inst rest ps chunk mid ops out events.
    generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv lbl bl
       else live_vars_at lv lbl (i + (np + 1))) halt
      (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
      lbl ps = SOME (chunk,mid) /\
    native_insts_trace lv dfg cfg fn lbl halt np bl (i+1) rest mid ops out events ==>
    native_insts_trace lv dfg cfg fn lbl halt np bl i (inst::rest) ps
      (chunk ++ ops) out
      ((i,inst,(if rest = [] then live_vars_at lv lbl bl
                else live_vars_at lv lbl (i + (np + 1))),
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode),
        ps,chunk,mid)::events))
End

Theorem native_insts_trace_sound:
  !lv dfg cfg fn lbl halt np bl i insts ps ops out events.
    native_insts_trace lv dfg cfg fn lbl halt np bl i insts ps ops out events ==>
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts ps = SOME (ops,out)
Proof
  ho_match_mp_tac native_insts_trace_ind >> rpt strip_tac >>
  simp[Once generate_block_insts_plan_def]
QED

Theorem native_insts_trace_complete:
  !insts lv dfg cfg fn lbl halt np bl i ps ops out.
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts ps = SOME (ops,out) ==>
    ?events. native_insts_trace lv dfg cfg fn lbl halt np bl i insts ps ops out events
Proof
  Induct >> simp[generate_block_insts_plan_def]
  >- (rpt strip_tac >> gvs[] >> qexists_tac `[]` >>
      irule (cj 1 native_insts_trace_rules)) >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  irule_at Any (cj 2 native_insts_trace_rules) >> simp[] >>
  goal_assum (drule_at Any)
QED

(* Preparation is represented separately, including the conditional entry
   parameter stage and conditional predecessor cleanup. Exit has no state
   update: the native function only prepends the label and preparation ops. *)
Definition native_block_trace_def:
  native_block_trace lv dfg cfg fn bb ps ops out (ps1,ps2,events) <=>
    ?param_ops clean_ops inst_ops.
      (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
       else ([],ps)) = (param_ops,ps1) /\
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
       then clean_stack_plan lv cfg fn bb ps1
       else ([],ps1)) = (clean_ops,ps2) /\
      native_insts_trace lv dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        0 (non_param_insts bb) ps2 inst_ops out events /\
      ops = [SOLabel bb.bb_label] ++ param_ops ++ clean_ops ++ inst_ops
End

Theorem native_block_trace_sound:
  native_block_trace lv dfg cfg fn bb ps ops out phases ==>
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops,out)
Proof
  PairCases_on `phases` >>
  simp[native_block_trace_def] >> strip_tac >>
  drule native_insts_trace_sound >> strip_tac >>
  simp[generate_block_plan_def] >>
  gvs[]
QED

Theorem native_block_trace_complete:
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops,out) ==>
  ?phases. native_block_trace lv dfg cfg fn bb ps ops out phases
Proof
  simp[generate_block_plan_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule native_insts_trace_complete >> strip_tac >>
  qexists_tac `(ps1,ps2,events)` >>
  simp[native_block_trace_def] >> metis_tac[]
QED

Theorem native_insts_trace_event:
  !lv dfg cfg fn lbl halt np bl i insts ps ops out events.
    native_insts_trace lv dfg cfg fn lbl halt np bl i insts ps ops out events ==>
    !j inst live term before chunk after.
      MEM (j,inst,live,term,before,chunk,after) events ==>
      generate_inst_plan lv dfg cfg fn inst live halt term lbl before = SOME (chunk,after)
Proof
  ho_match_mp_tac native_insts_trace_ind >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

(* A reusable preservation principle, not a resource-preservation claim.
   The closure premise contains the original native suffix and index. *)
Theorem native_insts_trace_preserve:
  !lv dfg cfg fn lbl halt np bl i insts ps ops out events.
    native_insts_trace lv dfg cfg fn lbl halt np bl i insts ps ops out events ==>
    !P.
      P i ps /\
      (!j inst rest before chunk after.
        P j before /\
        generate_inst_plan lv dfg cfg fn inst
          (if rest = [] then live_vars_at lv lbl bl
           else live_vars_at lv lbl (j + (np + 1))) halt
          (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
          lbl before = SOME (chunk,after) ==>
        P (j+1) after) ==>
      P (i + LENGTH insts) out /\
      EVERY (\(j,inst,live,term,before,chunk,after).
        P j before /\ P (j+1) after) events
Proof
  ho_match_mp_tac native_insts_trace_ind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `P (i+1) ps'` by metis_tac[] >>
  qpat_x_assum `!P. _` (qspec_then `P` mp_tac) >>
  impl_tac >- metis_tac[] >>
  simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >>
  strip_tac >> conj_tac
  >- (`i + (LENGTH insts + 1) = SUC (i + LENGTH insts)` by decide_tac >>
      qpat_x_assum `P (_ + _) out` mp_tac >> pure_asm_rewrite_tac[] >>
      disch_then ACCEPT_TAC) >>
  pure_asm_rewrite_tac[] >> simp[NoAsms]
QED

Theorem native_block_trace_preserve:
  native_block_trace lv dfg cfg fn bb ps ops out (ps1,ps2,events) /\
  P ps /\
  (!chunks after.
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps
     else ([],ps)) = (chunks,after) ==> P after) /\
  (!chunks after.
    P ps1 /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan lv cfg fn bb ps1 else ([],ps1)) = (chunks,after) ==>
    P after) /\
  (!inst live term before chunk after.
    P before /\
    generate_inst_plan lv dfg cfg fn inst live (bb_is_halting bb)
      term bb.bb_label before = SOME (chunk,after) ==> P after)
  ==>
  P ps1 /\ P ps2 /\ P out /\
  EVERY (\(j,inst,live,term,before,chunk,after). P before /\ P after) events
Proof
  simp[native_block_trace_def] >> strip_tac >>
  `P ps1` by metis_tac[] >>
  `P ps2` by metis_tac[] >>
  drule native_insts_trace_preserve >>
  disch_then (qspec_then `\j state. P state` mp_tac) >>
  simp[NoAsms] >> impl_tac >- metis_tac[] >>
  strip_tac >> simp[NoAsms] >> metis_tac[]
QED

Theory fnPlanLineageRelationalTail
Ancestors fnPlanLineageSetup stackPlanGen stackPlanOps list

(* Preparation and deletion confinement are inputs. Shielding is required
   only at the actual enabled optimistic observation, with arbitrary spills. *)
Theorem native_regular_conditional_shared_core_replay:
  !liveness dfg cfg fn inst nl halting term lbl ps prefixP prefixQ
   preops r pops t.
    inst.inst_opcode <> JMP /\
    lineage_regular_prepare dfg inst nl
      (ps with ps_stack := prefixP ++ ps.ps_stack) =
      (preops,r with ps_stack := prefixP ++ r.ps_stack) /\
    lineage_regular_prepare dfg inst nl
      (ps with ps_stack := prefixQ ++ ps.ps_stack) =
      (preops,r with ps_stack := prefixQ ++ r.ps_stack) /\
    (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs))
       (r with ps_stack := prefixP ++ r.ps_stack)
     else ([],r with ps_stack := prefixP ++ r.ps_stack)) =
       (pops,t with ps_stack := prefixP ++ t.ps_stack) /\
    (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs))
       (r with ps_stack := prefixQ ++ r.ps_stack)
     else ([],r with ps_stack := prefixQ ++ r.ps_stack)) =
       (pops,t with ps_stack := prefixQ ++ t.ps_stack) /\
    (inst.inst_outputs <> [] /\ FILTER (\v. MEM v nl) inst.inst_outputs <> [] ==>
      nl = [] \/ MEM (Var (LAST nl)) t.ps_stack \/
      (~MEM (Var (LAST nl)) prefixP /\ ~MEM (Var (LAST nl)) prefixQ)) ==>
    ?ops u.
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixP ++ ps.ps_stack) =
        (ops,u with ps_stack := prefixP ++ u.ps_stack) /\
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixQ ++ ps.ps_stack) =
        (ops,u with ps_stack := prefixQ ++ u.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (qexistsl [`preops`, `release_dead_spills nl r`] >>
      simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
        fnPlanLineageInventoryTheory.release_dead_spills_stack]) >>
  Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []`
  >- (qexistsl [`preops ++ pops`, `release_dead_spills nl t`] >>
      gvs[] >>
      simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
        fnPlanLineageInventoryTheory.release_dead_spills_stack]) >>
  namedCases_on `optimistic_swap_plan dfg inst nl term t` ["opts v"] >>
  `optimistic_swap_plan dfg inst nl term
    (t with ps_stack := prefixP ++ t.ps_stack) =
      (opts,v with ps_stack := prefixP ++ v.ps_stack)` by
    (irule optimistic_swap_plan_shielded_bottom_frame >> simp[] >> metis_tac[]) >>
  `optimistic_swap_plan dfg inst nl term
    (t with ps_stack := prefixQ ++ t.ps_stack) =
      (opts,v with ps_stack := prefixQ ++ v.ps_stack)` by
    (irule optimistic_swap_plan_shielded_bottom_frame >> simp[] >> metis_tac[]) >>
  qexistsl [`preops ++ pops ++ opts`, `release_dead_spills nl v`] >>
  gvs[] >>
  simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
    fnPlanLineageInventoryTheory.release_dead_spills_stack]
QED

(* A schedule-indexed simulation boundary.  R carries the actual observation
   premises at each instruction, rather than assuming arbitrary equal-spill
   states replay.  Exact step code equality composes without inspecting ops. *)
Theorem generate_block_insts_plan_relational_replay:
  !lv dfg cfg fn lbl halt np bl R.
    (!i inst rest p q ops p'.
      R i (inst::rest) p q /\
      generate_inst_plan lv dfg cfg fn inst
        (if rest = [] then live_vars_at lv lbl bl
         else live_vars_at lv lbl (i + np + 1)) halt
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
        lbl p = SOME (ops,p') ==>
      ?q'. generate_inst_plan lv dfg cfg fn inst
        (if rest = [] then live_vars_at lv lbl bl
         else live_vars_at lv lbl (i + np + 1)) halt
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
        lbl q = SOME (ops,q') /\ R (i + 1) rest p' q') /\
    (!i p q. R i [] p q ==>
      p.ps_alloc = q.ps_alloc /\ p.ps_spilled = q.ps_spilled) ==>
    !insts i p q ops p'.
      R i insts p q /\
      generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts p =
        SOME (ops,p') ==>
      ?q'. generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts q =
        SOME (ops,q') /\ R (i + LENGTH insts) [] p' q' /\
        p'.ps_alloc = q'.ps_alloc /\ p'.ps_spilled = q'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Induct_on `insts`
  >- (simp[generate_block_insts_plan_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[generate_block_insts_plan_def, AllCaseEqs()] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `q'` >> simp[generate_block_insts_plan_def] >>
  qpat_x_assum `R (_ + 1 + _) [] _ _` mp_tac >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD1, arithmeticTheory.ADD_CLAUSES] >>
  simp[]
QED

Definition lineage_inst_replay_ready_def:
  lineage_inst_replay_ready lv dfg cfg fn inst nl halt term lbl S p q <=>
    if is_pre_codegen_opcode inst.inst_opcode \/
       (inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst) then T
    else if inst.inst_opcode = PHI then
      (!ops p'. generate_phi_plan inst nl halt p = (ops,p') ==>
        ?q'. generate_phi_plan inst nl halt q = (ops,q') /\ S p' q')
    else if inst.inst_opcode = OFFSET then
      (!ops p'. generate_offset_plan inst p = (ops,p') ==>
        ?q'. generate_offset_plan inst q = (ops,q') /\ S p' q')
    else if is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP then S p q
    else
      (!ops p'.
        generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl p = (ops,p') /\
        (inst.inst_opcode = JMP ==> join_reached lv fn lbl inst p') ==>
        ?q'. generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl q = (ops,q') /\
          S p' q' /\ (inst.inst_opcode = JMP ==> join_reached lv fn lbl inst q'))
End

Theorem lineage_inst_replay_ready_step:
  !lv dfg cfg fn inst nl halt term lbl S p q ops p'.
  lineage_inst_replay_ready lv dfg cfg fn inst nl halt term lbl S p q /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl p = SOME (ops,p') ==>
  ?q'. generate_inst_plan lv dfg cfg fn inst nl halt term lbl q = SOME (ops,q') /\
    S p' q'
Proof
  rpt gen_tac >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode`
  >- simp[generate_inst_plan_def] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst`
  >- simp[generate_inst_plan_def] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (simp[lineage_inst_replay_ready_def, generate_inst_plan_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (simp[lineage_inst_replay_ready_def, generate_inst_plan_def] >> metis_tac[]) >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (simp[lineage_inst_replay_ready_def, generate_inst_plan_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (simp[lineage_inst_replay_ready_def, generate_inst_plan_def] >> metis_tac[]) >>
  simp[lineage_inst_replay_ready_def, generate_inst_plan_def] >>
  namedCases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl p`
    ["pops r"] >> simp[] >>
  Cases_on `inst.inst_opcode = JMP` >> simp[] >>
  strip_tac >> gvs[] >>
  qexists_tac `q'` >> simp[]
QED

Definition lineage_schedule_replay_ready_def:
  lineage_schedule_replay_ready lv dfg cfg fn lbl halt np bl R <=>
    (!i inst rest p q ops p'.
      R i (inst::rest) p q /\
      generate_inst_plan lv dfg cfg fn inst
        (if rest = [] then live_vars_at lv lbl bl
         else live_vars_at lv lbl (i + np + 1)) halt
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
        lbl p = SOME (ops,p') ==>
      ?q'. generate_inst_plan lv dfg cfg fn inst
        (if rest = [] then live_vars_at lv lbl bl
         else live_vars_at lv lbl (i + np + 1)) halt
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
        lbl q = SOME (ops,q') /\ R (i + 1) rest p' q') /\
    (!i p q. R i [] p q ==>
      p.ps_alloc = q.ps_alloc /\ p.ps_spilled = q.ps_spilled)
End

Theorem lineage_schedule_replay_ready_intro:
  !lv dfg cfg fn lbl halt np bl R.
    (!i p q. R i [] p q ==>
      p.ps_alloc = q.ps_alloc /\ p.ps_spilled = q.ps_spilled) /\
    (!i inst rest p q. R i (inst::rest) p q ==>
      lineage_inst_replay_ready lv dfg cfg fn inst
        (if rest = [] then live_vars_at lv lbl bl
         else live_vars_at lv lbl (i + np + 1)) halt
        (case rest of [] => F | next::_ => is_terminator next.inst_opcode)
        lbl (R (i + 1) rest) p q) ==>
    lineage_schedule_replay_ready lv dfg cfg fn lbl halt np bl R
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[lineage_schedule_replay_ready_def] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all lineage_inst_replay_ready_step >> simp[]
QED

Theorem lineage_schedule_replay:
  !lv dfg cfg fn lbl halt np bl R insts i p q ops p'.
    lineage_schedule_replay_ready lv dfg cfg fn lbl halt np bl R /\
    R i insts p q /\
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts p =
      SOME (ops,p') ==>
    ?q'. generate_block_insts_plan lv dfg cfg fn lbl halt np bl i insts q =
      SOME (ops,q') /\ R (i + LENGTH insts) [] p' q' /\
      p'.ps_alloc = q'.ps_alloc /\ p'.ps_spilled = q'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule (REWRITE_RULE [GSYM lineage_schedule_replay_ready_def]
    generate_block_insts_plan_relational_replay) >>
  disch_then drule_all >> simp[]
QED

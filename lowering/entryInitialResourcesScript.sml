(* Translate the unit's allocation charge to the body simulation interface. *)
Theory entryInitialResources
Ancestors
  allocaFrontierBound exprLoweringProps allocaBudgetProps vyperCompiler
  contextCodegenRel venomWf venomInst arithmetic

Theorem alloca_size_interface[local]:
  alloca_lit_size = alloca_size
Proof
  simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def]
QED

Theorem pending_alloca_size_budget[local]:
  pending_alloca_size func s = remaining_alloca_budget (fn_insts func) s
Proof
  simp[pending_alloca_size_def, remaining_alloca_budget_def, alloca_size_interface]
QED

Theorem alloca_frontier_inv_room:
  alloca_frontier_inv ctx func inst s /\
  unit_alloca_budget ctx < dimword (:256) ==>
  alloca_room ctx func s
Proof
  strip_tac >>
  gvs[alloca_frontier_inv_def, alloca_room_def, call_targets_card,
      pending_alloca_size_budget, unit_alloca_frame_def, alloca_size_interface] >>
  decide_tac
QED

Theorem initial_alloca_room:
  lookup_function func.fn_name ctx.ctx_functions = SOME func /\
  (!g. TC (fn_directly_calls ctx) func.fn_name g ==>
       ~TC (fn_directly_calls ctx) g g) /\
  s.vs_alloca_next = 0 /\
  unit_alloca_budget ctx < dimword (:256) ==>
  alloca_room ctx func s
Proof
  strip_tac >>
  `MEM func ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule remaining_alloca_budget_frame >>
  disch_then (qspec_then `s` assume_tac) >>
  `CARD {g | TC (fn_directly_calls ctx) func.fn_name g} <=
   LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
     (FLAT (MAP fn_insts ctx.ctx_functions)))` by simp[call_targets_card] >>
  simp[alloca_room_def, call_targets_card, pending_alloca_size_budget,
       unit_alloca_frame_def, alloca_size_interface] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  `remaining_alloca_budget (fn_insts func) s + CARD below * frame <=
   unit_alloca_budget ctx` suffices_by decide_tac >>
  `unit_alloca_budget ctx =
   (1 + LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
      (FLAT (MAP fn_insts ctx.ctx_functions)))) * frame` by
    simp[unit_alloca_budget_def, Abbr `frame`] >>
  `CARD below * frame <=
   LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
     (FLAT (MAP fn_insts ctx.ctx_functions))) * frame` by
    (irule LESS_MONO_MULT >> simp[Abbr `below`]) >>
  `remaining_alloca_budget (fn_insts func) s <= frame` by
    simp[Abbr `frame`] >>
  qpat_x_assum `unit_alloca_budget ctx = _` (fn th =>
    pure_rewrite_tac[th, RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >>
  decide_tac
QED

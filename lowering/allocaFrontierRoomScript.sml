Theory allocaFrontierRoom
Ancestors
  allocaFrontierBound allocaBudgetProps exprLoweringProps vyperCompiler
  contextCodegenRel venomInst venomState list pred_set words arithmetic

Definition alloca_frontier_inv_from_shift_def:
  alloca_frontier_inv_from k ctx fn (inst:instruction) s <=>
    alloca_frontier_inv ctx fn inst
      (s with vs_alloca_next := s.vs_alloca_next - k)
End

(* The static charge fits even when subtracting k clamps the frontier to 0. *)
Theorem alloca_frontier_inv_from_def:
  alloca_frontier_inv_from k ctx fn (inst:instruction) s <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    (!g. TC (fn_directly_calls ctx) fn.fn_name g ==>
         ~TC (fn_directly_calls ctx) g g) /\
    s.vs_alloca_next + remaining_alloca_budget (fn_insts fn) s +
    CARD {g | TC (fn_directly_calls ctx) fn.fn_name g} *
      SUM (MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA)
        (FLAT (MAP fn_insts ctx.ctx_functions)))) <=
    k + unit_alloca_budget ctx
Proof
  `remaining_alloca_budget (fn_insts fn)
     (s with vs_alloca_next := s.vs_alloca_next - k) =
   remaining_alloca_budget (fn_insts fn) s` by
    (irule remaining_alloca_budget_domain_cong >> simp[]) >>
  simp[alloca_frontier_inv_from_shift_def, alloca_frontier_inv_def] >>
  eq_tac >> strip_tac >> simp[]
  >- (Cases_on `k <= s.vs_alloca_next` >- decide_tac >>
      `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      qmatch_goalsub_abbrev_tac `CARD below * frame` >>
      qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = INVOKE)
                         (FLAT (MAP fn_insts ctx.ctx_functions)))` >>
      `remaining_alloca_budget (fn_insts fn) s <= frame /\ CARD below <= n`
        by simp[Abbr `below`, Abbr `frame`, Abbr `n`, call_targets_card,
                remaining_alloca_budget_frame] >>
      `CARD below * frame <= n * frame` by (irule LESS_MONO_MULT >> simp[]) >>
      `unit_alloca_budget ctx = (1 + n) * frame`
        by simp[unit_alloca_budget_def, Abbr `n`, Abbr `frame`] >>
      full_simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  decide_tac
QED

Theorem deploy_ctor_alloca_size_eq:
  alloca_lit_size = alloca_size
Proof
  simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def]
QED

Theorem deploy_ctor_pending_alloca_eq:
  pending_alloca_size func s = remaining_alloca_budget (fn_insts func) s
Proof
  simp[pending_alloca_size_def, remaining_alloca_budget_def,
       deploy_ctor_alloca_size_eq]
QED

Theorem deploy_ctor_frontier_alloca_room:
  alloca_frontier_inv_from k ctx func site s /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  alloca_room ctx func s
Proof
  simp[alloca_frontier_inv_from_def, alloca_room_def,
       deploy_ctor_pending_alloca_eq, unit_alloca_frame_def,
       deploy_ctor_alloca_size_eq, call_targets_card] >>
  rpt strip_tac >> decide_tac
QED

Theorem registration_frontier_alloca_room:
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) ==> alloca_room ctx fn s
Proof
  strip_tac >>
  irule deploy_ctor_frontier_alloca_room >>
  qexistsl [`0`, `site`] >>
  fs[alloca_frontier_inv_from_def, alloca_frontier_inv_def]
QED

(* Allocation charge available at an internal-call boundary. *)
Theory bodyPtrIntCallMargin
Ancestors exprLoweringProps relation finite_map pred_set list arithmetic words

Theorem alloca_room_call_margin:
  !ctx func s finish margin callee.
    alloca_room ctx func s /\
    fn_directly_calls ctx func.fn_name callee /\
    finish <= s.vs_alloca_next /\ margin <= unit_alloca_frame ctx ==>
    finish + margin < dimword (:256)
Proof
  rpt strip_tac >> fs[alloca_room_def] >>
  `TC (fn_directly_calls ctx) func.fn_name callee` by
    metis_tac[TC_SUBSET] >>
  `0 < CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` by
    (spose_not_then assume_tac >>
     `CARD {g | TC (fn_directly_calls ctx) func.fn_name g} = 0` by decide_tac >>
     ` {g | TC (fn_directly_calls ctx) func.fn_name g} = {}` by
       metis_tac[CARD_EQ_0] >>
     fs[EXTENSION]) >>
  `unit_alloca_frame ctx <=
   CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
     unit_alloca_frame ctx` by
    (Cases_on `CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` >>
     fs[MULT_CLAUSES]) >>
  decide_tac
QED

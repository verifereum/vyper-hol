(* Quotation-only checkpoint for the independently agreed definition bodies.
 * Quotations create no theorem objects. The additive guarded relation is
 * defined in guardedFrameReachable; its obligations remain unproved.
 *)
Theory dallocaPrefixStatements
Ancestors
  unitMemInv staticAbortDefs exprLoweringProps ptrDiscipline words list
  guardedFrameReachable frameRawProjection compileVyper unitTransformDefs

val raw_mem_ok_abort_body =
  ``\(ctx:venom_context) (fn:ir_function) inst (s:venom_state).
      in_static_abort_prefix fn s \/ raw_mem_ok ctx fn inst s``;

val lowered_mem_ok_abort_body =
  ``\eom fmp (ctx:venom_context) (fn:ir_function) inst (s:venom_state).
      in_static_abort_prefix fn s \/ lowered_mem_ok eom fmp ctx fn inst s``;

(* Initial-frontier/coverage formula from P7 449d8ce00, with the approved
 * margin 2^128. The current production fmp_room definition is untouched. *)
val fmp_room_body =
  ``\(ctx:venom_context) (func:ir_function) (ss:venom_state).
      (ptrDiscipline$ctx_has_dalloca ctx \/
       EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) ==>
      ss.vs_alloca_next + pending_alloca_size func ss +
      CARD {g | TC (fn_directly_calls ctx) func.fn_name g} *
        unit_alloca_frame ctx <= w2n ss.vs_initial_fmp /\
      w2n ss.vs_initial_fmp <= w2n ss.vs_fmp /\
      w2n ss.vs_initial_fmp + 2 ** 128 < dimword (:256) /\
      w2n ss.vs_fmp <=
        MAX (w2n ss.vs_initial_fmp) (LENGTH ss.vs_memory + 31)``;

val guarded_frame_subset_obligation =
  ``!vs ctx stk PG G tn fn inst s.
      guarded_frame_reachable vs ctx stk PG G tn fn inst s ==>
      frame_reachable vs ctx stk PG G tn fn inst s``;

val guarded_raw_subset_obligation =
  ``!vs ctx fn inst s.
      EVERY wf_function ctx.ctx_functions /\
      guarded_raw_reachable vs ctx fn inst s ==>
      raw_reachable vs ctx fn inst s``;

val guarded_outcomes_obligation =
  ``!vs ctx stk PG G tn fn inst s K.
      LENGTH vs.vs_outcomes <= K /\
      guarded_frame_reachable vs ctx stk PG G tn fn inst s ==>
      ?j. j <= K /\
          LENGTH vs.vs_outcomes = j + LENGTH s.vs_outcomes /\
          s.vs_outcomes = DROP j vs.vs_outcomes``;

(* Draft internal implication: B's site-size producers and the entry margin
 * are open leaves, not proposed top-level assumptions. Compiler emission
 * lockstep must justify the implication; syntax checking does not do so.
 *)
val guarded_allocation_bound_obligation =
  ``!tops rpolicy unit vs K B.
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
      LENGTH vs.vs_outcomes <= K /\
      w2n vs.vs_initial_fmp + (K + 1) * B < dimword (:256) /\
      (!stk PG G tn fn inst s sz_op sz.
         guarded_frame_reachable vs unit.cu_context stk PG G tn fn inst s /\
         inst.inst_opcode = DALLOCA /\ inst.inst_operands = [sz_op] /\
         eval_operand sz_op s = SOME sz ==>
         ceil32 (w2n sz) <= B) ==>
      !stk PG G tn fn inst s.
        guarded_frame_reachable vs unit.cu_context stk PG G tn fn inst s ==>
        dalloca_no_wrap inst s /\
        w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
        w2n s.vs_fmp <= w2n vs.vs_initial_fmp + (K + 1) * B``;

val () = List.app
  (fn (name, body) =>
    if null (free_vars body) then
      print (name ^ ": closed typed quotation\n")
    else raise Fail (name ^ ": unexpected free variables: " ^
      String.concatWith ", " (map term_to_string (free_vars body))))
  [("raw_mem_ok_abort", raw_mem_ok_abort_body),
   ("lowered_mem_ok_abort", lowered_mem_ok_abort_body),
   ("fmp_room", fmp_room_body),
   ("guarded_frame_subset", guarded_frame_subset_obligation),
   ("guarded_raw_subset", guarded_raw_subset_obligation),
   ("guarded_outcomes", guarded_outcomes_obligation),
   ("guarded_allocation_bound", guarded_allocation_bound_obligation)];

(* One execution log retains both GAS attempts and instruction visits, even
   when execution ends in Error. Visit offsets are a projection of this log. *)
Theory dftGasToListTrace
Ancestors
  dftGasOracleDefs venomExecSemantics venomInst venomState list arithmetic

Datatype:
  oracle_trace_item =
    TraceGas gas_event
  | TraceVisit ((num # num) list) num ir_function instruction venom_state
End

Definition trace_events_def:
  (trace_events [] = []) /\
  (trace_events (TraceGas e :: ts) = e :: trace_events ts) /\
  (trace_events (TraceVisit p d fn inst s :: ts) = trace_events ts)
End

(* The accumulator is the number of GAS attempts preceding a visit. *)
Definition trace_visits_def:
  (trace_visits n [] = []) /\
  (trace_visits n (TraceGas e :: ts) = trace_visits (SUC n) ts) /\
  (trace_visits n (TraceVisit p d fn inst s :: ts) =
     (n,p,d,fn,inst,s) :: trace_visits n ts)
End

Definition oracle_trace_defs:
  ((trace_step orc p d fuel ctx inst s : oracle_trace_item list) =
    if inst.inst_opcode = GAS then [TraceGas (p,d,inst.inst_id)]
    else if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => []
      | SOME (nm, ops) =>
          case lookup_function nm ctx.ctx_functions of
            NONE => []
          | SOME callee =>
              case eval_operands ops s of
                NONE => []
              | SOME args =>
                  case setup_callee callee args s of
                    NONE => []
                  | SOME cs =>
                      trace_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee cs
    else []) /\
  ((trace_block orc p d fuel ctx fn bb s : oracle_trace_item list) =
    case get_instruction bb s.vs_inst_idx of
      NONE => []
    | SOME inst =>
        TraceVisit p d fn inst s ::
        (trace_step orc p d fuel ctx inst s ++
         case ev_step orc p d fuel ctx inst s of
           OK s' =>
             if is_terminator inst.inst_opcode then []
             else trace_block orc p d fuel ctx fn bb
                    (s' with vs_inst_idx := SUC s.vs_inst_idx)
         | _ => [])) /\
  ((trace_blocks orc p d fuel ctx fn s : oracle_trace_item list) =
    case fuel of
      0 => []
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => []
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                trace_block orc p (SUC d) fuel' ctx fn bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions) ++
                (case ev_block orc p (SUC d) fuel' ctx bb
                        (s_phi with vs_inst_idx :=
                           phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then []
                     else trace_blocks orc p (SUC d) fuel' ctx fn s'
                 | _ => [])
            | _ => [])
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (orc,p,d,fuel,ctx,inst,s) => (fuel,1)
      | INR (INL (orc,p,d,fuel,ctx,fn,bb,s)) =>
          (fuel,2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (orc,p,d,fuel,ctx,fn,s)) => (fuel,0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     irule pairTheory.WF_LEX >> simp[prim_recTheory.WF_LESS]) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

Theorem trace_step_eq:
  trace_step orc p d fuel ctx inst s =
    if inst.inst_opcode = GAS then [TraceGas (p,d,inst.inst_id)]
    else if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => []
      | SOME (nm,ops) =>
          case lookup_function nm ctx.ctx_functions of
            NONE => []
          | SOME callee =>
              case eval_operands ops s of
                NONE => []
              | SOME args =>
                  case setup_callee callee args s of
                    NONE => []
                  | SOME cs =>
                      trace_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee cs
    else []
Proof
  simp[Once oracle_trace_defs]
QED

Definition trace_function_def:
  trace_function orc fuel ctx fn s =
    case fn_entry_label fn of
      NONE => []
    | SOME lbl => trace_blocks orc [] 0 fuel ctx fn
        (s with <| vs_current_bb := lbl; vs_inst_idx := 0 |>)
End

Definition trace_context_def:
  trace_context orc fuel ctx s =
    case ctx.ctx_entry of
      NONE => []
    | SOME nm =>
        case lookup_function nm ctx.ctx_functions of
          NONE => []
        | SOME fn => trace_function orc fuel ctx fn
            (s with vs_prev_bb := NONE)
End

Theorem trace_events_append:
  !xs ys. trace_events (xs ++ ys) = trace_events xs ++ trace_events ys
Proof
  Induct >> simp[trace_events_def] >> Cases_on `h` >>
  simp[trace_events_def]
QED

Theorem trace_visits_append:
  !xs n ys. trace_visits n (xs ++ ys) =
    trace_visits n xs ++ trace_visits (n + LENGTH (trace_events xs)) ys
Proof
  Induct >> simp[trace_visits_def, trace_events_def] >>
  Cases_on `h` >> simp[trace_visits_def, trace_events_def, ADD_CLAUSES]
QED

Theorem trace_blocks_zero:
  trace_blocks orc p d 0 ctx fn s = []
Proof
  simp[Once oracle_trace_defs]
QED

Theorem trace_step_gas:
  inst.inst_opcode = GAS ==>
  trace_step orc p d fuel ctx inst s = [TraceGas (p,d,inst.inst_id)]
Proof
  simp[trace_step_eq]
QED

Theorem trace_step_bad_invoke:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = NONE ==>
  trace_step orc p d fuel ctx inst s = []
Proof
  simp[trace_step_eq]
QED

Theorem trace_step_invoke:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  trace_step orc p d fuel ctx inst s =
    trace_blocks orc ((d,inst.inst_id)::p) d fuel ctx callee cs
Proof
  simp[trace_step_eq]
QED

Theorem trace_block_error:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ev_step orc p d fuel ctx inst s = Error err ==>
  trace_block orc p d fuel ctx fn bb s =
    TraceVisit p d fn inst s :: trace_step orc p d fuel ctx inst s
Proof
  simp[Once oracle_trace_defs]
QED

Theorem trace_malformed_gas:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\
  (!out. inst.inst_outputs <> [out]) ==>
  trace_block orc p d fuel ctx fn bb s =
    [TraceVisit p d fn inst s; TraceGas (p,d,inst.inst_id)]
Proof
  rpt strip_tac >>
  `ev_step orc p d fuel ctx inst s = Error "read0 requires single output"`
    by (simp[Once ev_defs, ev_gas_def] >>
        namedCases_on `inst.inst_outputs` ["", "out rest"] >>
        simp[] >> Cases_on `rest` >> gvs[]) >>
  drule_all trace_block_error >> simp[trace_step_gas]
QED

Theorem trace_block_eq:
  trace_block orc p d fuel ctx fn bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => []
    | SOME inst =>
        TraceVisit p d fn inst s ::
        (trace_step orc p d fuel ctx inst s ++
         case ev_step orc p d fuel ctx inst s of
           OK s' =>
             if is_terminator inst.inst_opcode then []
             else trace_block orc p d fuel ctx fn bb
                    (s' with vs_inst_idx := SUC s.vs_inst_idx)
         | _ => [])
Proof
  simp[Once oracle_trace_defs]
QED

Theorem trace_blocks_eq:
  trace_blocks orc p d fuel ctx fn s =
    case fuel of
      0 => []
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => []
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                trace_block orc p (SUC d) fuel' ctx fn bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions) ++
                (case ev_block orc p (SUC d) fuel' ctx bb
                        (s_phi with vs_inst_idx :=
                           phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then []
                     else trace_blocks orc p (SUC d) fuel' ctx fn s'
                 | _ => [])
            | _ => []
Proof
  simp[Once oracle_trace_defs]
QED

(* An INVOKE visit precedes the callee, and the next caller instruction
   follows the entire callee log, also when that instruction fails. *)
Theorem trace_invoke_then_failed_gas:
  get_instruction bb s.vs_inst_idx = SOME call_inst /\
  call_inst.inst_opcode = INVOKE /\ decode_invoke call_inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  ev_step orc p d fuel ctx call_inst s = OK s' /\
  ~is_terminator call_inst.inst_opcode /\
  next = s' with vs_inst_idx := SUC s.vs_inst_idx /\
  get_instruction bb next.vs_inst_idx = SOME gas /\
  gas.inst_opcode = GAS /\ ev_step orc p d fuel ctx gas next = Error err ==>
  trace_block orc p d fuel ctx fn bb s =
    TraceVisit p d fn call_inst s ::
    (trace_blocks orc ((d,call_inst.inst_id)::p) d fuel ctx callee cs ++
     [TraceVisit p d fn gas next; TraceGas (p,d,gas.inst_id)])
Proof
  rpt strip_tac >>
  drule_all trace_block_error >>
  simp[trace_step_gas] >> strip_tac >>
  simp[Once trace_block_eq, trace_step_eq]
QED

Theorem trace_visit_offset_probe:
  trace_visits n
    (TraceVisit p d fn call_inst s ::
     (callee_log ++ [TraceVisit p d fn gas t; TraceGas e])) =
  (n,p,d,fn,call_inst,s) ::
  (trace_visits n callee_log ++
   [(n + LENGTH (trace_events callee_log),p,d,fn,gas,t)])
Proof
  simp[trace_visits_def, trace_visits_append]
QED

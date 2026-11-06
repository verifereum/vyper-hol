(* List execution visits. Fuel is deliberately absent from a visit. *)
Theory dftGasFromListTraceDefs
Ancestors
  dftGasOracleDefs venomExecSemantics venomInst venomState list arithmetic

Type list_visit = ``:gas_event # ir_function # instruction # venom_state``

Definition trace_defs:
  ((trace_step p d fuel ctx fn inst s : list_visit list) =
    if inst.inst_opcode = INVOKE then
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
                      trace_blocks ((d, inst.inst_id)::p) d fuel ctx callee cs
    else []) /\
  ((trace_block p d fuel ctx fn bb s : list_visit list) =
    case get_instruction bb s.vs_inst_idx of
      NONE => []
    | SOME inst =>
        ((p,d,inst.inst_id),fn,inst,s) ::
        (trace_step p d fuel ctx fn inst s ++
         case step_inst fuel ctx inst s of
           OK s' =>
             if is_terminator inst.inst_opcode then []
             else trace_block p d fuel ctx fn bb
                    (s' with vs_inst_idx := SUC s.vs_inst_idx)
         | _ => [])) /\
  ((trace_blocks p d fuel ctx fn s : list_visit list) =
    case fuel of
      0 => []
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => []
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK sp =>
                trace_block p (SUC d) fuel' ctx fn bb
                  (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
                (case exec_block fuel' ctx bb
                        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then []
                     else trace_blocks p (SUC d) fuel' ctx fn s'
                 | _ => [])
            | _ => [])
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      INL (p,d,fuel,ctx,fn,inst,s) => (fuel,1)
    | INR (INL (p,d,fuel,ctx,fn,bb,s)) =>
        (fuel,2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
    | INR (INR (p,d,fuel,ctx,fn,s)) => (fuel,0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

Definition trace_function_def:
  trace_function fuel ctx fn s =
    case fn_entry_label fn of
      NONE => []
    | SOME lbl => trace_blocks [] 0 fuel ctx fn
        (s with <| vs_current_bb := lbl; vs_inst_idx := 0 |> )
End

Definition trace_context_def:
  trace_context fuel ctx s =
    case ctx.ctx_entry of
      NONE => []
    | SOME nm =>
        case lookup_function nm ctx.ctx_functions of
          NONE => []
        | SOME fn => trace_function fuel ctx fn (s with vs_prev_bb := NONE)
End

Definition visit_gas_def:
  visit_gas ((e,fn,inst,s):list_visit) =
    if inst.inst_opcode = GAS then
      [(e, case s.vs_gas_readings of [] => 0w | w::_ => w)]
    else []
End

Definition trace_gas_def:
  trace_gas visits = FLAT (MAP visit_gas visits)
End

Definition trace_agrees_def:
  trace_agrees orc visits = EVERY (\(e,w). orc e = w) (trace_gas visits)
End

Theorem trace_blocks_zero[simp]:
  trace_blocks p d 0 ctx fn s = []
Proof
  simp[Once trace_defs]
QED

Theorem trace_step_noninvoke:
  inst.inst_opcode <> INVOKE ==> trace_step p d fuel ctx fn inst s = []
Proof
  simp[Once trace_defs]
QED

Theorem trace_block_visit:
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  trace_block p d fuel ctx fn bb s =
    ((p,d,inst.inst_id),fn,inst,s) ::
    (trace_step p d fuel ctx fn inst s ++
     case step_inst fuel ctx inst s of
       OK s' => if is_terminator inst.inst_opcode then []
                else trace_block p d fuel ctx fn bb
                       (s' with vs_inst_idx := SUC s.vs_inst_idx)
     | _ => [])
Proof
  simp[Once trace_defs]
QED

Theorem trace_step_invoke:
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs ==>
  trace_step p d fuel ctx fn inst s =
    trace_blocks ((d,inst.inst_id)::p) d fuel ctx callee cs
Proof
  simp[Once trace_defs]
QED

Theorem trace_blocks_enter:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  trace_blocks p d (SUC fuel) ctx fn s =
    trace_block p (SUC d) fuel ctx fn bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
    (case exec_block fuel ctx bb
            (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
       OK s' => if s'.vs_halted then []
                else trace_blocks p (SUC d) fuel ctx fn s'
     | _ => [])
Proof
  simp[Once trace_defs]
QED

Theorem trace_step_gas:
  inst.inst_opcode = GAS ==> trace_step p d fuel ctx fn inst s = []
Proof
  simp[Once trace_defs]
QED

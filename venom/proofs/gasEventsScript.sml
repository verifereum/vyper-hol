(* Record the instruction sites of reached GAS events. The recursion uses
   the same fuel and machine states as gasCount, including INVOKE callees. *)
Theory gasEvents
Ancestors
  gasCount venomExecSemantics venomInst venomState list arithmetic

Definition gas_events_defs:
  ((gas_events_step fuel ctx owner inst s : (string # num) list) =
    if inst.inst_opcode = GAS then [(owner, inst.inst_id)]
    else if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => []
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => []
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => []
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => []
                  | SOME callee_s =>
                      gas_events_blocks fuel ctx callee_fn callee_s
    else []) /\
  ((gas_events_block fuel ctx owner bb s : (string # num) list) =
    case get_instruction bb s.vs_inst_idx of
      NONE => []
    | SOME inst =>
        gas_events_step fuel ctx owner inst s ++
        (case step_inst fuel ctx inst s of
           OK s' =>
             if is_terminator inst.inst_opcode then []
             else gas_events_block fuel ctx owner bb
                    (s' with vs_inst_idx := SUC s.vs_inst_idx)
         | _ => [])) /\
  ((gas_events_blocks fuel ctx fn s : (string # num) list) =
    case fuel of
      0 => []
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => []
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                gas_events_block fuel' ctx fn.fn_name bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions) ++
                (case exec_block fuel' ctx bb
                        (s_phi with vs_inst_idx :=
                           phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then []
                     else gas_events_blocks fuel' ctx fn s'
                 | _ => [])
            | _ => [])
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, owner, inst, s) => (fuel, 1)
      | INR (INL (fuel, ctx, owner, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (fuel, ctx, fn, s)) => (fuel, 0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

val gas_events_step_def = save_thm("gas_events_step_def", cj 1 gas_events_defs);
val gas_events_block_def = save_thm("gas_events_block_def", cj 2 gas_events_defs);
val gas_events_blocks_def = save_thm("gas_events_blocks_def", cj 3 gas_events_defs);

Theorem gas_events_length:
  (!fuel ctx owner inst s.
     LENGTH (gas_events_step fuel ctx owner inst s) =
       gas_count_step fuel ctx inst s) /\
  (!fuel ctx owner bb s.
     LENGTH (gas_events_block fuel ctx owner bb s) =
       gas_count_block fuel ctx bb s) /\
  (!fuel ctx fn s.
     LENGTH (gas_events_blocks fuel ctx fn s) =
       gas_count_blocks fuel ctx fn s)
Proof
  ho_match_mp_tac gas_events_defs_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once gas_events_defs, Once gas_count_defs] >>
  BasicProvers.every_case_tac >> gvs[]
QED

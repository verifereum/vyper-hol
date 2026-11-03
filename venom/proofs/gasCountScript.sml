(* Count executed GAS instructions, including reads after oracle exhaustion
   and reads in INVOKE callees. The recursion follows the existing runner. *)
Theory gasCount
Ancestors
  gasOracleReplay venomExecSemantics venomExecProofs venomInst venomState list arithmetic

Definition gas_count_defs:
  ((gas_count_step fuel ctx inst s : num) =
    if inst.inst_opcode = GAS then 1
    else if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => 0
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => 0
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => 0
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => 0
                  | SOME callee_s => gas_count_blocks fuel ctx callee_fn callee_s
    else 0) /\
  ((gas_count_block fuel ctx bb s : num) =
    case get_instruction bb s.vs_inst_idx of
      NONE => 0
    | SOME inst =>
        gas_count_step fuel ctx inst s +
        (case step_inst fuel ctx inst s of
           OK s' =>
             if is_terminator inst.inst_opcode then 0
             else gas_count_block fuel ctx bb
                    (s' with vs_inst_idx := SUC s.vs_inst_idx)
         | _ => 0)) /\
  ((gas_count_blocks fuel ctx fn s : num) =
    case fuel of
      0 => 0
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => 0
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              OK s_phi =>
                gas_count_block fuel' ctx bb
                  (s_phi with vs_inst_idx :=
                     phi_prefix_length bb.bb_instructions) +
                (case exec_block fuel' ctx bb
                        (s_phi with vs_inst_idx :=
                           phi_prefix_length bb.bb_instructions) of
                   OK s' =>
                     if s'.vs_halted then 0 else gas_count_blocks fuel' ctx fn s'
                 | _ => 0)
            | _ => 0)
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, inst, s) => (fuel, 1)
      | INR (INL (fuel, ctx, bb, s)) =>
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

val gas_count_step_def = save_thm("gas_count_step_def", cj 1 gas_count_defs);
val gas_count_block_def = save_thm("gas_count_block_def", cj 2 gas_count_defs);
val gas_count_blocks_def = save_thm("gas_count_blocks_def", cj 3 gas_count_defs);

Definition gas_count_suffix_def:
  gas_count_suffix n s r <=>
    case r of
      OK t => t.vs_gas_readings = DROP n s.vs_gas_readings
    | Halt t => t.vs_gas_readings = DROP n s.vs_gas_readings
    | IntRet vals t => t.vs_gas_readings = DROP n s.vs_gas_readings
    | Abort a t => t.vs_gas_readings = DROP n s.vs_gas_readings
    | Error e => T
End

Theorem gas_replay_at_suffix:
  gas_replay_at n f s ==> gas_count_suffix n s (f s)
Proof
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `[]` mp_tac) >>
  Cases_on `f s` >>
  Cases_on `f (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ [])` >>
  simp[stateEquivTheory.lift_result_def, gas_count_suffix_def] >>
  metis_tac[]
QED

Theorem gas_count_suffix_compose:
  gas_count_suffix n s (OK t) /\ gas_count_suffix m t r ==>
  gas_count_suffix (n + m) s r
Proof
  Cases_on `r` >> simp[gas_count_suffix_def, rich_listTheory.DROP_DROP_T]
QED

Theorem gas_count_phis:
  gas_count_suffix 0 s (eval_phis s insts)
Proof
  mp_tac gas_eval_phis >>
  disch_then (qspecl_then [`insts`, `s`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP gas_replay_at_suffix) >> simp[]
QED

Theorem gas_count_phis_ok:
  eval_phis s insts = OK t ==> t.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> mp_tac gas_count_phis >> simp[gas_count_suffix_def]
QED

Theorem gas_count_base:
  gas_count_suffix (if inst.inst_opcode = GAS then 1 else 0) s
    (step_inst_base inst s)
Proof
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[venomExecSemanticsTheory.step_inst_base_def] >>
      irule gas_replay_at_suffix >> simp[gas_exec_gas]) >>
  simp[] >> irule gas_replay_at_suffix >> simp[gas_base_non_gas]
QED

Theorem gas_count_suffix:
  (!fuel ctx inst s.
     gas_count_suffix (gas_count_step fuel ctx inst s) s
       (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
     gas_count_suffix (gas_count_block fuel ctx bb s) s
       (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
     gas_count_suffix (gas_count_blocks fuel ctx fn s) s
       (run_blocks fuel ctx fn s))
Proof
  cheat
QED

Theorem gas_count_fuel_mono:
  (!n m ctx inst s r.
     step_inst n ctx inst s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_step n ctx inst s = gas_count_step m ctx inst s) /\
  (!n m ctx bb s r.
     exec_block n ctx bb s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_block n ctx bb s = gas_count_block m ctx bb s) /\
  (!n m ctx fn s r.
     run_blocks n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
     gas_count_blocks n ctx fn s = gas_count_blocks m ctx fn s)
Proof
  cheat
QED

(*
 * Venom runs that read GAS from an event oracle instead of the state's
 * reading list.  Proof-only: dft_ctx_sim_gas uses them to fix the readings
 * of a run independently of the order DFT gives the GAS instructions.
 *
 * A GAS event names one GAS execution by where it happens, not by when:
 * the frame (the INVOKE sites from the entry, each as the depth of its
 * block and the INVOKE's id), the depth of the block in its call chain
 * (the number of blocks entered along it), and the GAS instruction's id.
 * DFT keeps blocks, ids and the fuel each block runs at, so a run of a
 * context and of its DFT schedule name their GAS executions alike.
 *
 * TOP-LEVEL:
 *   ev_step / ev_block / ev_blocks - run_defs with the oracle
 *   ev_function / ev_context       - run_function / run_context with it
 *   ev_reachable                   - raw_reachable with it, per event frame
 *   gas_res_rel                    - results equal up to vs_gas_readings
 *)
Theory dftGasOracleDefs
Ancestors
  o1PassContract contextCodegenRel venomExecSemantics venomInst venomState

Type gas_event = ``:(num # num) list # num # num``

(* ===== Oracle semantics ===== *)

(* GAS reads the oracle's word for its event (exec_gas without the list). *)
Definition ev_gas_def:
  ev_gas (w:bytes32) inst s =
    case inst.inst_outputs of
      [out] => OK (update_var out w s)
    | _ => Error "read0 requires single output"
End

(* run_defs, with the oracle orc, the frame p and the block depth d.  The
   callee of an INVOKE in a block of depth d runs in frame (d, id) :: p
   and its first block has depth SUC d. *)
Definition ev_defs:
  (ev_step (orc:gas_event -> bytes32) p d fuel ctx inst s =
    if inst.inst_opcode = GAS then ev_gas (orc (p, d, inst.inst_id)) inst s
    else if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => Error "invoke: bad operand format"
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => Error "invoke: undefined argument"
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => Error "invoke: empty function"
                  | SOME callee_s =>
                      case ev_blocks orc ((d, inst.inst_id) :: p) d fuel ctx
                             callee_fn callee_s of
                        IntRet ret callee_s' =>
                          (case bind_outputs inst.inst_outputs ret.iret_values
                                  (adopt_return_fmp ret
                                    (merge_callee_state s callee_s')) of
                            SOME s' => OK s'
                          | NONE => Error "invoke: return arity mismatch")
                      | Halt s' => Halt s'
                      | Abort a s' => Abort a s'
                      | Error e => Error e
                      | OK _ => Error "invoke: callee did not return"
    else step_inst_base inst s)
  /\
  (ev_block orc p d fuel ctx bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => Error "block not terminated"
    | SOME inst =>
        case ev_step orc p d fuel ctx inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then
              if s'.vs_halted then Halt s' else OK s'
            else ev_block orc p d fuel ctx bb
                   (s' with vs_inst_idx := SUC s.vs_inst_idx)
        | IntRet vals s' => IntRet vals s'
        | Halt s' => Halt s'
        | Abort a s' => Abort a s'
        | Error e => Error e)
  /\
  (ev_blocks orc p d fuel ctx fn s =
    case fuel of
      0 => Error "out of fuel"
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => Error "block not found"
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              Error e => Error e
            | OK s_phi =>
                case ev_block orc p (SUC d) fuel' ctx bb
                       (s_phi with vs_inst_idx :=
                          phi_prefix_length bb.bb_instructions) of
                  OK s' =>
                    if s'.vs_halted then Halt s'
                    else ev_blocks orc p (SUC d) fuel' ctx fn s'
                | IntRet vals s' => IntRet vals s'
                | other => other)
Termination
  qexists_tac `inv_image ($< LEX $<)
    (\x. case x of
      | INL (orc, p, d, fuel, ctx, inst, s) => (fuel, 1)
      | INR (INL (orc, p, d, fuel, ctx, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (orc, p, d, fuel, ctx, fn, s)) => (fuel, 0))` >>
  conj_tac >-
    (irule relationTheory.WF_inv_image >>
     MATCH_ACCEPT_TAC (MATCH_MP pairTheory.WF_LEX
       (CONJ prim_recTheory.WF_LESS prim_recTheory.WF_LESS))) >>
  simp_tac bool_ss [relationTheory.inv_image_thm, sumTheory.sum_case_def,
    pairTheory.pair_case_def, pairTheory.LEX_DEF_THM] >>
  rpt strip_tac >> gvs[get_instruction_def]
End

val ev_step_def = save_thm("ev_step_def", cj 1 ev_defs);
val ev_block_def = save_thm("ev_block_def", cj 2 ev_defs);
val ev_blocks_def = save_thm("ev_blocks_def", cj 3 ev_defs);

Definition ev_function_def:
  ev_function orc fuel ctx fn s =
    case fn_entry_label fn of
      NONE => Error "no entry block"
    | SOME lbl =>
        ev_blocks orc [] 0 fuel ctx fn
          (s with <| vs_current_bb := lbl; vs_inst_idx := 0 |>)
End

Definition ev_context_def:
  ev_context orc fuel ctx s =
    case ctx.ctx_entry of
      NONE => Error "no entry function"
    | SOME entry_name =>
        case lookup_function entry_name ctx.ctx_functions of
          NONE => Error "entry function not found"
        | SOME entry_fn =>
            ev_function orc fuel ctx entry_fn (s with vs_prev_bb := NONE)
End

(* ===== Oracle reachability ===== *)

(* raw_reachable (contextRawReachable) for the oracle semantics; each state
   carries its frame p and block depth d. *)
Inductive ev_reachable:
[~entry:]
  (!orc vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     ev_reachable orc vs0 ctx [] 1 fn inst s1)
[~next:]
  (!orc vs0 ctx p d fn inst inst' s s' fuel.
     ev_reachable orc vs0 ctx p d fn inst s /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\
     ev_step orc p d fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ev_reachable orc vs0 ctx p d fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!orc vs0 ctx p d fn inst inst' s s' s1 fuel.
     ev_reachable orc vs0 ctx p d fn inst s /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\
     ev_step orc p d fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     ev_reachable orc vs0 ctx p (SUC d) fn inst' s1)
[~callee:]
  (!orc vs0 ctx p d caller inv s nm ops callee args cs s1 inst.
     ev_reachable orc vs0 ctx p d caller inv s /\ active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     ev_reachable orc vs0 ctx ((d, inv.inst_id) :: p) (SUC d) callee inst s1)
End

(* ===== Results up to the reading list ===== *)

Definition gas_res_rel_def:
  gas_res_rel r r' <=>
    case (r, r') of
      (OK s, OK s') => gas_variant s s'
    | (Halt s, Halt s') => gas_variant s s'
    | (IntRet v s, IntRet v' s') => v = v' /\ gas_variant s s'
    | (Abort a s, Abort a' s') => a = a' /\ gas_variant s s'
    | (Error e, Error e') => T
    | _ => F
End

(* Experimental open-call presentation.  The oracle list field is ghost data:
   GAS reads the separate stream/counter.  Adequacy must materialize the unread
   suffix in that field; it is NOT asserted by these constructor probes. *)
Theory dftOpenMachine
Ancestors
  venomExecSemantics venomInst dftSparseOracle

Datatype:
  dft_open_frame = DftCaller ir_function num basic_block instruction venom_state
End

Datatype:
  dft_open_control = DftEnter ir_function num venom_state
                   | DftAt ir_function num basic_block venom_state
                   | DftDone exec_result
End

Datatype:
  dft_open_config = DftOpen dft_open_control (dft_open_frame list) num
End

(* budget is the remainder AFTER the current block entry. *)
Definition dft_open_continue_def:
  dft_open_continue fn budget bb inst before after =
    if is_terminator inst.inst_opcode then
      if after.vs_halted then DftDone (Halt after)
      else DftEnter fn budget after
    else DftAt fn budget bb
           (after with vs_inst_idx := SUC before.vs_inst_idx)
End

Definition dft_open_deliver_def:
  dft_open_deliver fn budget bb inst before stack n result =
    case result of
      OK after => DftOpen
        (dft_open_continue fn budget bb inst before after) stack n
    | other => DftOpen (DftDone other) stack n
End

(* Return is a separate transition: the caller's fuel, not the callee's,
   is restored. Halt/Abort/Error propagate without popping into the caller. *)
Definition dft_open_return_def:
  dft_open_return result stack n =
    case (result, stack) of
      (IntRet ret cs, DftCaller fn budget bb inst caller :: rest) =>
        (case bind_outputs inst.inst_outputs ret.iret_values
                (adopt_return_fmp ret (merge_callee_state caller cs)) of
           NONE => DftOpen (DftDone (Error "invoke: return arity mismatch")) [] n
         | SOME after => dft_open_deliver fn budget bb inst caller rest n (OK after))
    | _ => DftOpen (DftDone result) [] n
End

Definition dft_open_invoke_def:
  dft_open_invoke ctx fn budget bb inst s stack n =
    case decode_invoke inst of
      NONE => DftOpen (DftDone (Error "invoke: bad operand format")) [] n
    | SOME (nm, ops) =>
        case lookup_function nm ctx.ctx_functions of
          NONE => DftOpen (DftDone (Error "invoke: function not found")) [] n
        | SOME callee =>
            case eval_operands ops s of
              NONE => DftOpen (DftDone (Error "invoke: undefined argument")) [] n
            | SOME args =>
                case setup_callee callee args s of
                  NONE => DftOpen (DftDone (Error "invoke: empty function")) [] n
                | SOME cs => DftOpen (DftEnter callee budget cs)
                    (DftCaller fn budget bb inst s :: stack) n
End

Definition dft_open_next_def:
  dft_open_next (a:num -> 256 word) ctx (DftOpen control stack n) =
    case control of
      DftDone result => dft_open_return result stack n
    | DftEnter fn fuel s =>
        (case fuel of
           0 => DftOpen (DftDone (Error "out of fuel")) [] n
         | SUC budget =>
             case lookup_block s.vs_current_bb fn.fn_blocks of
               NONE => DftOpen (DftDone (Error "block not found")) [] n
             | SOME bb =>
                 case eval_phis s bb.bb_instructions of
                   OK sp => DftOpen (DftAt fn budget bb
                     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) stack n
                 | other => DftOpen (DftDone other) stack n)
    | DftAt fn budget bb s =>
        (case get_instruction bb s.vs_inst_idx of
           NONE => DftOpen (DftDone (Error "block not terminated")) [] n
         | SOME inst =>
             if inst.inst_opcode = INVOKE then
               dft_open_invoke ctx fn budget bb inst s stack n
             else if inst.inst_opcode = GAS then
               (case inst.inst_outputs of
                  [out] => dft_open_deliver fn budget bb inst s stack (SUC n)
                             (OK (update_var out (a n) s))
                | _ => DftOpen (DftDone (Error "read0 requires single output")) [] n)
             else dft_open_deliver fn budget bb inst s stack n (step_inst_base inst s))
End

(* Observations precede execution, including at a nonreturning call. *)
Definition dft_open_observe_def:
  dft_open_observe fn inst s config <=>
    ?budget bb stack n.
      config = DftOpen (DftAt fn budget bb s) stack n /\
      get_instruction bb s.vs_inst_idx = SOME inst
End

Theorem dft_open_single_gas:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
  DftOpen (DftAt fn budget bb
    ((update_var out (a n) s) with vs_inst_idx := SUC s.vs_inst_idx)) stack (SUC n)
Proof
  simp[dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       is_terminator_def]
QED

Theorem dft_open_invoke_push:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftEnter callee budget cs)
      (DftCaller fn budget bb inst s :: stack) n
Proof
  simp[dft_open_next_def, dft_open_invoke_def]
QED

Theorem dft_open_block_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  dft_open_next a ctx (DftOpen (DftEnter fn (SUC budget) s) stack n) =
    DftOpen (DftAt fn budget bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) stack n
Proof
  simp[dft_open_next_def]
QED

Theorem dft_open_callee_observation:
  get_instruction bb s.vs_inst_idx = SOME call_inst /\ call_inst.inst_opcode = INVOKE /\
  decode_invoke call_inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  lookup_block cs.vs_current_bb callee.fn_blocks = SOME cb /\
  eval_phis cs cb.bb_instructions = OK cp /\
  observed = cp with vs_inst_idx := phi_prefix_length cb.bb_instructions /\
  get_instruction cb observed.vs_inst_idx = SOME ci ==>
  dft_open_observe callee ci observed
    (dft_open_next a ctx (dft_open_next a ctx
      (DftOpen (DftAt fn (SUC budget) bb s) stack n)))
Proof
  strip_tac >> drule_all dft_open_invoke_push >> disch_tac >>
  simp[dft_open_next_def, dft_open_observe_def] >> gvs[]
QED

Theorem dft_open_return_resume:
  inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  dft_open_next a ctx
    (DftOpen (DftDone (IntRet ret cs))
      (DftCaller fn budget bb inst caller :: stack) n) =
  DftOpen (DftAt fn budget bb
    (after with vs_inst_idx := SUC caller.vs_inst_idx)) stack n
Proof
  simp[dft_open_next_def, dft_open_return_def, dft_open_deliver_def,
       dft_open_continue_def, is_terminator_def]
QED

(* Materialization is required only at the interface to the list semantics.
   The counter counts ALL successful GAS instructions, including zero reads
   after exhaustion.  The ghost list field need not track that counter. *)
Definition dft_open_materialize_def:
  dft_open_materialize xs n s = s with vs_gas_readings := DROP n xs
End

Definition dft_open_materialize_result_def:
  dft_open_materialize_result xs n result =
    case result of
      OK s => OK (dft_open_materialize xs n s)
    | IntRet ret s => IntRet ret (dft_open_materialize xs n s)
    | Halt s => Halt (dft_open_materialize xs n s)
    | Abort reason s => Abort reason (dft_open_materialize xs n s)
    | Error e => Error e
End

(* PROPOSED ADEQUACY OBLIGATIONS -- NOT THEOREMS, NOT ASSUMPTIONS.

   Terminal adequacy modulo Error text (same fuel, arbitrary function/state;
   dft_open_result_eq is defined in dftOpenAdequacy):

   dft_sparse_oracle a s.vs_gas_readings ==>
   (dft_open_result_eq (run_blocks fuel ctx fn s) result <=>
      ?steps rr n.
        FUNPOW (dft_open_next a ctx) steps
          (DftOpen (DftEnter fn fuel s) [] 0) =
            DftOpen (DftDone rr) [] n /\
        dft_open_result_eq
          (dft_open_materialize_result s.vs_gas_readings n rr) result)

   Raw-observation adequacy (all finite prefixes, including open calls):
   Let initial = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
                           vs_inst_idx := 0|>.
   Under the premises
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME entry /\
     fn_entry_label entry = SOME lbl /\
     EVERY (\f. ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks))
       ctx.ctx_functions /\
     dft_sparse_oracle a vs0.vs_gas_readings,
   the proposed equivalence is

   raw_reachable vs0 ctx fn inst observed <=>
     ?fuel steps budget bb ghost stack n.
       FUNPOW (dft_open_next a ctx) steps
         (DftOpen (DftEnter entry fuel initial) [] 0) =
           DftOpen (DftAt fn budget bb ghost) stack n /\
       get_instruction bb ghost.vs_inst_idx = SOME inst /\
       observed = dft_open_materialize vs0.vs_gas_readings n ghost

   Label uniqueness matters: active_inst uses MEM, whereas entry dispatch
   uses lookup_block.  Without it raw_reachable can select instructions from
   a different same-labelled block.  The task's o1_fn_shape has wf_function.
   The observation interface deliberately existentially quantifies fuel:
   raw_reachable next/block rules may use independent successful fuels.
   Proving that one sufficiently large root budget decorates a finite raw
   derivation requires monotonicity; it is NOT a constructor simplification.

   Paired-frontier candidate for subsequent review: decorate each active
   block and saved caller with a dynamic call/block path and two sets of
   static instruction IDs (executed, pending).  Pair effectful frontiers
   using dft_block_rel.  Pending effect-free computations must retain their
   operand environments, not just their IDs.  A source GAS may be assigned
   a target occurrence or NONE, consistently with one partial injection.
   None of those annotations or their preservation are defined/assumed here.
   In particular, these single-machine probes give no uniform matching fact.
*)

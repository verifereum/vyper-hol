(* Our frame with more gas, for the sufficient-gas theorems.
 *
 * TOP-LEVEL:
 *   add_frame_gas      - es with g more gas for its top frame
 *   frame_inst_at      - a state of the top frame's run and its instruction
 *   frame_inst_raises  - the top frame's instruction raises an exception
 *   add_frame_gas_wf_state - add_frame_gas keeps wf_state
 *)
Theory frameGas
Ancestors
  callTrace vfmExecution vfmExecutionProp vfmContext list rich_list pair

(* es with g more gas for our (top) frame.  Every frame on the stack gets
   g more gas limit and every caller g more gas used, so the callers'
   unused gas is unchanged and wf_state's gas invariants (gas_stack_ok,
   wf_context) still hold. *)
Definition add_frame_gas_def:
  add_frame_gas g es =
    case es.contexts of
      [] => es
    | (c, rb) :: rest =>
        es with contexts :=
          (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g),
           rb) ::
          MAP (\(c, rb).
                 (c with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
                  rb)) rest
End

(* s is a state of es's frame (run_call's loop, our frame on top) and op
   is the instruction step runs there. *)
Definition frame_inst_at_def:
  frame_inst_at es s op <=>
    ?ctxt rb rest.
      RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
                 step a = (INL (), b)) es s /\
      s.contexts = (ctxt, rb) :: rest /\
      LENGTH s.contexts = LENGTH es.contexts /\
      case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
        SOME op' => op = op'
      | NONE => op = if LENGTH ctxt.msgParams.code <= ctxt.pc then Stop
                     else Invalid
End

(* Our frame's instruction op raises exc.  Stated on step_inst, not on
   step's result: step catches the exception and pops the frame, and in a
   nested frame frame_outcome tells a failure apart only from success.
   The raise must leave the stack at our depth: a precompile runs inside
   the CALL that pushed its frame, and its failure is the callee's. *)
Definition frame_inst_raises_def:
  frame_inst_raises es exc op <=>
    ?s s'.
      frame_inst_at es s op /\
      step_inst op s = (INR (SOME exc), s') /\
      LENGTH s'.contexts = LENGTH es.contexts
End

Theorem add_frame_gas_contexts:
  es.contexts = (c, rb) :: t ==>
  (add_frame_gas g es).contexts =
    (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g), rb) ::
    MAP (\x. (FST x with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
              SND x)) t
Proof
  rw[add_frame_gas_def] >> simp[MAP_EQ_f, FORALL_PROD]
QED

Theorem add_frame_gas_fields:
  (add_frame_gas g es).rollback = es.rollback /\
  (add_frame_gas g es).txParams = es.txParams /\
  (add_frame_gas g es).msdomain = es.msdomain
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem gas_stack_ok_add_frame_gas[local]:
  es.contexts = (c, rb) :: t /\ wf_context c /\
  EVERY (wf_context o FST) t /\ gas_stack_ok es ==>
  gas_stack_ok (add_frame_gas g es)
Proof
  rw[gas_stack_ok_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_MAP, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[unused_gas_def, listTheory.SUM, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[wf_context_def]
QED

Theorem add_frame_gas_wf_state:
  !g es. wf_state es ==> wf_state (add_frame_gas g es)
Proof
  rpt strip_tac >>
  Cases_on `es.contexts` >- fs[wf_state_def] >>
  PairCases_on `h` >>
  `gas_stack_ok (add_frame_gas g es)` by
    (irule gas_stack_ok_add_frame_gas >> fs[wf_state_def]) >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[wf_state_def, wf_context_def, all_accounts_def, stack_room_ok_def,
      outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
      add_frame_gas_fields, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[EVERY_MEM]
QED

Theorem add_frame_gas_calldata:
  !g es. (FST (HD (add_frame_gas g es).contexts)).msgParams.data =
         (FST (HD es.contexts)).msgParams.data
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem frame_inst_at_unique:
  frame_inst_at es s op /\ frame_inst_at es s op' ==> op = op'
Proof
  rw[frame_inst_at_def] >> gvs[] >>
  Cases_on `FLOOKUP ctxt.msgParams.parsed ctxt.pc` >> gvs[] >>
  Cases_on `LENGTH ctxt.msgParams.code <= ctxt.pc` >> gvs[]
QED

Theorem frame_inst_at_self:
  es.contexts <> [] /\
  (FST (HD es.contexts)).pc < LENGTH (FST (HD es.contexts)).msgParams.code /\
  next_opcode (FST (HD es.contexts)) = SOME op ==>
  frame_inst_at es es op
Proof
  Cases_on `es.contexts` >> simp[] >> PairCases_on `h` >>
  simp[frame_inst_at_def, next_opcode_def] >>
  strip_tac >> gvs[]
QED

Theorem frame_inst_at_prefix:
  RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
             step a = (INL (),b)) es es1 /\
  LENGTH es1.contexts = LENGTH es.contexts /\
  frame_inst_at es1 s op ==> frame_inst_at es s op
Proof
  rw[frame_inst_at_def] >> metis_tac[relationTheory.RTC_TRANS]
QED

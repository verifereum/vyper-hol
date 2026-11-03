(* Fuel-free execution inherits the instruction semantics of the open machine.
   Budgets are administrative; erasure never changes states or gas counters. *)
Theory dftOpenErase
Ancestors
  dftOpenFuel dftOpenMachine venomExecSemantics venomInst

Definition dft_fill_frame_def:
  dft_fill_frame k (DftCaller fn b bb inst s) = DftCaller fn k bb inst s
End

Definition dft_fill_control_def:
  (dft_fill_control k (DftEnter fn b s) = DftEnter fn k s) /\
  (dft_fill_control k (DftAt fn b bb s) = DftAt fn k bb s) /\
  (dft_fill_control k (DftDone r) = DftDone r)
End

Definition dft_fill_def:
  dft_fill k (DftOpen control stack n) =
    DftOpen (dft_fill_control k control) (MAP (dft_fill_frame k) stack) n
End

Definition dft_erase_def:
  dft_erase c = dft_fill 0 c
End

Definition dft_next_inf_def:
  dft_next_inf a ctx c = dft_erase (dft_open_next a ctx (dft_fill 1 c))
End

Theorem dft_fill_frame_twice[local,simp]:
  dft_fill_frame k (dft_fill_frame j f) = dft_fill_frame k f
Proof
  Cases_on `f` >> simp[dft_fill_frame_def]
QED

Theorem dft_fill_control_twice[local,simp]:
  dft_fill_control k (dft_fill_control j control) = dft_fill_control k control
Proof
  Cases_on `control` >> simp[dft_fill_control_def]
QED

Theorem dft_fill_twice[simp]:
  dft_fill k (dft_fill j c) = dft_fill k c
Proof
  Cases_on `c` >> simp[dft_fill_def, listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_erase_fill[simp]:
  dft_erase (dft_fill k c) = dft_erase c
Proof
  simp[dft_erase_def]
QED

Theorem dft_erase_idempotent[simp]:
  dft_erase (dft_erase c) = dft_erase c
Proof
  simp[dft_erase_def]
QED

Theorem dft_next_inf_canonical[simp]:
  dft_erase (dft_next_inf a ctx c) = dft_next_inf a ctx c
Proof
  simp[dft_next_inf_def]
QED

Theorem dft_fill_continue[local]:
  dft_fill_control k (dft_open_continue fn b bb inst before after) =
  dft_fill_control k (dft_open_continue fn j bb inst before after)
Proof
  simp[dft_open_continue_def] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  Cases_on `after.vs_halted` >> simp[dft_fill_control_def]
QED

Theorem dft_fill_deliver[local]:
  dft_fill k (dft_open_deliver fn b bb inst before stack n r) =
  dft_fill k (dft_open_deliver fn j bb inst before
    (MAP (dft_fill_frame h) stack) n r)
Proof
  Cases_on `r` >>
  simp[dft_open_deliver_def, dft_fill_def, dft_fill_continue,
       dft_fill_control_def, listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_fill_return[local]:
  dft_fill k (dft_open_return r stack n) =
  dft_fill k (dft_open_return r (MAP (dft_fill_frame j) stack) n)
Proof
  Cases_on `r` >> Cases_on `stack` >>
  simp[dft_open_return_def, dft_fill_def, dft_fill_control_def] >>
  Cases_on `h` >> simp[dft_fill_frame_def, dft_open_return_def] >>
  rename1 `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  Cases_on `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_fill_def, dft_fill_control_def, dft_fill_deliver]
QED

Theorem dft_fill_invoke[local]:
  dft_fill k (dft_open_invoke ctx fn b bb inst s stack n) =
  dft_fill k (dft_open_invoke ctx fn j bb inst s
    (MAP (dft_fill_frame h) stack) n)
Proof
  simp[dft_open_invoke_def] >> Cases_on `decode_invoke inst` >>
  simp[dft_fill_def, dft_fill_control_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >>
  simp[dft_fill_def, dft_fill_control_def] >>
  Cases_on `eval_operands x1 s` >>
  simp[dft_fill_def, dft_fill_control_def] >>
  rename1 `setup_callee callee args s` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_fill_frame_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_fill_next:
  ~dft_zero_entry c /\ 0 < j ==>
  dft_fill k (dft_open_next a ctx c) =
  dft_fill k (dft_open_next a ctx (dft_fill j c))
Proof
  Cases_on `c` >> Cases_on `d` >>
  simp[dft_zero_entry_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_fill_return]
  >- (Cases_on `n'` >> simp[] >> rpt strip_tac >>
      Cases_on `j` >> gvs[] >>
      Cases_on `lookup_block v.vs_current_bb i.fn_blocks` >>
      simp[dft_fill_def, dft_fill_control_def] >>
      rename1 `eval_phis s bb.bb_instructions` >>
      Cases_on `eval_phis s bb.bb_instructions` >>
      simp[dft_fill_def, dft_fill_control_def,
           listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]) >>
  rpt strip_tac >> Cases_on `get_instruction b v.vs_inst_idx` >>
  simp[dft_fill_def, dft_fill_control_def] >>
  rename1 `inst.inst_opcode = INVOKE` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- simp[dft_fill_invoke] >>
  Cases_on `inst.inst_opcode = GAS` >> simp[dft_fill_deliver] >>
  Cases_on `inst.inst_outputs` >>
  simp[dft_fill_def, dft_fill_control_def] >>
  Cases_on `t` >> simp[dft_fill_deliver, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_erase_next:
  ~dft_zero_entry c ==>
  dft_erase (dft_open_next a ctx c) = dft_next_inf a ctx (dft_erase c)
Proof
  simp[dft_next_inf_def, dft_erase_def] >>
  strip_tac >> irule dft_fill_next >> simp[]
QED

Theorem dft_erase_observe:
  dft_open_observe fn inst s (dft_erase c) <=> dft_open_observe fn inst s c
Proof
  Cases_on `c` >> Cases_on `d` >>
  simp[dft_open_observe_def, dft_erase_def, dft_fill_def, dft_fill_control_def]
QED

Theorem dft_next_inf_gas:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  dft_next_inf a ctx (DftOpen (DftAt fn b bb s) stack n) =
  dft_erase (DftOpen (DftAt fn 0 bb
    ((update_var out (a n) s) with vs_inst_idx := SUC s.vs_inst_idx))
    stack (SUC n))
Proof
  strip_tac >> simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       is_terminator_def, dft_erase_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_next_inf_gas_bad_arity:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = GAS /\ ~(?out. inst.inst_outputs = [out]) ==>
  dft_next_inf a ctx (DftOpen (DftAt fn b bb s) stack n) =
  DftOpen (DftDone (Error "read0 requires single output")) [] n
Proof
  strip_tac >>
  simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `inst.inst_outputs` >>
  gvs[dft_fill_def, dft_fill_control_def] >>
  Cases_on `t` >> gvs[dft_fill_def, dft_fill_control_def]
QED

Theorem dft_next_inf_entry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  dft_next_inf a ctx (DftOpen (DftEnter fn b s) stack n) =
  dft_erase (DftOpen (DftAt fn 0 bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) stack n)
Proof
  strip_tac >> simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_next_inf_invoke:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_next_inf a ctx (DftOpen (DftAt fn b bb s) stack n) =
  dft_erase (DftOpen (DftEnter callee 0 cs)
    (DftCaller fn 0 bb inst s :: stack) n)
Proof
  strip_tac >> simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_open_invoke_def, dft_erase_def, dft_fill_frame_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

Theorem dft_next_inf_return:
  inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  dft_next_inf a ctx
    (DftOpen (DftDone (IntRet ret cs))
      (DftCaller fn b bb inst caller :: stack) n) =
  dft_erase (DftOpen (DftAt fn 0 bb
    (after with vs_inst_idx := SUC caller.vs_inst_idx)) stack n)
Proof
  strip_tac >> simp[dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_fill_frame_def, dft_open_next_def, dft_open_return_def,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def, dft_erase_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, listTheory.MAP_EQ_f]
QED

(* Dynamic addresses are proof ghosts; projection is the fuel-free core. *)
Theory dftOccurrenceMachine
Ancestors
  dftOpenErase dftOpenMachine venomExecSemantics venomInst arithmetic list

Datatype:
  dft_occ_config = <| dft_occ_core : dft_open_config;
                      dft_occ_path : (num # num) list;
                      dft_occ_visit : num;
                      dft_occ_saved : ((num # num) list # num) list |>
End

Definition dft_occ_init_def:
  dft_occ_init c = <| dft_occ_core := c; dft_occ_path := [];
                     dft_occ_visit := 0; dft_occ_saved := [] |>
End

(* Classify an already computed transition. Only an actual call push can
   go from At/INVOKE to Enter; only a successful return goes Done to At. *)
Definition dft_occ_update_def:
  dft_occ_update c d =
    case (c.dft_occ_core, d) of
      (DftOpen (DftAt fn b bb s) stack n,
       DftOpen (DftEnter callee fuel cs) stack' n') =>
        (case get_instruction bb s.vs_inst_idx of
           SOME inst =>
             if inst.inst_opcode = INVOKE then
               c with <|dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit, inst.inst_id)];
                        dft_occ_visit := 0;
                        dft_occ_saved := (c.dft_occ_path, c.dft_occ_visit) :: c.dft_occ_saved|>
             else c with dft_occ_visit := SUC c.dft_occ_visit
         | NONE => c)
    | (DftOpen (DftDone r) stack n, DftOpen (DftAt fn b bb s) stack' n') =>
        (case c.dft_occ_saved of
           (path,visit)::saved => c with <|dft_occ_path := path;
               dft_occ_visit := visit; dft_occ_saved := saved|>
         | [] => c)
    | (_, DftOpen ctl [] n) => c with dft_occ_saved := []
    | _ => c
End

Definition dft_occ_next_def:
  dft_occ_next a ctx c =
    let d = dft_next_inf a ctx c.dft_occ_core in
    (dft_occ_update c d) with dft_occ_core := d
End

Definition dft_occ_event_def:
  dft_occ_event inst addr c <=>
    (?fn b bb s stack n.
       c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n /\
       get_instruction bb s.vs_inst_idx = SOME inst) /\
    addr = c.dft_occ_path ++ [(c.dft_occ_visit, inst.inst_id)]
End

Definition dft_occ_gas_event_def:
  dft_occ_gas_event inst addr c <=>
    dft_occ_event inst addr c /\ inst.inst_opcode = GAS /\
    ?out. inst.inst_outputs = [out]
End

Theorem dft_occ_next_projection[simp]:
  (dft_occ_next a ctx c).dft_occ_core = dft_next_inf a ctx c.dft_occ_core
Proof
  simp[dft_occ_next_def]
QED

Theorem dft_occ_iter_projection:
  !j c. (FUNPOW (dft_occ_next a ctx) j c).dft_occ_core =
    FUNPOW (dft_next_inf a ctx) j c.dft_occ_core
Proof
  Induct_on `j` >> simp[FUNPOW_SUC]
QED

Theorem dft_occ_push:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  dft_occ_next a ctx c = c with
    <| dft_occ_core := dft_erase (DftOpen (DftEnter callee 1 cs)
         (DftCaller fn 1 bb inst s :: MAP (dft_fill_frame 1) stack) n);
       dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit, inst.inst_id)];
       dft_occ_visit := 0;
       dft_occ_saved := (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved |>
Proof
  strip_tac >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_open_invoke_def, dft_occ_update_def,
       dft_erase_def]
QED

Theorem dft_occ_pop:
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller fn 0 bb inst caller :: stack) n /\
  c.dft_occ_saved = (path,visit)::saved /\
  inst.inst_opcode = INVOKE /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  dft_occ_next a ctx c = c with
    <| dft_occ_core := dft_erase (DftOpen (DftAt fn 1 bb
         (after with vs_inst_idx := SUC caller.vs_inst_idx))
         (MAP (dft_fill_frame 1) stack) n);
       dft_occ_path := path; dft_occ_visit := visit;
       dft_occ_saved := saved |>
Proof
  strip_tac >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_fill_frame_def, dft_open_next_def, dft_open_return_def,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_occ_update_def, dft_erase_def]
QED

Theorem dft_occ_terminator:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  is_terminator inst.inst_opcode /\ ~after.vs_halted /\
  step_inst_base inst s = OK after ==>
  dft_occ_next a ctx c = c with
    <| dft_occ_core := dft_erase (DftOpen (DftEnter fn 1 after)
         (MAP (dft_fill_frame 1) stack) n);
       dft_occ_visit := SUC c.dft_occ_visit |>
Proof
  strip_tac >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       dft_occ_update_def, dft_erase_def]
QED

Theorem dft_occ_event_address:
  dft_occ_event inst addr c ==>
  addr = c.dft_occ_path ++ [(c.dft_occ_visit, inst.inst_id)]
Proof
  simp[dft_occ_event_def]
QED

Theorem dft_occ_event_deterministic:
  dft_occ_event inst addr c /\ dft_occ_event inst' addr' c ==>
  inst = inst' /\ addr = addr'
Proof
  simp[dft_occ_event_def] >> rpt strip_tac >> gvs[]
QED

Definition dft_occ_frame_ok_def:
  dft_occ_frame_ok (DftCaller fn b bb inst s) <=> inst.inst_opcode = INVOKE
End

Definition dft_occ_aligned_def:
  dft_occ_aligned c <=>
    case c.dft_occ_core of DftOpen ctl stack n =>
      LENGTH c.dft_occ_saved = LENGTH stack /\ EVERY dft_occ_frame_ok stack
End

Theorem dft_occ_frame_ok_fill[simp]:
  dft_occ_frame_ok (dft_fill_frame b frame) = dft_occ_frame_ok frame
Proof
  Cases_on `frame` >> simp[dft_occ_frame_ok_def, dft_fill_frame_def]
QED

Theorem dft_occ_frames_ok_fill[simp]:
  EVERY dft_occ_frame_ok (MAP (dft_fill_frame b) stack) = EVERY dft_occ_frame_ok stack
Proof
  Induct_on `stack` >> simp[]
QED

Theorem dft_occ_next_aligned:
  dft_occ_aligned c ==> dft_occ_aligned (dft_occ_next a ctx c)
Proof
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl`
  >- suspend "enter"
  >- suspend "at"
  >- suspend "done"
QED

Resume dft_occ_next_aligned[enter]:
  rename1 `c.dft_occ_core = DftOpen (DftEnter fn budget s) stack n` >>
      simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
      Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_aligned_def] >>
      rename1 `lookup_block _ _ = SOME bb` >>
      Cases_on `eval_phis s bb.bb_instructions` >>
      Cases_on `stack` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_aligned_def]
QED

Resume dft_occ_next_aligned[at]:
  rename1 `c.dft_occ_core = DftOpen (DftAt fn budget bb s) stack n` >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
           dft_occ_update_def] >>
      rename1 `get_instruction _ _ = SOME inst` >>
      Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
            dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
          Cases_on `decode_invoke inst` >>
          simp[dft_open_invoke_def, dft_fill_def, dft_fill_control_def,
            dft_occ_update_def] >>
          rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
          Cases_on `lookup_function pair0 ctx.ctx_functions` >>
          simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def] >>
          rename1 `lookup_function _ _ = SOME callee` >>
          Cases_on `eval_operands pair1 s` >>
          simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def] >>
          rename1 `eval_operands _ _ = SOME args` >>
          Cases_on `setup_callee callee args s` >>
          simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_frame_ok_def]) >>
      Cases_on `inst.inst_opcode = GAS`
      >- (simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
            dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
          Cases_on `inst.inst_outputs` >>
          simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def] >>
          rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
          Cases_on `stack` >>
          simp[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
            dft_fill_def, dft_fill_control_def, dft_occ_update_def]) >>
      simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
      Cases_on `step_inst_base inst s` >> Cases_on `stack` >>
      simp[dft_open_deliver_def, dft_open_continue_def,
        dft_fill_def, dft_fill_control_def, dft_occ_update_def] >>
      rpt (IF_CASES_TAC >> simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def])
QED

Resume dft_occ_next_aligned[done]:
  Cases_on `e` >> Cases_on `stack` >>
      simp[dft_occ_aligned_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
        dft_open_return_def, dft_occ_update_def] >>
      rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
      Cases_on `frame` >>
      Cases_on `c.dft_occ_saved` >>
      simp[dft_fill_frame_def, dft_occ_frame_ok_def] >>
      rename1 `c.dft_occ_saved = pair::saved` >> PairCases_on `pair` >>
      strip_tac >>
      rename1 `bind_outputs inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state caller cs))` >>
      Cases_on `bind_outputs inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state caller cs))` >>
      simp[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
        dft_fill_def, dft_fill_control_def, dft_occ_update_def]
QED

Finalise dft_occ_next_aligned


Theorem dft_occ_init_aligned[simp]:
  dft_occ_aligned (dft_occ_init (DftOpen ctl [] n))
Proof
  simp[dft_occ_init_def, dft_occ_aligned_def]
QED

Theorem dft_occ_iter_aligned:
  !j c. dft_occ_aligned c ==>
    dft_occ_aligned (FUNPOW (dft_occ_next a ctx) j c)
Proof
  Induct_on `j` >> simp[FUNPOW_SUC, dft_occ_next_aligned]
QED

Theorem dft_occ_block_id_injective:
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  get_instruction bb p = SOME inst /\ get_instruction bb q = SOME inst' /\
  inst.inst_id = inst'.inst_id ==> p = q
Proof
  simp[get_instruction_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  `EL p (MAP (\i. i.inst_id) bb.bb_instructions) =
   EL q (MAP (\i. i.inst_id) bb.bb_instructions)` by simp[EL_MAP] >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`p`, `q`] mp_tac) >> simp[]
QED

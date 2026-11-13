(*
 * A gas-origin pointer focus gives O1 safety up to the gas cut.
 *
 * gas_origin_ptr_focus checks, along one path from the unit's entry, the
 * memory and pointer conditions of every instruction it runs, and of every
 * call it completes, up to a state where its marks are used up.  The run
 * is deterministic, so every reachable state that has popped fewer gas
 * readings than the focus has marks lies on that path or inside a call it
 * completes: o1_safe_upto holds at the cut MIN (LENGTH marks) (LENGTH
 * readings).  Past the readings a GAS reads 0w without popping, so a
 * focus longer than the readings only covers the states before they run
 * out.
 *
 * TOP-LEVEL:
 *   gas_origin_ptr_focus_o1_safe_upto -- the bridge
 *)
Theory fragGasOriginPtrSafeUpto
Ancestors
  fragGasOriginPtr fragGasFocus fragExec o1SafeUpto ptrSafeRun memSafeRun
  ptrDiscipline contextRawReachable contextCodegenRel
  concretizePtrCoverageStaticMemReachability lowerDloadPtrRawReachable
  gasCount gasEvents gasOracleReplay unitMemInv unitTransformDefs
  lowerDloadDefs contextCodegenRelProps venomExecSemantics venomExecProofs
  venomInstProofs venomInst venomState finite_map list arithmetic

(* ===== Readings ===== *)

Theorem step_inst_readings_le[local]:
  (step_inst fuel ctx inst s = OK t ==>
   LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings) /\
  (step_inst fuel ctx inst s = IntRet v t ==>
   LENGTH t.vs_gas_readings <= LENGTH s.vs_gas_readings)
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`] mp_tac (cj 1 gas_count_suffix) >>
  gvs[gas_count_suffix_def]
QED

Theorem enters_block_readings[local]:
  enters_block fn s s1 ==> s1.vs_gas_readings = s.vs_gas_readings
Proof
  rw[enters_block_def] >> imp_res_tac gas_count_phis_ok >> simp[]
QED

(* ===== The invariant ===== *)

(* A state on the focus, with as many marks left as the readings it has
   still to pop: the focus started with b marks at vs's readings. *)
Definition focus_at_def:
  focus_at D lo explicit ctx vs b fn PG G tn s <=>
    ?m out.
      gas_origin_ptr_focus (D, lo, explicit, ctx, fn, PG) (s, G, tn) m out /\
      LENGTH vs.vs_gas_readings + LENGTH m = b + LENGTH s.vs_gas_readings
End

(* A state whose run, from inside its block, is pointer- and memory-safe
   at every fuel: the states of a call the focus completes. *)
Definition run_safe_def:
  run_safe D lo ctx fn PG G tn s <=>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s /\ mem_safe_run fuel ctx fn s
End

(* What a run_safe state's callers carry, like ptrSafeRun's frames_ok: where
   the frame returns, the caller is back at Q (on the focus, for the call the
   focus completes), or on a safe run whose own callers carry the same. *)
Definition frames_cont_def:
  (frames_cont Q D lo ctx [] fn PG G tn s <=> T) /\
  (frames_cont Q D lo ctx (f::stk) fn PG G tn s <=>
    !fuel ret s_end s'.
      frame_run fuel ctx fn s = IntRet ret s_end /\
      bind_outputs f.cf_inst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
        SOME s' ==>
      Q f.cf_fn f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (SND (ghost_run fuel ctx fn PG G tn s) with t_var :=
           DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) \/
      run_safe D lo ctx f.cf_fn f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (SND (ghost_run fuel ctx fn PG G tn s) with t_var :=
           DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
      frames_cont Q D lo ctx stk f.cf_fn f.cf_params
        (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
        (SND (ghost_run fuel ctx fn PG G tn s) with t_var :=
           DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
        (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))
End

Theorem frames_cont_transfer[local]:
  frames_cont Q D lo ctx stk fn PG G tn s ==>
  (!fuel ret s_end.
     frame_run fuel ctx fn2 s2 = IntRet ret s_end ==>
     ?fuel1. frame_run fuel1 ctx fn s = IntRet ret s_end /\
             SND (ghost_run fuel1 ctx fn PG G tn s) =
             SND (ghost_run fuel ctx fn2 PG2 G2 tn2 s2)) ==>
  frames_cont Q D lo ctx stk fn2 PG2 G2 tn2 s2
Proof
  Cases_on `stk` >> simp[frames_cont_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> metis_tac[]
QED

(* Entering a block: the run and the ghost from its entry are the ones from
   past its PHIs, and so is a run safe at every fuel. *)
Theorem enters_block_run[local]:
  !fn s s1 ctx D lo PG G tn fuel.
    enters_block fn s s1 ==>
    run_blocks (SUC fuel) ctx fn s = frame_run fuel ctx fn s1 /\
    ghost_blocks (SUC fuel) ctx fn PG G tn s =
      ghost_run fuel ctx fn PG G tn s1 /\
    ((!fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s /\
             mem_safe_blocks fuel ctx fn s) ==>
     run_safe D lo ctx fn PG G tn s1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (fn th => simp[th]) frame_run_enters_block >>
  rw[run_safe_def] >>
  metis_tac[ptr_safe_enters_block, mem_safe_enters_block]
QED

(* An INVOKE whose callee run returns: at any larger fuel the step and its
   ghost are the ones the return gives. *)
Theorem invoke_return[local]:
  !ivk nm ops ctx callee s args cs s1 fuel ret s_end s' M PG G tn.
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  frame_run fuel ctx callee s1 = IntRet ret s_end /\
  bind_outputs ivk.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' /\
  SUC fuel <= M ==>
  step_inst M ctx ivk s = OK s' /\
  ghost_step M ctx PG G tn ivk s =
    (DRESTRICT G (COMPL (set ivk.inst_outputs)),
     SND (ghost_run fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) s1)
       with t_var := DRESTRICT tn.t_var (COMPL (set ivk.inst_outputs)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_then (qspecl_then [`ctx`, `D`, `lo`, `MAP (op_prov G) ops`, `FEMPTY`,
                           `tn with t_var := FEMPTY`, `fuel`] strip_assume_tac)
    enters_block_run >>
  `run_blocks (SUC fuel) ctx callee cs = IntRet ret s_end` by simp[] >>
  `run_blocks M ctx callee cs = IntRet ret s_end` by
    (qspecl_then [`SUC fuel`, `M`, `ctx`, `callee`, `cs`,
                  `IntRet ret s_end`] mp_tac (cj 3 fuel_mono) >>
     simp[]) >>
  `ghost_blocks M ctx callee (MAP (op_prov G) ops) FEMPTY
     (tn with t_var := FEMPTY) cs =
   ghost_blocks (SUC fuel) ctx callee (MAP (op_prov G) ops) FEMPTY
     (tn with t_var := FEMPTY) cs` by
    (irule (cj 3 ghost_fuel_mono_up) >> simp[]) >>
  conj_tac >- (simp[Once step_inst_def] >> gvs[]) >>
  drule_all ghost_step_invoke >> simp[]
QED

(* ===== Steps from a safe run ===== *)

Theorem run_safe_next[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst f0 ctx inst s = OK s' /\
  run_safe D lo ctx fn PG G tn s /\
  frames_cont Q D lo ctx stk fn PG G tn s ==>
  run_safe D lo ctx fn PG (step_prov PG G inst s') (step_taint inst s s' tn)
    (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
  frames_cont Q D lo ctx stk fn PG (step_prov PG G inst s')
    (step_taint inst s s' tn) (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `!fuel. step_inst fuel ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `!fuel. ghost_step fuel ctx PG G tn inst s =
          (step_prov PG G inst s', step_taint inst s s' tn)` by
    metis_tac[ghost_step_non_invoke] >>
  conj_tac
  >- (qpat_x_assum `run_safe _ _ _ _ _ _ _ _` mp_tac >>
      simp[run_safe_def, ptr_safe_run_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `fuel` strip_assume_tac) >>
      qspecl_then [`D`, `lo`, `fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`,
                   `s`, `inst`, `s'`] mp_tac ptr_safe_block_step >>
      (impl_tac >- simp[]) >> disch_then (fn th => fs[th]) >>
      qspecl_then [`fuel`, `ctx`, `fn`, `s`, `bb`, `inst`, `s'`] mp_tac
        mem_safe_run_step >>
      (impl_tac >- simp[]) >> disch_then (fn th => fs[th]) >>
      qpat_x_assum `!fuel. ghost_step _ _ _ _ _ _ _ = _`
        (qspec_then `fuel` (fn th => fs[th]))) >>
  drule_then irule frames_cont_transfer >>
  rpt strip_tac >> qexists_tac `fuel` >>
  qspecl_then [`fuel`, `ctx`, `fn`, `bb`, `s`, `inst`, `s'`] mp_tac
    block_run_step >>
  qspecl_then [`fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`, `inst`, `s'`]
    mp_tac ghost_block_step >>
  gvs[frame_run_def, ghost_run_def]
QED

Theorem run_safe_jump[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ step_inst f0 ctx inst s = OK s' /\
  ~s'.vs_halted /\ enters_block fn s' s1 /\
  run_safe D lo ctx fn PG G tn s /\
  frames_cont Q D lo ctx stk fn PG G tn s ==>
  run_safe D lo ctx fn PG (entry_prov fn s' G) (entry_taint_vars fn s' tn) s1 /\
  frames_cont Q D lo ctx stk fn PG (entry_prov fn s' G)
    (entry_taint_vars fn s' tn) s1
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `!fuel. step_inst fuel ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  `!fuel. run_blocks (SUC fuel) ctx fn s' = frame_run fuel ctx fn s1 /\
          ghost_blocks (SUC fuel) ctx fn PG (entry_prov fn s' G)
            (entry_taint_vars fn s' tn) s' =
          ghost_run fuel ctx fn PG (entry_prov fn s' G)
            (entry_taint_vars fn s' tn) s1` by
    metis_tac[enters_block_run] >>
  conj_tac
  >- (irule (cj 3 (SPEC_ALL enters_block_run)) >>
      qexists_tac `s'` >> simp[] >> gen_tac >>
      qpat_x_assum `run_safe _ _ _ _ _ _ _ _` mp_tac >>
      simp[run_safe_def, ptr_safe_run_def] >>
      disch_then (qspec_then `fuel` strip_assume_tac) >>
      conj_tac
      >- (qspecl_then [`D`, `lo`, `fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`,
                       `s`, `inst`, `s'`] mp_tac ptr_safe_block_terminator >>
          simp[]) >>
      metis_tac[mem_safe_run_terminator]) >>
  drule_then irule frames_cont_transfer >>
  rpt strip_tac >> qexists_tac `SUC fuel` >>
  qspecl_then [`SUC fuel`, `ctx`, `fn`, `bb`, `s`, `inst`, `s'`] mp_tac
    block_run_terminator >>
  qspecl_then [`SUC fuel`, `ctx`, `fn`, `PG`, `G`, `tn`, `bb`, `s`, `inst`,
               `s'`] mp_tac ghost_block_terminator >>
  gvs[frame_run_def, ghost_run_def]
QED

Theorem run_safe_call[local]:
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ivk /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  run_safe D lo ctx caller PG G tn s /\
  frames_cont Q D lo ctx stk caller PG G tn s ==>
  run_safe D lo ctx callee (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) s1 /\
  frames_cont Q D lo ctx
    (<| cf_fn := caller; cf_inst := ivk; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    callee (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) s1
Proof
  strip_tac >>
  `~revert_forward_at bb s.vs_inst_idx` by
    (strip_tac >> drule_all revert_forward_at_opcode >> simp[]) >>
  `!fuel. ptr_safe_block D lo fuel ctx caller PG G tn bb s /\
          mem_safe_run fuel ctx caller s` by
    (qpat_x_assum `run_safe _ _ _ _ _ _ _ _` mp_tac >>
     simp[run_safe_def, ptr_safe_run_def]) >>
  `!fuel. ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops) FEMPTY
            (tn with t_var := FEMPTY) cs /\
          mem_safe_blocks fuel ctx callee cs` by
    (gen_tac >>
     `ptr_safe_step D lo fuel ctx caller PG G tn ivk s` by
       metis_tac[ptr_safe_block_head] >>
     `mem_safe_step fuel ctx ivk s` by metis_tac[mem_safe_run_head] >>
     drule_all_then assume_tac ptr_safe_step_invoke >>
     drule_all_then assume_tac mem_safe_step_invoke >> gvs[]) >>
  conj_tac >- metis_tac[enters_block_run] >>
  simp[frames_cont_def] >> rpt gen_tac >> strip_tac >> disj2_tac >>
  qmatch_goalsub_abbrev_tac `run_safe D lo ctx caller PG GR tnR s2` >>
  `!M. SUC fuel <= M ==>
       step_inst M ctx ivk s = OK s' /\
       ghost_step M ctx PG G tn ivk s = (GR, tnR)` by
    (rpt strip_tac >> drule_all invoke_return >>
     simp[Abbr `GR`, Abbr `tnR`]) >>
  `s'.vs_current_bb = s.vs_current_bb` by
    (`step_inst (SUC fuel) ctx ivk s = OK s'` by simp[] >>
     drule step_preserves_control_flow >> simp[is_terminator_def]) >>
  `~is_terminator ivk.inst_opcode` by simp[is_terminator_def] >>
  conj_tac
  >- (`!f. ptr_safe_block D lo f ctx caller PG GR tnR bb s2 /\
           mem_safe_run f ctx caller s2` suffices_by
        simp[run_safe_def, ptr_safe_run_def, Abbr `s2`] >>
      gen_tac >> simp[Abbr `s2`] >>
      qpat_assum `!M. _ ==> _` (qspec_then `MAX f (SUC fuel)` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `!fuel. ptr_safe_block _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `MAX f (SUC fuel)` strip_assume_tac) >>
      qspecl_then [`D`, `lo`, `MAX f (SUC fuel)`, `ctx`, `caller`, `PG`,
                   `G`, `tn`, `bb`, `s`, `ivk`, `s'`] mp_tac
        ptr_safe_block_step >>
      (impl_tac >- simp[]) >> disch_then (fn th => fs[th]) >>
      qspecl_then [`MAX f (SUC fuel)`, `ctx`, `caller`, `s`, `bb`, `ivk`,
                   `s'`] mp_tac mem_safe_run_step >>
      (impl_tac >- simp[]) >> disch_then (fn th => fs[th]) >>
      qpat_x_assum `ghost_step _ _ _ _ _ _ _ = _` (fn th => fs[th]) >>
      conj_tac
      >- (irule (cj 2 ptr_safe_fuel_mono_down) >>
          qexists_tac `MAX f (SUC fuel)` >> simp[]) >>
      irule mem_safe_run_fuel_mono_down >>
      qexists_tac `MAX f (SUC fuel)` >> simp[]) >>
  drule_then irule frames_cont_transfer >>
  qx_gen_tac `f` >> rpt gen_tac >> strip_tac >>
  qexists_tac `MAX f (SUC fuel)` >>
  qpat_x_assum `!M. _ ==> _` (qspec_then `MAX f (SUC fuel)` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `frame_run (MAX f (SUC fuel)) ctx caller s2 =
   frame_run f ctx caller s2` by
    (irule frame_run_fuel_mono >> simp[]) >>
  `ghost_run (MAX f (SUC fuel)) ctx caller PG GR tnR s2 =
   ghost_run f ctx caller PG GR tnR s2` by
    (irule ghost_run_fuel_mono_up >> simp[]) >>
  qspecl_then [`MAX f (SUC fuel)`, `ctx`, `caller`, `bb`, `s`, `ivk`,
               `s'`] mp_tac block_run_step >>
  qspecl_then [`MAX f (SUC fuel)`, `ctx`, `caller`, `PG`, `G`, `tn`, `bb`,
               `s`, `ivk`, `s'`] mp_tac ghost_block_step >>
  gvs[frame_run_def, ghost_run_def, Abbr `s2`]
QED

Theorem run_safe_ret[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME rinst /\
  step_inst fuel ctx rinst s = IntRet ret s_end /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) =
    SOME s' /\
  frames_cont Q D lo ctx (f::stk) fn PG G tn s ==>
  Q f.cf_fn f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) \/
  run_safe D lo ctx f.cf_fn f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
  frames_cont Q D lo ctx stk f.cf_fn f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `frame_run fuel ctx fn s = IntRet ret s_end` by
    (simp[frame_run_def, block_run_def] >> simp[Once exec_block_def]) >>
  `ghost_run fuel ctx fn PG G tn s = (G, tn)` by
    (simp[ghost_run_def] >> metis_tac[ghost_block_intret]) >>
  qpat_x_assum `frames_cont _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[frames_cont_def] >> disch_then drule_all >> simp[]
QED

(* ===== Steps from the focus ===== *)

Theorem focus_at_marks[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\ k <= b ==>
  ?m out.
    gas_origin_ptr_focus (D, lo, explicit, ctx, fn, PG) (s, G, tn) m out /\
    LENGTH vs.vs_gas_readings + LENGTH m = b + LENGTH s.vs_gas_readings /\
    m <> []
Proof
  rw[focus_at_def, gas_cut_def] >> qexistsl_tac [`m`, `out`] >> simp[] >>
  strip_tac >> gvs[] >> decide_tac
QED

(* Under the cut the focus goes on: an edge whose end is on the focus while
   the cut holds there, or a descent into the INVOKE's callee. *)
Theorem focus_at_first[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings ==>
  (?left mid G1 tn1.
     gas_origin_ptr_edge (D, lo, explicit, ctx, fn, PG) (s, G, tn) left
       (OK mid, G1, tn1) /\
     (gas_cut k vs mid ==> focus_at D lo explicit ctx vs b fn PG G1 tn1 mid)) \/
  (?bb inst name ops callee entered.
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst /\
     inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name, ops) /\
     gas_invoke_entry (ctx, fn) s callee entered /\
     ptr_inst_ok D lo 0 ctx fn G tn inst s /\
     focus_at D lo explicit ctx vs b callee (MAP (op_prov G) ops) FEMPTY
       (tn with t_var := FEMPTY) entered)
Proof
  strip_tac >> drule_all focus_at_marks >> strip_tac >>
  drule_then (qspecl_then [`D`, `lo`, `explicit`, `ctx`, `fn`, `PG`, `s`, `G`,
                           `tn`] mp_tac) gas_origin_ptr_focus_first >>
  simp[] >> strip_tac
  >- (disj1_tac >> qexistsl_tac [`left`, `mid`, `G1`, `tn1`] >> simp[] >>
      strip_tac >> simp[focus_at_def] >> qexistsl_tac [`right`, `out`] >>
      simp[] >> drule gas_origin_ptr_edge_ok_readings >> strip_tac >>
      gvs[gas_cut_def] >> decide_tac) >>
  disj2_tac >>
  qexistsl_tac [`bb`, `inst`, `name`, `ops`, `callee`, `entered`] >>
  simp[focus_at_def] >> drule gas_invoke_entry_readings >> strip_tac >>
  qexistsl_tac [`m`, `out`] >> simp[]
QED

Theorem focus_at_not_phi[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings ==>
  ?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
            get_instruction bb s.vs_inst_idx = SOME inst /\
            inst.inst_opcode <> PHI
Proof
  strip_tac >> drule_all focus_at_first >> strip_tac
  >- metis_tac[gas_origin_ptr_edge_not_phi] >>
  qexistsl_tac [`bb`, `inst`] >> simp[]
QED

(* A focus state at a block's start runs no PHI there, so entering the
   block changes neither the state nor the ghost. *)
Theorem focus_at_block_start[local]:
  !D lo explicit ctx vs b fn PG G tn s k s1.
    focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\
    k <= b /\ k <= LENGTH vs.vs_gas_readings /\
    s.vs_inst_idx = 0 /\ enters_block fn s s1 ==>
    s1 = s /\ entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  rpt gen_tac >> strip_tac >> drule_all focus_at_not_phi >> strip_tac >>
  gvs[enters_block_def, entry_prov_def, entry_taint_vars_def] >>
  Cases_on `bb.bb_instructions` >> gvs[get_instruction_def] >>
  gvs[eval_phis_def, phi_prefix_length_def, phis_prov_def, phis_taint_def] >>
  simp[venom_state_component_equality, taint_component_equality]
QED

Theorem focus_at_next[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst f0 ctx inst s = OK s' /\
  gas_cut k vs (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  focus_at D lo explicit ctx vs b fn PG (step_prov PG G inst s')
    (step_taint inst s s' tn) (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `gas_cut k vs s` by
    (drule (cj 1 step_inst_readings_le) >> fs[gas_cut_def] >> decide_tac) >>
  `!fe. step_inst fe ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  `!fe. ghost_step fe ctx PG G tn inst s =
        (step_prov PG G inst s', step_taint inst s s' tn)` by
    metis_tac[ghost_step_non_invoke] >>
  drule_all focus_at_first >> strip_tac >> gvs[] >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def]
QED

Theorem focus_at_block[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ step_inst f0 ctx inst s = OK s' /\
  ~s'.vs_halted /\ enters_block fn s' s1 /\ gas_cut k vs s1 ==>
  focus_at D lo explicit ctx vs b fn PG (entry_prov fn s' G)
    (entry_taint_vars fn s' tn) s1
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `gas_cut k vs s'` by
    (qpat_x_assum `gas_cut _ _ s1` mp_tac >>
     drule enters_block_readings >> simp[gas_cut_def]) >>
  `gas_cut k vs s` by
    (drule (cj 1 step_inst_readings_le) >> fs[gas_cut_def] >> decide_tac) >>
  `!fe. step_inst fe ctx inst s = OK s'` by
    metis_tac[step_inst_non_invoke_fuel] >>
  drule_all focus_at_first >> strip_tac >> gvs[] >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
  gvs[exit_result_def]
  >~ [`jump_to _ _`]
  >- (`(jump_to lbl s).vs_inst_idx = 0` by simp[jump_to_def] >>
      qspecl_then [`D`, `lo`, `explicit`, `ctx`, `vs`, `b`, `fn`, `PG`, `G`,
                   `tn`, `jump_to lbl s`, `k`, `s1`] mp_tac
        focus_at_block_start >>
      simp[] >> strip_tac >> gvs[])
  >~ [`jump_to _ _`]
  >- (`(jump_to lbl s).vs_inst_idx = 0` by simp[jump_to_def] >>
      qspecl_then [`D`, `lo`, `explicit`, `ctx`, `vs`, `b`, `fn`, `PG`, `G`,
                   `tn`, `jump_to lbl s`, `k`, `s1`] mp_tac
        focus_at_block_start >>
      simp[] >> strip_tac >> gvs[])
  >> gvs[enters_block_def]
QED

(* The call a focus edge completes: its callee's states are on a safe run,
   and its return lands where the edge ends. *)
Theorem focus_call_frames[local]:
  !Q D lo ctx caller PG G tn s ivk nm ops callee args cs s1 fe t stk.
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\
  step_inst fe ctx ivk s = OK t /\
  Q caller PG (FST (ghost_step fe ctx PG G tn ivk s))
    (SND (ghost_step fe ctx PG G tn ivk s))
    (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  frames_cont Q D lo ctx
    (<| cf_fn := caller; cf_inst := ivk; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    callee (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) s1
Proof
  rpt gen_tac >> strip_tac >> simp[frames_cont_def] >> rpt gen_tac >>
  strip_tac >> disj1_tac >>
  `SUC fuel <= MAX fe (SUC fuel)` by simp[] >>
  drule_all invoke_return >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  `step_inst (MAX fe (SUC fuel)) ctx ivk s = OK t` by
    (qspecl_then [`fe`, `MAX fe (SUC fuel)`, `ctx`, `ivk`, `s`, `OK t`]
       mp_tac (cj 1 fuel_mono) >> simp[]) >>
  `ghost_step fe ctx PG G tn ivk s =
   ghost_step (MAX fe (SUC fuel)) ctx PG G tn ivk s` by
    (irule EQ_SYM >> irule (cj 1 ghost_fuel_mono_up) >> simp[]) >>
  `s' = t` by
    (qpat_x_assum `step_inst (MAX _ _) _ _ _ = OK s'` mp_tac >> simp[]) >>
  gvs[]
QED

Theorem focus_at_call[local]:
  focus_at D lo explicit ctx vs b caller PG G tn s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings /\
  lookup_block s.vs_current_bb caller.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ivk /\
  ivk.inst_opcode = INVOKE /\ decode_invoke ivk = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ gas_cut k vs s1 ==>
  focus_at D lo explicit ctx vs b callee (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) s1 \/
  run_safe D lo ctx callee (MAP (op_prov G) ops) FEMPTY
    (tn with t_var := FEMPTY) s1 /\
  frames_cont
    (\f P g u c. gas_cut k vs c ==> focus_at D lo explicit ctx vs b f P g u c)
    D lo ctx
    (<| cf_fn := caller; cf_inst := ivk; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    callee (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) s1
Proof
  strip_tac >>
  `gas_cut k vs s` by
    (imp_res_tac enters_block_readings >>
     imp_res_tac gas_setup_callee_readings >> gvs[gas_cut_def]) >>
  drule_all focus_at_first >> strip_tac
  >- (disj2_tac >> drule gas_origin_ptr_edge_common_fuel >> strip_tac >>
      gvs[exit_result_def, is_terminator_def] >>
      rpt (qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o GSYM)) >>
      gvs[exit_result_def] >>
      `~revert_forward_at bb s.vs_inst_idx` by
        (strip_tac >> drule_all revert_forward_at_opcode >> simp[]) >>
      gvs[] >>
      `?ret se. run_blocks fuel ctx callee cs = IntRet ret se` by
        (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
         simp[Once step_inst_def, AllCaseEqs()] >> metis_tac[]) >>
      `!e. run_blocks fuel ctx callee cs <> Error e` by simp[] >>
      conj_tac
      >- (irule (cj 3 (SPEC_ALL enters_block_run)) >>
          qexists_tac `cs` >> simp[] >> gen_tac >>
          drule_all_then assume_tac ptr_safe_step_invoke >>
          drule_all_then assume_tac mem_safe_step_invoke >> gvs[] >>
          conj_tac
          >- (irule ptr_safe_blocks_all_fuel >> qexists_tac `fuel` >>
              simp[]) >>
          irule mem_safe_blocks_all_fuel >> qexists_tac `fuel` >> simp[]) >>
      qpat_x_assum `(_, _) = ghost_step _ _ _ _ _ _ _`
        (assume_tac o GSYM) >>
      qspecl_then [`\f P g u c. gas_cut k vs c ==>
                      focus_at D lo explicit ctx vs b f P g u c`,
                   `D`, `lo`, `ctx`, `caller`, `PG`, `G`, `tn`, `s`, `inst`,
                   `nm`, `ops`, `callee`, `args`, `cs`, `s1`, `fuel`, `t`,
                   `stk`] mp_tac focus_call_frames >>
      simp[]) >>
  disj1_tac >> gvs[gas_invoke_entry_def, enters_block_def]
QED

Theorem focus_at_not_ret[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME rinst /\
  step_inst fuel ctx rinst s = IntRet ret s_end ==> F
Proof
  strip_tac >> drule step_inst_intret_not_invoke >> strip_tac >>
  `!fe. step_inst fe ctx rinst s = IntRet ret s_end` by
    metis_tac[step_inst_non_invoke_fuel] >>
  drule_all focus_at_first >> strip_tac >> gvs[] >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >> gvs[exit_result_def]
QED

(* ===== Every reachable state under the cut ===== *)

Theorem frame_reachable_focus[local]:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    !D lo explicit b k.
      EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
      (!name efn lbl.
         ctx.ctx_entry = SOME name /\
         lookup_function name ctx.ctx_functions = SOME efn /\
         fn_entry_label efn = SOME lbl ==>
         focus_at D lo explicit ctx vs0 b efn [] FEMPTY entry_taint
           (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                        vs_inst_idx := 0 |>)) /\
      k <= b /\ k <= LENGTH vs0.vs_gas_readings /\ gas_cut k vs0 s ==>
      focus_at D lo explicit ctx vs0 b fn PG G tn s \/
      run_safe D lo ctx fn PG G tn s /\
      frames_cont
        (\f P g u c. gas_cut k vs0 c ==>
                     focus_at D lo explicit ctx vs0 b f P g u c)
        D lo ctx stk fn PG G tn s
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >- (disj1_tac >> first_x_assum drule_all >> strip_tac >>
      drule enters_block_readings >> strip_tac >>
      qspecl_then [`D`, `lo`, `explicit`, `ctx`, `vs0`, `b`, `fn`, `[]`,
                   `FEMPTY`, `entry_taint`,
                   `vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                                vs_inst_idx := 0 |>`, `k`, `s`] mp_tac
        focus_at_block_start >>
      fs[gas_cut_def] >> strip_tac >> gvs[]) >>
  `!g. MEM g ctx.ctx_functions ==> ALL_DISTINCT (fn_labels g)` by
    fs[EVERY_MEM] >>
  qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o MATCH_MP frame_reachable_functions_member)
  >- (`?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
            get_instruction bb s.vs_inst_idx = SOME inst` by
        metis_tac[active_inst_block_lookup] >>
      `gas_cut k vs0 s` by
        (drule (cj 1 step_inst_readings_le) >> fs[gas_cut_def] >>
         decide_tac) >>
      first_x_assum (qspecl_then [`D`, `lo`, `explicit`, `b`, `k`] mp_tac) >>
      simp[] >> strip_tac
      >- (disj1_tac >> drule_all focus_at_next >> simp[]) >>
      disj2_tac >> drule_all run_safe_next >> simp[])
  >- (`?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
            get_instruction bb s.vs_inst_idx = SOME inst` by
        metis_tac[active_inst_block_lookup] >>
      `gas_cut k vs0 s` by
        (imp_res_tac enters_block_readings >>
         imp_res_tac (cj 1 step_inst_readings_le) >> gvs[gas_cut_def] >>
         decide_tac) >>
      first_x_assum (qspecl_then [`D`, `lo`, `explicit`, `b`, `k`] mp_tac) >>
      simp[] >> strip_tac
      >- (disj1_tac >> drule_all focus_at_block >> simp[]) >>
      disj2_tac >> drule_all run_safe_jump >> simp[])
  >- (`?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
            get_instruction bb s.vs_inst_idx = SOME inst` by
        metis_tac[active_inst_block_lookup] >>
      `gas_cut k vs0 s` by
        (imp_res_tac enters_block_readings >>
         imp_res_tac gas_setup_callee_readings >> gvs[gas_cut_def]) >>
      first_x_assum (qspecl_then [`D`, `lo`, `explicit`, `b`, `k`] mp_tac) >>
      simp[] >> strip_tac
      >- (drule_all focus_at_call >>
          disch_then (qspec_then `stk` mp_tac) >> simp[]) >>
      disj2_tac >> drule_all run_safe_call >> simp[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `gas_cut k vs0 s` by
    (imp_res_tac gas_bind_outputs_readings >>
     imp_res_tac (cj 2 step_inst_readings_le) >> fs[gas_cut_def] >>
     decide_tac) >>
  first_x_assum (qspecl_then [`D`, `lo`, `explicit`, `b`, `k`] mp_tac) >>
  simp[] >> strip_tac
  >- (drule_all focus_at_not_ret >> simp[]) >>
  drule_all run_safe_ret >> simp[]
QED

(* ===== The per-state facts ===== *)

Theorem mem_step_facts[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) ==>
  inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s
Proof
  strip_tac
  >- (drule_all revert_forward_at_opcode >> strip_tac >>
      simp[inst_mem_ok_in_fn_def] >> metis_tac[]) >>
  gvs[Once mem_safe_step_def, inst_mem_ok_in_fn_def]
QED

Theorem invoke_mem_facts[local]:
  inst.inst_opcode = INVOKE ==>
  inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s
Proof
  strip_tac >>
  `inst = inst with inst_opcode := INVOKE` by
    simp[instruction_component_equality] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  simp[inst_mem_ok_in_fn_def, inst_mem_below_frontier_def]
QED

Theorem focus_at_ok[local]:
  focus_at D lo explicit ctx vs b fn PG G tn s /\ gas_cut k vs s /\
  k <= b /\ k <= LENGTH vs.vs_gas_readings /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\
  inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s
Proof
  strip_tac >> drule_all focus_at_first >> strip_tac
  >- (drule gas_origin_ptr_edge_common_fuel >> strip_tac >> gvs[] >>
      metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_fuel, mem_step_facts]) >>
  gvs[] >> metis_tac[invoke_mem_facts]
QED

Theorem run_safe_ok[local]:
  run_safe D lo ctx fn PG G tn s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\
  inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s
Proof
  strip_tac >>
  qpat_x_assum `run_safe _ _ _ _ _ _ _ _` mp_tac >>
  simp[run_safe_def, ptr_safe_run_def] >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  drule_all ptr_safe_block_head >> strip_tac >>
  drule_all mem_safe_run_head >> strip_tac >>
  metis_tac[ptr_safe_step_inst_ok, mem_step_facts]
QED

(* ===== The bridge ===== *)

Theorem gas_origin_ptr_focus_o1_safe_upto:
  gas_origin_ptr_focus (D, lo, explicit, ctx, func, [])
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>,
     FEMPTY, entry_taint) marks out /\
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME func /\
  fn_entry_label func = SOME lbl /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) ctx.ctx_functions /\
  EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f)) ctx.ctx_functions /\
  lo <= vs.vs_alloca_next /\
  reserved_intervals_wf ctx.ctx_global_reserved /\
  EVERY (\f. f.fn_eom = NONE) ctx.ctx_functions /\
  ~ctx_has_dalloca ctx /\ fmp_free_ctx ctx /\ fixed_region_reserved lo ctx /\
  mem_inv dload_headroom_ok ctx vs /\
  code_layout_valid vs ==>
  o1_safe_upto D lo (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)) ctx vs
Proof
  strip_tac >>
  qabbrev_tac `k = MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)` >>
  `k <= LENGTH marks /\ k <= LENGTH vs.vs_gas_readings` by simp[Abbr `k`] >>
  `!stk PG G tn fn inst s.
     frame_reachable vs ctx stk PG G tn fn inst s /\ gas_cut k vs s ==>
     (!fuel. ptr_inst_ok D lo fuel ctx fn G tn inst s) /\
     inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s` by
    (rpt gen_tac >> strip_tac >>
     `active_inst fn inst s` by
       (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rw[] >> simp[]) >>
     `MEM fn ctx.ctx_functions` by
       metis_tac[frame_reachable_functions_member] >>
     `ALL_DISTINCT (fn_labels fn)` by fs[EVERY_MEM] >>
     drule_all active_inst_block_lookup >> strip_tac >>
     drule frame_reachable_focus >>
     disch_then (qspecl_then [`D`, `lo`, `explicit`, `LENGTH marks`, `k`]
                   mp_tac) >>
     impl_tac
     >- (simp[] >> rpt strip_tac >> gvs[] >> simp[focus_at_def] >>
         qexistsl_tac [`marks`, `out`] >> simp[]) >>
     strip_tac
     >- (drule_all focus_at_ok >> metis_tac[ptr_inst_ok_fuel]) >>
     drule_all run_safe_ok >> metis_tac[ptr_inst_ok_fuel]) >>
  `ptr_discipline_upto lo k ctx vs` by
    (simp[ptr_discipline_upto_def] >> conj_tac >- metis_tac[] >>
     rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[ptr_inst_ok_def]) >>
  `taint_within_upto D k ctx vs` by
    (simp[taint_within_upto_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     first_x_assum (qspec_then `fuel` mp_tac) >> simp[ptr_inst_ok_def]) >>
  `!fn inst s. raw_reachable vs ctx fn inst s /\ gas_cut k vs s ==>
     inst_mem_ok_in_fn fn inst s /\ inst_dload_in_section inst s` by
    (rpt gen_tac >> strip_tac >> drule ptr_raw_reachable_frame >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  `!fn inst s. raw_reachable vs ctx fn inst s /\ gas_cut k vs s ==>
     dload_offset_ok ctx fn inst s` by
    (match_mp_tac dload_offset_ok_upto_intro >> simp[] >> metis_tac[]) >>
  `!fn inst s. raw_reachable vs ctx fn inst s ==>
     s.vs_alloca_next < dimword (:256)` by
    (qpat_x_assum `mem_inv _ _ _` mp_tac >>
     simp[mem_inv_raw_reachable, dload_headroom_ok_def] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  rw[o1_safe_upto_def, o1_ptr_safe_upto_def, raw_mem_ok_def] >> metis_tac[]
QED

(* Representative boundaries for mixed ordinary edits. *)
Theory dftMixedResidualProbe
Ancestors
  dftOccurrenceOrdinaryEdit dftOccurrenceResidual dftOccurrenceFrame
  dftOccurrenceOpenCall dftOccurrenceSuspended dftCommutation dftOrdinarySwap
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecSemantics venomInst venomState list

Theorem dft_nongas_success_gas_address:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME gas ==>
  dft_occ_address (dft_occ_oracle_next w C c) =
    c.dft_occ_path ++ [(c.dft_occ_visit,gas.inst_id)]
Proof
  strip_tac >> drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  simp[dft_occ_address_def]
QED

Theorem dft_gas_value_ordinary_frame:
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  step_inst_base inst (update_var v (w addr) s) = OK (update_var v (w addr) t)
Proof
  strip_tac >>
  `!y. MEM (Var y) inst.inst_operands ==> v <> y` by metis_tac[] >>
  drule_all step_inst_base_frame >>
  disch_then (qspecl_then [`s`, `w addr`] mp_tac) >> simp[map_result_state_def]
QED

(* Multiple pending outputs, rather than a single GAS write, are needed
   when the ordinary operation is moved across an INVOKE. *)
Theorem dft_pending_cut_push:
  dft_cut_pair us [] sL sR /\
  EVERY (\p. ~MEM (Var (FST p)) ops) us /\
  eval_operands ops sL = SOME args /\ setup_callee callee args sL = SOME cs /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb sR) stack n /\
  get_instruction bb sR.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := dft_erase (DftOpen (DftEnter callee 1 cs)
        (DftCaller fn 1 bb inst sR :: MAP (dft_fill_frame 1) stack) n);
      dft_occ_path := c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)];
      dft_occ_visit := 0;
      dft_occ_saved := (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved|>
Proof
  strip_tac >>
  `eval_operands ops sL = eval_operands ops sR` by
    (irule dft_cut_pair_eval_operands >>
     qexistsl_tac [`us`, `[]`] >> simp[]) >>
  `setup_callee callee args sL = setup_callee callee args sR` by
    metis_tac[dft_cut_pair_setup_callee] >>
  rewrite_tac[dft_occ_oracle_next_def] >> irule dft_occ_push >> simp[] >>
  qexists `args` >> metis_tac[]
QED

Theorem dft_invoke_partner_pending:
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  step_inst_base x s = OK t ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
    t = dft_pending_apply us s
Proof
  strip_tac >> drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  `?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
    t = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
    step_inst_base x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us)` by
    (irule dft_ordinary_empty_write_replay >> simp[] >>
     fs[venomEffectsTheory.empty_effects_def]) >>
  metis_tac[dft_pending_apply_def]
QED

Definition dft_pending_frames_def:
  dft_pending_frames us (DftCaller fnL bL bbL callL sL)
      (DftCaller fnR bR bbR callR sR) <=>
    bL = 0 /\ bR = 0 /\ callL = callR /\ callL.inst_opcode = INVOKE /\
    EVERY (\p. ~MEM (FST p) callL.inst_outputs) us /\
    dft_cut_pair us [] sL sR
End

Definition dft_pending_suspended_def:
  dft_pending_suspended us frameL frameR tailL tailR savedL savedR path visit l r <=>
    dft_pending_frames us frameL frameR /\
    ?ctl prefix ghosts nL nR.
      l.dft_occ_core = DftOpen ctl (prefix ++ frameL::tailL) nL /\
      r.dft_occ_core = DftOpen ctl (prefix ++ frameR::tailR) nR /\
      dft_erase l.dft_occ_core = l.dft_occ_core /\
      dft_erase r.dft_occ_core = r.dft_occ_core /\
      LENGTH ghosts = LENGTH prefix /\ EVERY dft_occ_frame_ok prefix /\
      l.dft_occ_saved = ghosts ++ (path,visit)::savedL /\
      r.dft_occ_saved = ghosts ++ (path,visit)::savedR /\
      l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit
End

Theorem dft_pending_suspended_observe:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
  (dft_open_observe fn inst s l.dft_occ_core <=>
   dft_open_observe fn inst s r.dft_occ_core)
Proof
  simp[dft_pending_suspended_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_pending_suspended_address:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r ==>
  dft_occ_address l = dft_occ_address r
Proof
  simp[dft_pending_suspended_def] >> rpt strip_tac >>
  simp[dft_occ_address_def]
QED

Theorem dft_pending_fill_frame[local,simp]:
  dft_fill_frame 0 (dft_fill_frame 1 frame) = dft_fill_frame 0 frame
Proof
  Cases_on `frame` >> simp[dft_fill_frame_def]
QED

Theorem dft_pending_suspended_enter:
  dft_pending_suspended us fL fR tL tR sL sR path visit l r /\
  l.dft_occ_core = DftOpen (DftEnter fn 0 s) stack n ==>
  dft_pending_suspended us fL fR tL tR sL sR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r) \/
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  simp[dft_pending_suspended_def] >> rpt strip_tac >> gvs[] >>
  gvs[dft_erase_def, dft_fill_def, dft_fill_control_def, APPEND_11_LENGTH] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_fill_def, dft_fill_control_def,
           dft_occ_update_def, dft_suspend_cleared_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, dft_erase_def,
       dft_fill_def, dft_fill_control_def,
       dft_pending_fill_frame, SF ETA_ss] >>
  Cases_on `prefix` >> gvs[] >> metis_tac[]
QED

Theorem dft_pending_suspended_init:
  dft_cut_pair us [] sL sR /\
  EVERY (\p. ~MEM (Var (FST p)) ops) us /\
  EVERY (\p. ~MEM (FST p) call.inst_outputs) us /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops sL = SOME args /\ setup_callee callee args sL = SOME cs /\
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL sL) tailL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR sR) tailR nR /\
  get_instruction bbL sL.vs_inst_idx = SOME call /\
  get_instruction bbR sR.vs_inst_idx = SOME call /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  l.dft_occ_saved = savedL /\ r.dft_occ_saved = savedR /\
  MAP (dft_fill_frame 0) tailL = tailL /\
  MAP (dft_fill_frame 0) tailR = tailR ==>
  dft_pending_suspended us (DftCaller fnL 0 bbL call sL)
    (DftCaller fnR 0 bbR call sR) tailL tailR savedL savedR path visit
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `eval_operands ops sR = SOME args` by
    ( `eval_operands ops sL = eval_operands ops sR` by
        (irule dft_cut_pair_eval_operands >>
         qexistsl_tac [`us`, `[]`] >> simp[]) >> metis_tac[]) >>
  `setup_callee callee args sR = SOME cs` by
    metis_tac[dft_cut_pair_setup_callee] >>
  drule_all dft_suspend_push >>
  disch_then (qspec_then `w` assume_tac) >>
  rev_drule_all dft_suspend_push >>
  disch_then (qspec_then `w` assume_tac) >>
  simp[dft_pending_suspended_def, dft_pending_frames_def,
       dft_erase_def, dft_fill_def, dft_fill_control_def, dft_fill_frame_def] >>
  qexistsl_tac [`[]`, `[]`] >> simp[]
QED

(* Root-machine GAS/ordinary probe. The intermediate ordinary state may
   change memory and all non-variable fields; only the GAS output is framed. *)
Theorem dft_gas_ordinary_machine_probe:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) [] n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) [] n /\
  l.dft_occ_saved = [] /\ r.dft_occ_saved = [] /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  let after = (update_var v (w (path ++ [(visit,gas.inst_id)])) t)
                with vs_inst_idx := SUC (SUC s.vs_inst_idx)
  in
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l)).dft_occ_core =
      DftOpen (DftAt fnL 0 bbL after) [] (SUC n) /\
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C r)).dft_occ_core =
      DftOpen (DftAt fnR 0 bbR after) [] (SUC n)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `step_inst_base inst (update_var v (w (path ++ [(visit,gas.inst_id)])) s) =
     OK (update_var v (w (path ++ [(visit,gas.inst_id)])) t)` by
    metis_tac[dft_gas_value_ordinary_frame] >>
  `step_inst_base inst ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
      with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((update_var v (w (path ++ [(visit,gas.inst_id)])) t)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  qpat_assum `l.dft_occ_core = _` (mp_then Any mp_tac dft_suspend_gas_step) >>
  simp[] >> disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
      `mid.dft_occ_core = DftOpen (DftAt fnL 0 bbL
        ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
          with vs_inst_idx := SUC s.vs_inst_idx)) [] (SUC n)` by
        simp[Abbr `mid`] >>
      drule dft_occ_ordinary_next >>
      simp[update_var_inst_idx] >>
      disch_then (qspecl_then [`w`, `(update_var v (w (path ++ [(visit,gas.inst_id)])) t) with vs_inst_idx := SUC s.vs_inst_idx`, `C`] mp_tac) >>
      simp[]) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
  `mid.dft_occ_core = DftOpen (DftAt fnR 0 bbR
    (t with vs_inst_idx := SUC s.vs_inst_idx)) [] n` by simp[Abbr `mid`] >>
  drule dft_suspend_gas_step >>
  simp[Abbr `mid`] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  simp[update_var_def]
QED

(* Interface-probe inventory (not a whole-orbit transport theorem).

   GAS/ordinary:
   - The successful two-step root square above checks the occurrence address
     and SUC gas clock in both instruction orders, even when the ordinary
     instruction changes effect state. General stacks, nested edits and
     residual initialization from the static edit environment remain to lift.
   - If ordinary aborts before GAS in one orientation, the other orientation
     has consumed one extra GAS. Transport must use result relatedness, NOT
     equality of final occurrence counters. Exclude local Error by original
     readiness at the crossing; do not assume whole-run safety.
   - GAS has no memory ranges. Cover the ordinary observation before/after
     the GAS update using operand disjointness and memory equality. Entry
     and exit observations and the reverse edit need separate coverage.

   INVOKE/ordinary:
   - dft_invoke_partner_pending extracts arbitrary output updates from the
     inversion's actual empty-effect restrictions; it does not assert that
     every empty-write instruction is neutral or successful.
   - dft_pending_suspended_init checks common callee entry from paired cuts.
     dft_pending_suspended_enter checks one actual callee entry transition,
     including missing block and PHI failure. It needs no callee return.
   - General At transitions (ordinary, GAS, nested INVOKE), nested returns,
     distinguished return and Abort/Error clearing still need multi-output
     suspension closure. Return must preserve pending outputs disjoint from
     call outputs, using the restore/cut interface, not single-GAS framing.
   - Call lookup/decode/argument/setup failures must synchronize. Successful
     ordinary execution before a call versus after its return needs the
     empty-effect replay boundary, including changes to callee-visible state.
     Local abort ordering and local no-Error must come from protected cuts.
   - While suspended, observe/address boundaries above are exact. At caller
     resumption, cover the moved ordinary instruction's observation (its
     empty-effect restriction alone is not an observation theorem). Both
     forward and reverse orientations must retain all target observations,
     including prefixes of nonreturning callees.
   - Init pushes the SAME dynamic call address; entry leaves it unchanged.
     General nested closure must maintain saved-address depth. Productive
     segment lengths and fuel adequacy are separate obligations: these probes
     do not prove equal endpoint gas clocks or a single finite reading list.

   The multi-output suspended skeleton intentionally mirrors the accepted
   single-GAS skeleton. Before duplicating its full transition proof, factor
   a generic paired-inaccessible-caller boundary if the consumer interface
   permits it. No definition or frozen obligation was changed by these probes.
*)

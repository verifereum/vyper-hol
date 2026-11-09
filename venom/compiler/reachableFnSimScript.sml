(*
 * Context simulation from block-level simulations on reachable frames
 *
 * A pass that is only correct on states the source program actually
 * reaches under the pointer discipline (its frames are frame_reachable,
 * so access_ok and allocas_from hold there) proves one block at a time:
 * from block-boundary states s (source) and t (target) related by R, with
 * s reachable, one block of the source and of the target end in results
 * related by R at the next reachable boundary, by R_ret on internal
 * return, or by dead_result_rel on halt and abort.  Inside the block it
 * may run callees through fn_sim_below, the same simulation for smaller
 * fuel.  reachable_fn_sim_ctx_sim turns that into ctx_sim.
 *
 * R and R_ret see the frame_reachable ghosts: the suspended callers stk
 * and the argument sites PG, fixed for a frame, and the provenance G and
 * taint tn at the boundary, which change from block to block.  A pass
 * that leaves memory different in a caller's dead buffers needs stk to
 * say where those are while a callee runs, and the taint to say which
 * bytes of a fresh allocation may differ.
 *
 * TOP-LEVEL:
 *   block_reach              — the source reaches a block-boundary state
 *   fn_run_rel               — related results of a function run
 *   block_step_rel           — related results of one block
 *   fn_sim_below             — function-level simulation below a fuel bound
 *   reachable_fn_sim_ctx_sim — block obligation ==> ctx_sim
 *)

Theory reachableFnSim
Ancestors
  ptrDiscipline ptrSafeRun o1PassContract passSimulationDefs
  contextCodegenRel venomExecSemantics venomState venomExecProps
  venomRetProps venomInst ctxLookupAgreeHelpers list

(* A block-boundary state of fn (before its PHIs): if the block is
   entered, the source reaches its first active instruction from vs with
   these ghosts. *)
Definition block_reach_def:
  block_reach vs C stk PG G tn fn s <=>
    !s1 inst.
      enters_block fn s s1 /\ active_inst fn inst s1 ==>
      frame_reachable vs C stk PG G tn fn inst s1
End

Theorem frame_reachable_block_reach:
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted ==>
  block_reach vs C stk PG (entry_prov fn s' G)
    (entry_taint_vars fn s' tn) fn s'
Proof
  rw[block_reach_def] >> irule frame_reachable_block >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem frame_reachable_call_block_reach:
  frame_reachable vs C stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  block_reach vs C
    (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee cs
Proof
  rw[block_reach_def] >> irule frame_reachable_call >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Related results of a whole function run.  R_ret sees the returned
   values and the ghosts at the return. *)
Definition fn_run_rel_def:
  fn_run_rel D R_ret stk PG fn r r' <=>
    case (r, r') of
      (Halt s, Halt s') => dead_result_rel D r r'
    | (Abort a s, Abort a' s') => dead_result_rel D r r'
    | (IntRet v s, IntRet v' s') =>
        v' = v /\ ?G tn. R_ret stk PG G tn fn v s s'
    | _ => F
End

(* Related results of one block: a non-halted OK reaches the next
   boundary, and continues under R there. *)
Definition block_step_rel_def:
  block_step_rel D vs C R R_ret stk PG fn r r' <=>
    case (r, r') of
      (OK s, OK s') =>
        (s'.vs_halted <=> s.vs_halted) /\
        (if s.vs_halted then dead_result_rel D (Halt s) (Halt s')
         else ?G tn. block_reach vs C stk PG G tn fn s /\
                     R stk PG G tn fn s s')
    | _ => fn_run_rel D R_ret stk PG fn r r'
End

(* Every function of C simulates its namesake in C' from R-related,
   reachable block-boundary states, for every fuel below n. *)
Definition fn_sim_below_def:
  fn_sim_below D vs C C' R R_ret n <=>
    !k stk PG G tn fn fn' s t.
      k < n /\
      MEM fn C.ctx_functions /\
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      R stk PG G tn fn s t /\ block_reach vs C stk PG G tn fn s /\
      terminates (run_blocks k C fn s) ==>
      ?m. fn_run_rel D R_ret stk PG fn (run_blocks k C fn s)
                                       (run_blocks m C' fn' t)
End

(* The big-step semantics stays inside frame_reachable: a block run from
   a reachable instruction ends, on OK, at a reachable block boundary, and
   on internal return at a reachable return instruction; a function run
   from a reachable boundary returns from a reachable return instruction.
   Pass proofs use it to know their INVOKE sites and block ends reachable. *)
Theorem frame_reachable_walk_mutual:
  (!fuel C inst s vs stk PG G tn fn s'.
     frame_reachable vs C stk PG G tn fn inst s /\
     active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
     step_inst fuel C inst s = OK s' ==>
     ?G' tn'. !inst'.
       active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
       frame_reachable vs C stk PG G' tn' fn inst'
         (s' with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!fuel C bb s vs stk PG G tn fn r.
     frame_reachable vs C stk PG G tn fn
       (EL s.vs_inst_idx bb.bb_instructions) s /\
     MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
     s.vs_inst_idx < LENGTH bb.bb_instructions /\
     exec_block fuel C bb s = r ==>
     (!s'. r = OK s' ==> ?G' tn'. block_reach vs C stk PG G' tn' fn s') /\
     (!v se. r = IntRet v se ==>
        ?G' tn' rinst sr fuel'.
          frame_reachable vs C stk PG G' tn' fn rinst sr /\
          active_inst fn rinst sr /\
          step_inst fuel' C rinst sr = IntRet v se)) /\
  (!fuel C fn s vs stk PG G tn v se.
     block_reach vs C stk PG G tn fn s /\
     run_blocks fuel C fn s = IntRet v se ==>
     ?G' tn' rinst sr fuel'.
       frame_reachable vs C stk PG G' tn' fn rinst sr /\
       active_inst fn rinst sr /\
       step_inst fuel' C rinst sr = IntRet v se)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume frame_reachable_walk_mutual[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[Once step_inst_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule_all frame_reachable_call_block_reach >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      qexistsl [`DRESTRICT G (COMPL (set inst.inst_outputs))`,
        `tn' with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs))`] >>
      rpt strip_tac >>
      drule frame_reachable_ret >> simp[] >>
      disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >> qexistsl [`step_prov PG G inst s'`, `step_taint inst s s' tn`] >>
  rpt strip_tac >> irule frame_reachable_next >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume frame_reachable_walk_mutual[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `active_inst fn (EL s.vs_inst_idx bb.bb_instructions) s` by
    (simp[active_inst_def] >> metis_tac[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >> strip_tac >> gvs[]
  >- (Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
      >- (gvs[AllCaseEqs()] >> rpt strip_tac >>
          drule_all frame_reachable_block_reach >> metis_tac[]) >>
      drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
      Cases_on `SUC s.vs_inst_idx < LENGTH bb.bb_instructions`
      >- (gvs[get_instruction_def] >>
          qpat_x_assum `!vs stk PG G tn fn. _ ==> ?G' tn'. _` drule_all >> strip_tac >>
          `active_inst fn (EL (SUC s.vs_inst_idx) bb.bb_instructions)
             (v with vs_inst_idx := SUC s.vs_inst_idx)` by
            (simp[active_inst_def] >> metis_tac[]) >>
          first_x_assum drule >> strip_tac >>
          first_x_assum drule_all >> simp[]) >>
      conj_tac >> simp[Once exec_block_def, get_instruction_def])
  >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume frame_reachable_walk_mutual[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `fuel` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  rename1 `eval_phis s bb.bb_instructions = OK sphi` >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = sphi.vs_current_bb` by
    (drule venomExecProofsTheory.eval_phis_preserves_current_bb >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecPropsTheory.lookup_block_label]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >> gvs[Once exec_block_def, get_instruction_def]) >>
  (`active_inst fn (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
          (sphi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        (simp[active_inst_def] >> metis_tac[]) >>
      `frame_reachable vs C stk PG G tn fn
         (EL (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
         (sphi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        (gvs[block_reach_def] >> first_x_assum irule >>
         simp[enters_block_def] >> metis_tac[]) >>
      first_x_assum drule_all >> strip_tac >> metis_tac[])
QED

Finalise frame_reachable_walk_mutual

Theorem frame_reachable_walk:
  (!fuel C bb s vs stk PG G tn fn r.
     frame_reachable vs C stk PG G tn fn
       (EL s.vs_inst_idx bb.bb_instructions) s /\
     MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
     s.vs_inst_idx < LENGTH bb.bb_instructions /\
     exec_block fuel C bb s = r ==>
     (!s'. r = OK s' ==> ?G' tn'. block_reach vs C stk PG G' tn' fn s') /\
     (!v se. r = IntRet v se ==>
        ?G' tn' rinst sr fuel'.
          frame_reachable vs C stk PG G' tn' fn rinst sr /\
          active_inst fn rinst sr /\
          step_inst fuel' C rinst sr = IntRet v se)) /\
  (!fuel C fn s vs stk PG G tn v se.
     block_reach vs C stk PG G tn fn s /\
     run_blocks fuel C fn s = IntRet v se ==>
     ?G' tn' rinst sr fuel'.
       frame_reachable vs C stk PG G' tn' fn rinst sr /\
       active_inst fn rinst sr /\
       step_inst fuel' C rinst sr = IntRet v se)
Proof
  ACCEPT_TAC (CONJUNCT2 frame_reachable_walk_mutual)
QED

(* A block that stops the run (halted OK, Halt, Abort, IntRet) stops both
   function runs alike. *)
Theorem run_blocks_stop_sim[local]:
  !D vs C C' R R_ret stk PG fn fn' bb bb' j m s t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    block_step_rel D vs C R R_ret stk PG fn
      (run_block j C bb s) (run_block m C' bb' t) /\
    ~(?s1. run_block j C bb s = OK s1 /\ ~s1.vs_halted) ==>
    fn_run_rel D R_ret stk PG fn (run_blocks (SUC j) C fn s)
                                 (run_blocks (SUC m) C' fn' t)
Proof
  rpt strip_tac >> simp[run_blocks_unfold] >>
  Cases_on `run_block j C bb s` >> Cases_on `run_block m C' bb' t` >>
  gvs[block_step_rel_def, fn_run_rel_def] >> metis_tac[]
QED

(* A block that continues continues both runs; the target's later fuel
   covers both its block and its continuation. *)
Theorem run_blocks_ok_sim[local]:
  !D R_ret stk PG fn fn' bb bb' j m m2 M s t s1 t1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    run_block j C bb s = OK s1 /\ ~s1.vs_halted /\
    run_block m C' bb' t = OK t1 /\ ~t1.vs_halted /\
    fn_run_rel D R_ret stk PG fn (run_blocks j C fn s1)
                                 (run_blocks m2 C' fn' t1) /\
    m <= M /\ m2 <= M ==>
    fn_run_rel D R_ret stk PG fn (run_blocks (SUC j) C fn s)
                                 (run_blocks (SUC M) C' fn' t)
Proof
  rpt strip_tac >>
  `run_block M C' bb' t = OK t1` by
    (irule run_block_fuel_mono_OK >> qexists_tac `m` >> simp[]) >>
  `run_blocks M C' fn' t1 = run_blocks m2 C' fn' t1` by
    (irule (CONJUNCT2 (CONJUNCT2 fuel_mono)) >>
     conj_tac >- (rpt strip_tac >>
                  Cases_on `run_blocks j C fn s1` >> gvs[fn_run_rel_def]) >>
     qexists_tac `m2` >> simp[]) >>
  simp[run_blocks_unfold]
QED

(* The block obligation gives fn_sim_below at every bound. *)
Theorem block_sim_fn_sim_below[local]:
  !D vs C C' R R_ret.
    (!k stk PG G tn fn fn' s t bb.
       fn_sim_below D vs C C' R R_ret (SUC k) /\
       MEM fn C.ctx_functions /\
       lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       R stk PG G tn fn s t /\ block_reach vs C stk PG G tn fn s /\
       lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       terminates (run_block k C bb s) ==>
       ?m bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
               block_step_rel D vs C R R_ret stk PG fn
                 (run_block k C bb s) (run_block m C' bb' t)) ==>
    !n. fn_sim_below D vs C C' R R_ret n
Proof
  rpt gen_tac >> strip_tac >> completeInduct_on `n` >>
  simp[Once fn_sim_below_def] >> rpt strip_tac >>
  Cases_on `k` >- gvs[Once run_blocks_def, terminates_def] >>
  rename1 `run_blocks (SUC j) C fn s` >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
     gvs[run_blocks_unfold, terminates_def]) >>
  `terminates (run_block j C bb s)` by
    (gvs[run_blocks_unfold] >>
     Cases_on `run_block j C bb s` >> gvs[terminates_def]) >>
  `fn_sim_below D vs C C' R R_ret (SUC j)` by
    (qpat_x_assum `!m. m < n ==> _` irule >> simp[]) >>
  qpat_x_assum `!k stk PG G tn fn fn' s t bb. _`
    (qspecl_then [`j`, `stk`, `PG`, `G`, `tn`, `fn`, `fn'`, `s`, `t`, `bb`]
       mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `?s1. run_block j C bb s = OK s1 /\ ~s1.vs_halted`
  >- (gvs[] >>
      `?t1 G1 tn1. run_block m C' bb' t = OK t1 /\ ~t1.vs_halted /\
                   block_reach vs C stk PG G1 tn1 fn s1 /\
                   R stk PG G1 tn1 fn s1 t1` by
        (Cases_on `run_block m C' bb' t` >>
         gvs[block_step_rel_def, fn_run_rel_def] >> metis_tac[]) >>
      `terminates (run_blocks j C fn s1)` by gvs[run_blocks_unfold] >>
      qpat_x_assum `!m. m < n ==> _` (qspec_then `SUC j`
        (mp_tac o SIMP_RULE std_ss [fn_sim_below_def])) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`j`, `stk`, `PG`, `G1`, `tn1`, `fn`, `fn'`,
                               `s1`, `t1`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qexists_tac `SUC (m + m')` >> irule run_blocks_ok_sim >>
      simp[] >> qexistsl_tac [`m`, `m'`, `t1`] >> simp[]) >>
  qexists_tac `SUC m` >> irule run_blocks_stop_sim >> simp[] >>
  metis_tac[]
QED

(* Why it holds: strong induction on n for fn_sim_below n.  run_blocks
   (SUC j) C fn s looks up the block and runs run_block j on it, then
   Halt (halted OK), run_blocks j C fn s' (OK) or the propagated result
   (venomExecSemanticsTheory.run_blocks_unfold); the OK arm of
   block_step_rel hands the next iteration its block_reach and R, and
   target fuels compose by venomExecPropsTheory.fuel_mono.  The root
   reduces run_context to run_blocks from the entry state, where
   frame_reachable's entry rule gives block_reach with the empty ghosts;
   o1_ctx_shape rules out IntRet/OK at the root
   (venomRetPropsTheory.run_context_not_int_ret, run_context_not_ok). *)
Theorem reachable_fn_sim_ctx_sim:
  !D vs C C' R R_ret.
    o1_ctx_shape C /\
    C'.ctx_entry = C.ctx_entry /\
    (!fn. MEM fn C.ctx_functions ==>
          ?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
                fn_entry_label fn' = fn_entry_label fn) /\
    (!name fn lbl.
       C.ctx_entry = SOME name /\
       lookup_function name C.ctx_functions = SOME fn /\
       fn_entry_label fn = SOME lbl ==>
       R [] [] FEMPTY entry_taint fn
         (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                     vs_inst_idx := 0 |>)
         (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                     vs_inst_idx := 0 |>)) /\
    (!k stk PG G tn fn fn' s t bb.
       fn_sim_below D vs C C' R R_ret (SUC k) /\
       MEM fn C.ctx_functions /\
       lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       R stk PG G tn fn s t /\ block_reach vs C stk PG G tn fn s /\
       lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       terminates (run_block k C bb s) ==>
       ?m bb'. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
               block_step_rel D vs C R R_ret stk PG fn
                 (run_block k C bb s) (run_block m C' bb' t)) ==>
    ctx_sim D C C' vs vs
Proof
  rpt strip_tac >> rw[ctx_sim_def] >>
  `!v t. run_context fuel C vs <> IntRet v t` by
    (rpt gen_tac >> irule run_context_not_int_ret >> rpt strip_tac >>
     `MEM fn C.ctx_functions /\ fn.fn_name = name` by
       metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
     gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM,
         entry_fn_no_return_def] >> metis_tac[]) >>
  drule block_sim_fn_sim_below >> strip_tac >>
  Cases_on `C.ctx_entry` >- gvs[run_context_def, terminates_def] >>
  rename1 `C.ctx_entry = SOME name` >>
  Cases_on `lookup_function name C.ctx_functions`
  >- gvs[run_context_def, terminates_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  Cases_on `fn_entry_label fn`
  >- gvs[run_context_def, run_function_def, terminates_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  `MEM fn C.ctx_functions /\ fn.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
         fn_entry_label fn' = SOME lbl` by metis_tac[] >>
  qabbrev_tac `s0 = vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                              vs_inst_idx := 0 |>` >>
  `!f. run_context f C vs = run_blocks f C fn s0 /\
       run_context f C' vs = run_blocks f C' fn' s0` by
    gvs[run_context_def, run_function_def, Abbr `s0`] >>
  `block_reach vs C [] [] FEMPTY entry_taint fn s0` by
    (rw[block_reach_def, Abbr `s0`] >> irule frame_reachable_entry >>
     metis_tac[]) >>
  qpat_x_assum `!n. fn_sim_below _ _ _ _ _ _ n`
    (qspec_then `SUC fuel` (mp_tac o SIMP_RULE std_ss [fn_sim_below_def])) >>
  disch_then (qspecl_then [`fuel`, `[]`, `[]`, `FEMPTY`, `entry_taint`,
                           `fn`, `fn'`, `s0`, `s0`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >> strip_tac >>
  qexists_tac `m` >> gvs[] >>
  Cases_on `run_blocks fuel C fn s0` >> gvs[fn_run_rel_def] >>
  Cases_on `run_blocks m C' fn' s0` >> gvs[]
QED

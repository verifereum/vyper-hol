(*
 * FmpLowering's stage simulation relation, between a source state of the
 * raw context (run at fmp; it never reclaims within a frame, but a
 * caller's later DALLOCA reuses a returned callee's addresses, since the
 * caller keeps its own vs_fmp) and a target state of the
 * lowered context (threads a runner through BUMP and INVOKE, reclaims at
 * the restores).  Definitions only: establishing and preserving the
 * relation are the later pieces' obligations.
 *
 * A site map sm sends each live nonempty source DALLOCA site (b,z), as the
 * ghost provenance G names it, to its target address c and the inst_id of
 * the DALLOCA that made it.  sm is one map for the whole call stack: a
 * callee's sites are added above its entry and dropped at its RET.
 * Variables are related only while live; a pointer into a zero-size site
 * is unconstrained.  Memory agrees below eom and on the sites of sm.
 *
 * TOP-LEVEL:
 *   fmp_ld_sites      - sm as LowerDload's site triples
 *   fmp_sites_ok      - geometry of sm
 *   fmp_value_rel     - one value
 *   fmp_env_rel       - a frame's variables
 *   fmp_params_rel    - a frame's parameters
 *   fmp_frame_covers  - base coverage of a frame's own sites
 *   fmp_ledger_link   - a frame's own sites are its ledger's regions
 *   fmp_stage_lowered - the target function is FmpLowering's output
 *   fmp_stage_plan    - its reclaim plan
 *   fmp_stage_root    - where its root instruction counts
 *   fmp_stage_tidx    - the control map, source index to target index
 *   fmp_frame_base    - a frame's source entry fmp
 *   fmp_frame_lo      - a frame's target entry runner
 *   fmp_frame_rel     - one frame, before or after its point's restores
 *   fmp_saved_rel     - the saved caller frames
 *   fmp_stage_rel     - the joint relation
 *   fmp_stage_ctx     - the stage theorems' premises
 *   fmp_target_run    - the next n target instructions of a block
 *   fmp_stage_result  - related exec_block results
 *   fmp_invoke_sim    - an INVOKE step is simulated
 *)
Theory fmpStageRel
Ancestors
  fmpLowerSequenceExec fmpLowerReclaimPlan fmpLedgerProps fmpLowerDefs
  fmpReclaimDefs fmpAliasDefs fmpAnalysisDefs livenessDefs analysisSimDefs
  o1LowerDloadRelocationKernel o1LowerDloadShared ptrDiscipline
  o1PassContract venomPassSchedule venomCompilerTypes unitShapeDefs
  passSimulationDefs contextCodegenRel venomExecSemantics venomState
  venomInst finite_map words list

(* ===== The site map ===== *)

(* Why: the LowerDload kernels (ld_value_agree, ld_memory_agree) and their
   per-op lemmas take sites as (source base, target base, size). *)
Definition fmp_ld_sites_def:
  fmp_ld_sites (sm : (num # num) |-> (num # num)) =
    FMAP_MAP2 (\(k,v). (FST k, FST v, SND k)) sm
End

Theorem FLOOKUP_fmp_ld_sites:
  FLOOKUP (fmp_ld_sites sm) (b,z) =
    case FLOOKUP sm (b,z) of
      NONE => NONE
    | SOME (c,id) => SOME (b,c,z)
Proof
  simp[fmp_ld_sites_def, FLOOKUP_DEF, FMAP_MAP2_THM] >>
  rw[] >> Cases_on `sm ' (b,z)` >> simp[]
QED

(* Why: memory reasoning needs the sites nonempty and disjoint on both
   sides, the source ones below the raw frontier raw_fmp, and the target
   ones in [fmp0, lo), so a BUMP from the runner lo overlaps none. *)
Definition fmp_sites_ok_def:
  fmp_sites_ok sm fmp0 raw0 lo (raw_fmp : bytes32) <=>
    (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
       0 < z /\ raw0 <= b /\ b + z <= w2n raw_fmp /\
       fmp0 <= c /\ c + z <= lo) /\
    (!b z c id d w e jd.
       FLOOKUP sm (b,z) = SOME (c,id) /\ FLOOKUP sm (d,w) = SOME (e,jd) /\
       (b,z) <> (d,w) ==>
       (b + z <= d \/ d + w <= b) /\ (c + z <= e \/ e + w <= c))
End

(* ===== Values, variables and parameters ===== *)

(* Why: a pointer into a zero-size site can be neither dereferenced nor
   compared (access_ok), and two such sites can share a key with different
   targets, so it is unconstrained; everything else is ld_value_agree. *)
Definition fmp_value_rel_def:
  fmp_value_rel sm (h : (num # num) option) m x y <=>
    (?b. h = SOME (b,0)) \/ ld_value_agree (fmp_ld_sites sm) h m x y
End

(* Why: the target defines every variable the source does (it runs the
   same definitions), so a PHI reading a dead operand still succeeds.
   Values are related only for live variables: nothing else is read
   again, and a reclaim frees only sites no live variable points into, so
   a restore can drop them from sm.  The return-pc variable differs (the
   target's token is the runner), but RET drops it. *)
Definition fmp_env_rel_def:
  fmp_env_rel sm fn live G tv s t <=>
    !v x. FLOOKUP s.vs_vars v = SOME x ==>
      ?y. FLOOKUP t.vs_vars v = SOME y /\
          (MEM v live /\ ~retpc_var fn v ==>
           fmp_value_rel sm (FLOOKUP G v)
             (op_taint (entry_taint with t_var := tv) (Var v)) x y)
End

(* Why: PARAM reads the user arguments, which the target passes in the
   same positions; a callee taking the FMP gets the runner after them. *)
Definition fmp_params_rel_def:
  fmp_params_rel sm PG s t <=>
    LENGTH s.vs_params <= LENGTH t.vs_params /\
    !k. k < LENGTH s.vs_params ==>
      fmp_value_rel sm (if k < LENGTH PG then EL k PG else NONE) {}
        (EL k s.vs_params) (EL k t.vs_params)
End

(* Why: fmp_restore_contract needs fmp_base_covers for the provenance "v
   points into an own site of sm made by DALLOCA id".  Only the frame's
   own sites are covered, those at or above its entry fmp eb and below
   its runner lo: a callee receives its caller's pointers through PARAM,
   which its own analysis doesn't trace, and its sites lie above its
   caller's lo. *)
Definition fmp_frame_covers_def:
  fmp_frame_covers (sm : (num # num) |-> (num # num)) env (eb:num) (lo:num) G <=>
    !v b z c id.
      FLOOKUP G v = SOME (b,z) /\ FLOOKUP sm (b,z) = SOME (c,id) /\
      eb <= b /\ c < lo ==>
      MEM id (fmp_bases env v)
End

(* Why: each own site of sm at or above the ledger's bottom is a region of
   the ledger with the same DALLOCA, so the sites a restore must drop
   (those at or above its new runner) are exactly the popped regions'.
   Own sites below the bottom are the ones a join dropped from the
   analysis stack; they end at or below the bottom, so no restore of this
   frame reaches them. *)
Definition fmp_ledger_link_def:
  fmp_ledger_link (sm : (num # num) |-> (num # num)) (eb:num) (lo:num) regions <=>
    !b z c id.
      FLOOKUP sm (b,z) = SOME (c,id) /\ eb <= b /\ c < lo ==>
      ((if regions = [] then lo else (LAST regions).fr_lo) <= c ==>
       ?r. MEM r regions /\ r.fr_lo = c /\ r.fr_hi = c + z /\ r.fr_site = id) /\
      (c < (if regions = [] then lo else (LAST regions).fr_lo) ==>
       c + z <= (if regions = [] then lo else (LAST regions).fr_lo))
End

(* ===== The lowered function and the control map ===== *)

(* Why: each target function is FmpLowering's output for its source
   function in some observed context (ctx_pass_stage), and runner is the
   variable that output threads. *)
Definition fmp_stage_lowered_def:
  fmp_stage_lowered infos ctx runner fn fn' <=>
    analyze_fmp_context ctx = SOME infos /\
    ?sp sp'. ir_supply_covers_fn sp fn /\
             fmp_lower_function_with_info infos ctx sp fn = SOME (fn',sp') /\
             runner = FST (fresh_ir_var sp)
End

(* Why: the restores and the analysis states are read off the plan the
   lowering used; a function the lowering leaves alone has none. *)
Definition fmp_stage_plan_def:
  fmp_stage_plan infos ctx fn =
    case analyze_fmp_reclaims infos ctx fn of
      SOME plan => plan
    | NONE => FEMPTY
End

(* Why: a function taking the FMP gets one root instruction in its entry
   block (fmp_install_root), counted in the control map from source index
   rp on.  Elsewhere it sits before RETPC_PARAM (at LENGTH users), and the
   source step of RETPC_PARAM runs both, so rp is one past it.  In the
   context entry it sits after the parameters (none, by o1_fn_shape), and
   runs before the frame's first related point.  NONE when there is no
   runner. *)
Definition fmp_stage_root_def:
  fmp_stage_root infos ctx fn =
    if fn.fn_fmp_signature = NONE /\
       (case FLOOKUP infos fn.fn_name of
          SOME info => info.fi_needs_fmp
        | NONE => F)
    then
      case (split_fmp_entry fn, fn.fn_blocks) of
        (SOME (FmpEntryLayout users retpc rest), bb::bbs) =>
          SOME (bb.bb_label,
                if fn_is_context_entry ctx fn
                then LENGTH users + LENGTH (OPTION_TO_LIST retpc)
                else SUC (LENGTH users))
      | _ => NONE
    else NONE
End

(* Why: the control map.  Source index idx of block lbl sits at this target
   index, the start of its restores: each earlier point contributes its
   restore (one if the plan has one there) and its expansion (four for
   DALLOCA, one otherwise), plus the root from its position on. *)
Definition fmp_stage_tidx_def:
  fmp_stage_tidx (plan : fmp_reclaim_plan) root lbl insts idx =
    SUM (GENLIST (\j. (if (lbl,j) IN FDOM plan then 1 else 0) +
                      (if (EL j insts).inst_opcode = DALLOCA then 4 else 1))
                 idx) +
    (case root of
       SOME (rl,rp) => if lbl = rl /\ rp <= idx then 1 else 0
     | NONE => 0)
End

(* ===== Frames ===== *)

(* Why: a frame's own sites are the ones at or above the source FMP it was
   entered with (the caller's at its INVOKE, setup_callee). *)
Definition fmp_frame_base_def:
  fmp_frame_base raw0 [] = raw0 /\
  fmp_frame_base raw0 (f::stk) = w2n f.cf_state.vs_fmp
End

(* Why: likewise on the target, the runner it was entered with: the
   initial fmp at the root, else the caller's runner at its INVOKE. *)
Definition fmp_frame_lo_def:
  fmp_frame_lo fmp0 [] = fmp0 /\
  fmp_frame_lo fmp0 ((t:venom_state,lo:num)::ts) = lo
End

(* Why: one frame of fn, source state s and target state t of fn', with
   entry fmp eb, entry runner elo and runner lo.  With restored = F, t is
   at the start of the source point's restores; with restored = T (an
   INVOKE, a terminator, or a DALLOCA about to step, and every saved
   frame) it is past them, with the popped stack.  Past the root the
   runner holds lo, the ledger tiles the analysis stack's regions up to lo
   and links them to sm, and the own sites are covered.  Before the root
   the entry runner is where the root reads it. *)
Definition fmp_frame_rel_def:
  fmp_frame_rel sm fmp0 raw0 eb elo lo restored fn fn' PG G tv s t <=>
    ?infos ctx runner.
      let lbl = s.vs_current_bb in
      let idx = s.vs_inst_idx in
      let insts = (case lookup_block lbl fn.fn_blocks of
                     SOME bb => bb.bb_instructions | NONE => []) in
      let plan = fmp_stage_plan infos ctx fn in
      let root = fmp_stage_root infos ctx fn in
      fmp_stage_lowered infos ctx runner fn fn' /\
      lbl = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
      t.vs_inst_idx =
        fmp_stage_tidx plan root lbl insts idx +
        (if restored /\ (lbl,idx) IN FDOM plan then 1 else 0) /\
      fmp_env_rel sm fn (live_vars_at (liveness_analyze fn) lbl idx) G tv s t /\
      fmp_params_rel sm PG s t /\
      s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
      s.vs_block_ctx = t.vs_block_ctx /\
      s.vs_data_section = t.vs_data_section /\ s.vs_labels = t.vs_labels /\
      s.vs_code = t.vs_code /\ s.vs_prev_hashes = t.vs_prev_hashes /\
      w2n s.vs_initial_fmp = raw0 /\ w2n t.vs_initial_fmp = fmp0 /\
      fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\ elo <= lo /\
      eb <= w2n s.vs_fmp /\
      (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
         (eb <= b <=> elo <= c) /\ (b < eb ==> c + z <= elo /\ b + z <= eb)) /\
      (case root of
         NONE => lo = elo
       | SOME (rl,rp) =>
         ?env states st stack.
           fmp_base_analyze (fn_insts fn) = SOME env /\
           fmp_reclaim_states infos fn = SOME states /\
           df_at NONE states lbl idx = SOME st /\
           stack = (if restored
                    then SND (fmp_pop_at infos fn (liveness_analyze fn) env
                                (lbl,idx) (EL idx insts) st)
                    else st.frs_stack) /\
           fmp_frame_covers sm env eb lo G /\
           (if lbl = rl /\ idx < rp then
              lo = elo /\ stack = [] /\
              (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
              (~fn_is_context_entry ctx fn ==>
                 LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
                 LENGTH s.vs_params < LENGTH t.vs_params /\
                 EL (LENGTH s.vs_params) t.vs_params = n2w elo)
            else
              lookup_var runner t = SOME (n2w lo) /\
              ?regions.
                fmp_ledger_ok (fn_insts fn) env t lo regions /\
                MAP (\r. r.fr_mark) regions = stack /\
                EVERY (\r. elo <= r.fr_lo) regions /\
                fmp_ledger_link sm eb lo regions))
End

(* Why: the saved caller frames, innermost first, each with its target
   state at the INVOKE and its runner there, which is its callee's entry
   runner. *)
Definition fmp_saved_rel_def:
  (fmp_saved_rel C' sm fmp0 raw0 [] [] <=> T) /\
  (fmp_saved_rel C' sm fmp0 raw0 (f::stk) ((t,lo)::ts) <=>
     (?fn'. lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME fn' /\
        fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
          (fmp_frame_lo fmp0 ts) lo T f.cf_fn fn' f.cf_params f.cf_prov
          f.cf_tvar f.cf_state t) /\
     f.cf_state.vs_halted = t.vs_halted /\
     fmp_saved_rel C' sm fmp0 raw0 stk ts) /\
  (fmp_saved_rel C' sm fmp0 raw0 [] (_::_) <=> F) /\
  (fmp_saved_rel C' sm fmp0 raw0 (_::_) [] <=> F)
End

(* Why: the joint relation at a source point (stk PG G tn fn s, as
   frame_reachable names them) and the target state t with saved frames
   ts: the geometry of sm, the active frame, the saved frames, and the
   state all frames share (memory, ld_shared_agree's fields, the return
   data, the halt flag). *)
Definition fmp_stage_rel_def:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts <=>
    fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
    (?fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
       fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
         (fmp_frame_lo fmp0 ts) lo restored fn fn' PG G tn.t_var s t) /\
    fmp_saved_rel C' sm fmp0 raw0 stk ts /\
    ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
    s.vs_returndata = t.vs_returndata /\ s.vs_halted = t.vs_halted
End

(* ===== Shapes of the step statements ===== *)

(* Why: the frozen stage theorems' premises, at the raw source state vs,
   which every piece of the simulation assumes. *)
Definition fmp_stage_ctx_def:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom <=>
    ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
      (o1_walk_view rpolicy 3) C C' /\
    o1_pre 3 C C' /\ dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs' /\
    vs = vs' with <| vs_fmp := fmp; vs_initial_fmp := fmp |> /\
    o1_inv D 3 C vs /\ fmp_variant_room (SOME fmp) C' vs' /\
    max_live_eom C = SOME eom
End

(* Why: one source step is matched by the next n instructions of the
   target's block (restores, an expansion, the root), run straight-line;
   t' is past them. *)
Definition fmp_target_run_def:
  fmp_target_run fuel C' name t n t' <=>
    ?fn' bb' t1.
      lookup_function name C'.ctx_functions = SOME fn' /\
      lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
      t.vs_inst_idx + n <= LENGTH bb'.bb_instructions /\
      run_insts fuel C' (TAKE n (DROP t.vs_inst_idx bb'.bb_instructions)) t =
        OK t1 /\
      t' = t1 with vs_inst_idx := t.vs_inst_idx + n
End

(* Why: what exec_block of a related point gives, as run_blocks and the
   INVOKE step consume it: a halt or abort related by dead_result_rel; a
   RET at a related point, returning the same values (they carry no
   provenance, so the relation makes them equal) in its unchanged state;
   or a jump from a related point, past its restores, to the same block. *)
Definition fmp_stage_result_def:
  fmp_stage_result D C C' vs fmp0 raw0 eom stk PG fn ts r r' <=>
    case r of
      Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | Error e => F
    | IntRet ir se =>
        ?ri sr G tn sm lo tr fn' ri' kr jr.
          ri.inst_opcode = RET /\ active_inst fn ri sr /\
          frame_reachable vs C stk PG G tn fn ri sr /\
          fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sr lo tr ts /\
          lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
          active_inst fn' ri' tr /\
          step_inst kr C ri sr = IntRet ir se /\ se = sr /\
          step_inst kr C' ri' tr = IntRet jr tr /\ r' = IntRet jr tr /\
          jr.iret_values = ir.iret_values /\
          ir.iret_adopt_fmp = NONE /\ jr.iret_adopt_fmp = NONE
    | OK se =>
        ?bi sb G tn sm lo tb fn' bi' kb te.
          MEM bi.inst_opcode [JMP; JNZ; DJMP] /\ active_inst fn bi sb /\
          frame_reachable vs C stk PG G tn fn bi sb /\
          fmp_stage_rel D C' sm fmp0 raw0 eom T stk PG G tn fn sb lo tb ts /\
          lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
          active_inst fn' bi' tb /\
          step_inst kb C bi sb = OK se /\ step_inst kb C' bi' tb = OK te /\
          r' = OK te /\ ~se.vs_halted /\ ~te.vs_halted /\
          se.vs_current_bb = te.vs_current_bb /\
          se.vs_prev_bb = te.vs_prev_bb
End

(* Why: the INVOKE case of the runner induction (run_defs_ind's step_inst
   predicate): from a related point past the INVOKE's restores, the target
   INVOKE matches the source one, returning to a related point with the
   same runner; the site map may change across the call. *)
Definition fmp_invoke_sim_def:
  fmp_invoke_sim rpolicy D C C' vs vs' fmp eom k inv s <=>
    !stk PG G tn fn sm lo t ts fn' inv' r.
      fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\ ~s.vs_halted /\
      frame_reachable vs C stk PG G tn fn inv s /\ active_inst fn inv s /\
      inv.inst_opcode = INVOKE /\
      fmp_stage_rel D C' sm (w2n vs'.vs_initial_fmp) (w2n fmp) eom T
        stk PG G tn fn s lo t ts /\
      lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
      active_inst fn' inv' t /\
      step_inst k C inv s = r /\ terminates r ==>
      ?m r'.
        step_inst m C' inv' t = r' /\
        case r of
          OK s1 =>
            ?t1 tn1 next sm1.
              r' = OK t1 /\
              active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
              frame_reachable vs C stk PG
                (DRESTRICT G (COMPL (set inv.inst_outputs))) tn1 fn next
                (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
              fmp_stage_rel D C' sm1 (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
                stk PG (DRESTRICT G (COMPL (set inv.inst_outputs))) tn1 fn
                (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
                (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
        | Halt se => dead_result_rel D r r'
        | Abort ab se => dead_result_rel D r r'
        | _ => F
End

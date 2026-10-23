(* Original-instruction indexed FMP reclaim analysis.  A shared step pops the
 * maximal dead newest-first prefix BEFORE applying the instruction effect.
 * Candidates and the checker use the same pre-state and the same step.
 * This executable certificate is not an operational memory-safety theorem. *)
Theory fmpReclaimDefs
Ancestors
  fmpAnalysisDefs fmpAliasDefs livenessDefs cfgDefs dominatorDefs arithmetic
  finite_map rich_list

Type fmp_point = ``:string # num``
Datatype:
  fmp_reclaim_state = <| frs_stack : string list;
    frs_captures : string list; frs_can_reclaim : bool |>
End
Type fmp_reclaim_plan = ``:(fmp_point,string) fmap``

Definition fmp_empty_reclaim_state_def:
  fmp_empty_reclaim_state = <| frs_stack := []; frs_captures := [];
    frs_can_reclaim := T |>
End
Definition fmp_common_top_def:
  fmp_common_top [] ys = [] /\
  fmp_common_top xs [] = [] /\
  fmp_common_top (x::xs) (y::ys) =
    if x = y then x::fmp_common_top xs ys else []
End
Definition fmp_reclaim_join_def:
  fmp_reclaim_join x y = <|
    frs_stack := fmp_common_top x.frs_stack y.frs_stack;
    frs_captures := list_union x.frs_captures y.frs_captures;
    frs_can_reclaim := (x.frs_can_reclaim /\ y.frs_can_reclaim) |>
End
Definition fmp_reclaim_option_join_def:
  fmp_reclaim_option_join NONE y = y /\
  fmp_reclaim_option_join x NONE = x /\
  fmp_reclaim_option_join (SOME x) (SOME y) = SOME (fmp_reclaim_join x y)
End
Definition fmp_getfmp_outputs_def:
  fmp_getfmp_outputs (inst:instruction) =
    if inst.inst_opcode = GETFMP then inst.inst_outputs else []
End

Definition fmp_callee_info_def:
  fmp_callee_info infos inst =
    case fmp_invoke_target inst of
      SOME (SOME name) => FLOOKUP infos name
    | _ => NONE
End
Definition fmp_is_reclaim_point_def:
  fmp_is_reclaim_point infos inst <=>
    MEM inst.inst_opcode [DALLOCA; JMP; JNZ; DJMP] \/
    (case fmp_callee_info infos inst of
       SOME info => info.fi_needs_fmp | NONE => F)
End
Definition fmp_clears_marks_def:
  fmp_clears_marks infos inst <=> inst.inst_opcode = SETFMP \/
    (case fmp_callee_info infos inst of
       SOME info => info.fi_publishes_fmp | NONE => F)
End

(* Splitting is independent of instruction effects: head is the newest mark. *)
Definition fmp_pop_prefix_def:
  fmp_pop_prefix dead [] = ([],[]) /\
  fmp_pop_prefix dead (x::xs) =
    if dead x then
      let (popped,kept) = fmp_pop_prefix dead xs in (x::popped,kept)
    else ([],x::xs)
End
Definition fmp_pop_target_def:
  fmp_pop_target [] = NONE /\
  fmp_pop_target (x::xs) = SOME (LAST (x::xs))
End
Definition fmp_mark_dead_def:
  fmp_mark_dead insts env live mark <=>
    case fmp_dalloca_query insts env mark of
      NONE => F
    | SOME id => ~fmp_allocation_live env insts live id
End
Definition fmp_capture_veto_def:
  fmp_capture_veto fn live (p:fmp_point) cap <=>
    fmp_capture_query_veto (fn_insts fn)
      (live_vars_at live (FST p) (SND p)) cap
End
Definition fmp_pop_at_def:
  fmp_pop_at infos fn live env p inst st =
    if st.frs_can_reclaim /\ fmp_is_reclaim_point infos inst /\
       ~EXISTS (fmp_capture_veto fn live p) st.frs_captures
    then fmp_pop_prefix
      (fmp_mark_dead (fn_insts fn) env
        (live_vars_at live (FST p) (SND p))) st.frs_stack
    else ([],st.frs_stack)
End
Definition fmp_apply_effect_def:
  fmp_apply_effect infos inst st =
    if fmp_clears_marks infos inst then fmp_empty_reclaim_state
    else if inst.inst_opcode = DALLOCA then
      case fmp_single_output inst of
        SOME mark => st with frs_stack := mark::st.frs_stack
      | NONE => st with frs_can_reclaim := F
    else st with frs_captures :=
      list_union (fmp_getfmp_outputs inst) st.frs_captures
End
Definition fmp_reclaim_step_def:
  fmp_reclaim_step infos fn live env p inst NONE = (NONE,NONE) /\
  fmp_reclaim_step infos fn live env p inst (SOME st) =
    let (popped,kept) = fmp_pop_at infos fn live env p inst st in
    (fmp_pop_target popped,
     SOME (fmp_apply_effect infos inst (st with frs_stack := kept)))
End
Definition fmp_transfer_def:
  fmp_transfer infos fn live env p inst st =
    SND (fmp_reclaim_step infos fn live env p inst st)
End

(* Task-local indexed adapter.  The generic framework's transfer receives no
 * block/index; this adapter preserves its join/worklist discipline but passes
 * the original point explicitly.  inst_id is never used as an index. *)
Definition fmp_fold_forward_def:
  fmp_fold_forward transfer lbl [] (idx:num) acc m =
    (acc,m |+ ((lbl,idx),acc)) /\
  fmp_fold_forward transfer lbl (inst::rest) idx acc m =
    fmp_fold_forward transfer lbl rest (idx+1)
      (transfer (lbl,idx) inst acc) (m |+ ((lbl,idx),acc))
End
Definition fmp_joined_def:
  fmp_joined entry cfg states lbl =
    df_joined_val Forward NONE fmp_reclaim_option_join
      (K (\src dst st. st)) () entry cfg states lbl
End
Definition fmp_fold_at_def:
  fmp_fold_at transfer entry cfg bbs states lbl =
    fmp_fold_forward transfer lbl
      (case lookup_block lbl bbs of NONE => [] | SOME bb => bb.bb_instructions)
      0 (fmp_joined entry cfg states lbl) FEMPTY
End
Definition fmp_process_block_def:
  fmp_process_block transfer entry cfg bbs lbl states =
    let final = FST (fmp_fold_at transfer entry cfg bbs states lbl) in
    let old = df_boundary NONE states lbl in
    let new = fmp_reclaim_option_join old final in
    if new = old then states
    else states with ds_boundary := states.ds_boundary |+ (lbl,new)
End
Definition fmp_populate_def:
  fmp_populate transfer entry cfg bbs states =
    FOLDL (\st lbl. st with ds_inst := FUNION
      (SND (fmp_fold_at transfer entry cfg bbs states lbl)) st.ds_inst)
      states (MAP (\bb. bb.bb_label) bbs)
End
Definition fmp_reclaim_fuel_def:
  fmp_reclaim_fuel fn = (LENGTH fn.fn_blocks + 1) * (LENGTH (fn_insts fn) + 1)
End
Definition fmp_reclaim_analyze_fuel_def:
  fmp_reclaim_analyze_fuel fuel infos fn live env =
    case entry_block fn of NONE => NONE | SOME bb =>
    let entry = SOME (bb.bb_label,SOME fmp_empty_reclaim_state) in
    let cfg = cfg_analyze fn in
    let transfer = fmp_transfer infos fn live env in
    let st0 = init_df_state NONE (MAP (\b. b.bb_label) fn.fn_blocks) in
    let st1 = st0 with ds_boundary :=
      st0.ds_boundary |+ (bb.bb_label,SOME fmp_empty_reclaim_state) in
    let result = SND (wl_iterate_fuel fuel
      (\lbl old new. df_boundary NONE new lbl <> df_boundary NONE old lbl)
      (fmp_process_block transfer entry cfg fn.fn_blocks)
      (cfg_succs_of cfg) cfg.cfg_dfs_pre st1) in
    SOME (fmp_populate transfer entry cfg fn.fn_blocks result)
End
Definition fmp_reclaim_states_def:
  fmp_reclaim_states infos fn =
    case fmp_base_analyze (fn_insts fn) of NONE => NONE | SOME env =>
    let live = liveness_analyze fn in
    case fmp_reclaim_analyze_fuel (fmp_reclaim_fuel fn) infos fn live env of
      NONE => NONE
    | SOME states =>
        (case fmp_reclaim_analyze_fuel (fmp_reclaim_fuel fn + 1)
                infos fn live env of
           SOME states' => if states' = states then SOME states else NONE
         | NONE => NONE)
End

Definition fmp_point_well_located_def:
  fmp_point_well_located fn (p:fmp_point) <=>
    case lookup_block (FST p) fn.fn_blocks of NONE => F
    | SOME bb => SND p < LENGTH bb.bb_instructions
End
Definition fmp_restore_target_ok_def:
  fmp_restore_target_ok infos ctx fn live captures (p:fmp_point) base <=>
    fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
    fmp_point_well_located fn p /\
    ~EXISTS (fmp_capture_veto fn live p) captures /\
    (case fmp_base_analyze (fn_insts fn) of NONE => F
     | SOME env => fmp_mark_dead (fn_insts fn) env
        (live_vars_at live (FST p) (SND p)) base)
End

(* A block walk queries exactly the original pre-instruction states. *)
Definition fmp_scan_candidates_def:
  fmp_scan_candidates infos fn live env states lbl [] (idx:num) = [] /\
  fmp_scan_candidates infos fn live env states lbl (inst::rest) idx =
    let p = (lbl,idx) in
    let target = FST (fmp_reclaim_step infos fn live env p inst
      (df_at NONE states lbl idx)) in
    let entries = fmp_scan_candidates infos fn live env states lbl rest (idx+1) in
    case target of NONE => entries | SOME mark => (p,mark)::entries
End
Definition fmp_collect_candidates_def:
  fmp_collect_candidates infos fn live env states bbs =
    FLAT (MAP (\bb. fmp_scan_candidates infos fn live env states
      bb.bb_label bb.bb_instructions 0) bbs)
End
Definition fmp_plan_of_list_def:
  fmp_plan_of_list [] = FEMPTY /\
  fmp_plan_of_list ((p,base)::rest) = fmp_plan_of_list rest |+ (p,base)
End
Definition fmp_candidate_plan_def:
  fmp_candidate_plan infos ctx fn states =
    case fmp_base_analyze (fn_insts fn) of NONE => FEMPTY | SOME env =>
    fmp_plan_of_list (fmp_collect_candidates infos fn (liveness_analyze fn)
      env states fn.fn_blocks)
End
Definition fmp_reclaim_entry_ok_def:
  fmp_reclaim_entry_ok infos ctx fn (p:fmp_point) base <=>
    case fmp_base_analyze (fn_insts fn) of NONE => F | SOME env =>
    case fmp_reclaim_states infos fn of NONE => F | SOME states =>
    case lookup_block (FST p) fn.fn_blocks of NONE => F | SOME bb =>
      SND p < LENGTH bb.bb_instructions /\
      (case df_at NONE states (FST p) (SND p) of NONE => F | SOME st =>
        fmp_restore_target_ok infos ctx fn (liveness_analyze fn)
          st.frs_captures p base /\
        FST (fmp_reclaim_step infos fn (liveness_analyze fn) env p
          (EL (SND p) bb.bb_instructions) (SOME st)) = SOME base)
End
Definition fmp_reclaim_plan_ok_def:
  fmp_reclaim_plan_ok infos ctx fn (plan:fmp_reclaim_plan) <=>
    !p base. FLOOKUP plan p = SOME base ==>
      fmp_reclaim_entry_ok infos ctx fn p base
End
Theorem fmp_reclaim_plan_ok_compute[compute]:
  fmp_reclaim_plan_ok infos ctx fn plan <=>
    FEVERY (\(p,base). fmp_reclaim_entry_ok infos ctx fn p base) plan
Proof
  simp[fmp_reclaim_plan_ok_def, finite_mapTheory.FEVERY_DEF,
       finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED
Definition analyze_fmp_reclaims_def:
  analyze_fmp_reclaims (infos:fmp_info_map) (ctx:venom_context)
      (fn:ir_function) : fmp_reclaim_plan option =
    if ~fmp_info_valid ctx infos \/ ~MEM fn ctx.ctx_functions \/
       ~wf_function fn \/ ~fn_inst_wf fn \/ fn.fn_fmp_signature <> NONE
    then NONE
    else case fmp_reclaim_states infos fn of NONE => NONE | SOME states =>
      let plan = fmp_candidate_plan infos ctx fn states in
      if fmp_reclaim_plan_ok infos ctx fn plan then SOME plan else NONE
End

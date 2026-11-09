Theory frameOriginHistory
Ancestors
  frameOriginReachable frameExecutionHistory rich_list list

(* Snapshots retain the maps of this activation, not reconstructed maps. *)
Datatype:
  origin_snapshot = OriginSnapshot ir_function ((num # num) option list)
    ((string, num # num) fmap)
    ((string, frame_origin # (num # num)) fmap) instruction venom_state
End

Datatype:
  origin_event = OriginObserve origin_snapshot
    | OriginInitial venom_state
    | OriginCallee venom_state
    | OriginOrdinary num venom_state
    | OriginBlock num venom_state
    | OriginResume num ir_function instruction venom_state internal_return
        venom_state venom_state
End

Definition origin_observations_def:
  origin_observations [] = [] /\
  origin_observations (e::es) =
    case e of
      OriginObserve (OriginSnapshot fn PG G om inst s) =>
        (inst,s)::origin_observations es
    | _ => origin_observations es
End

Theorem origin_observations_append[simp]:
  origin_observations (a ++ b) = origin_observations a ++ origin_observations b
Proof
  Induct_on `a` >> simp[origin_observations_def] >>
  Cases_on `h` >> simp[origin_observations_def] >>
  Cases_on `o'` >> simp[origin_observations_def]
QED

Inductive joint_origin_history:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\ active_inst fn inst s1 ==>
     joint_origin_history vs0 ctx [] [] FEMPTY entry_taint fn inst s1 [] FEMPTY []
       [OriginInitial (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>);
        OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst s1)])
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel oms om hs h.
     joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
     active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
     inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     joint_origin_history vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx) oms (origin_step PG om inst s') hs
       (h ++ [OriginOrdinary fuel s'; OriginObserve
         (OriginSnapshot fn PG (step_prov PG G inst s') (origin_step PG om inst s')
           inst' (s' with vs_inst_idx := SUC s.vs_inst_idx))]))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel oms om hs h.
     joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
     active_inst fn inst s /\ is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     joint_origin_history vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1 oms (origin_entry fn s' om) hs
       (h ++ [OriginBlock fuel s'; OriginObserve
         (OriginSnapshot fn PG (entry_prov fn s' G) (origin_entry fn s' om) inst' s1)]))
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst oms om hs h.
     joint_origin_history vs0 ctx stk PG G tn caller inv s oms om hs h /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     joint_origin_history vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
       (om::oms) FEMPTY (h::hs)
       [OriginCallee cs; OriginObserve
         (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst s1)])
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel oms om caller_om hs h caller_h.
     joint_origin_history vs0 ctx (f::stk) PG G tn fn rinst s
       (caller_om::oms) om (caller_h::hs) h /\
     active_inst fn rinst s /\ step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
     active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     joint_origin_history vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
       (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
       (caller_h ++ [OriginResume fuel fn rinst s ret s_end s'; OriginObserve
         (OriginSnapshot f.cf_fn f.cf_params
           (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
           (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
           (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))]))
End

Theorem joint_origin_history_erasure:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt strip_tac >>
  metis_tac[origin_frame_reachable_rules]
QED

Theorem joint_origin_history_projection:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    frame_history vs0 ctx stk PG G tn fn inst s
      (MAP origin_observations hs) (origin_observations h)
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt strip_tac >>
  gvs[origin_observations_def] >> metis_tac[frame_history_rules]
QED

Theorem joint_origin_history_endpoints:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    h <> [] /\ LAST h = OriginObserve (OriginSnapshot fn PG G om inst s) /\
    LIST_REL (\f p. SND p <> [] /\ LAST (SND p) = OriginObserve
      (OriginSnapshot f.cf_fn f.cf_params f.cf_prov (FST p) f.cf_inst f.cf_state))
      stk (ZIP (oms,hs)) /\ LENGTH oms = LENGTH stk /\ LENGTH hs = LENGTH stk
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt strip_tac >> gvs[LAST_APPEND]
QED

Theorem origin_frame_has_joint_history:
  !vs0 ctx stk PG G tn fn inst s oms om.
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    ?hs h. joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt strip_tac
  >- metis_tac[joint_origin_history_rules]
  >- metis_tac[joint_origin_history_rules]
  >- metis_tac[joint_origin_history_rules]
  >- metis_tac[joint_origin_history_rules]
  >> `LENGTH hs = LENGTH (f::stk)` by metis_tac[joint_origin_history_endpoints] >>
  Cases_on `hs` >> gvs[] >> metis_tac[joint_origin_history_rules]
QED

(* A log edge is a successful transition, not merely an attempted step.
   Resume is deliberately separate from ordinary instruction execution. *)
Definition origin_edge_def:
  origin_edge ctx (OriginSnapshot fn PG G om inst s) e
      (OriginSnapshot fn' PG' G' om' inst' t) =
    (active_inst fn inst s /\ active_inst fn' inst' t /\
    case e of
      OriginOrdinary fuel post =>
        ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
        step_inst fuel ctx inst s = OK post /\
        fn' = fn /\ PG' = PG /\ G' = step_prov PG G inst post /\
        om' = origin_step PG om inst post /\
        t = (post with vs_inst_idx := SUC s.vs_inst_idx)
    | OriginBlock fuel post =>
        is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
        ~post.vs_halted /\ enters_block fn post t /\
        fn' = fn /\ PG' = PG /\ G' = entry_prov fn post G /\
        om' = origin_entry fn post om
    | OriginResume fuel callee rinst rs ret send post =>
        active_inst callee rinst rs /\
        step_inst fuel ctx rinst rs = IntRet ret send /\
        bind_outputs inst.inst_outputs ret.iret_values
          (adopt_return_fmp ret (merge_callee_state s send)) = SOME post /\
        fn' = fn /\ PG' = PG /\
        G' = DRESTRICT G (COMPL (set inst.inst_outputs)) /\
        om' = DRESTRICT om (COMPL (set inst.inst_outputs)) /\
        t = (post with vs_inst_idx := SUC s.vs_inst_idx)
    | _ => F)
End

Definition origin_start_def:
  origin_start e (OriginSnapshot fn PG G om inst s) =
    (G = FEMPTY /\ om = FEMPTY /\ active_inst fn inst s /\
    case e of
      OriginInitial pre => PG = [] /\ enters_block fn pre s
    | OriginCallee pre => enters_block fn pre s
    | _ => F)
End

(* This small grammar is the consumer boundary for adjacency inversion. *)
Inductive origin_log:
[~start:]
  (!ctx e a. origin_start e a ==> origin_log ctx [e; OriginObserve a])
[~extend:]
  (!ctx h a e b.
     origin_log ctx h /\ LAST h = OriginObserve a /\ origin_edge ctx a e b ==>
     origin_log ctx (h ++ [e; OriginObserve b]))
End

Theorem origin_log_endpoint_active:
  !ctx h. origin_log ctx h ==>
    !fn PG G om inst s.
      LAST h = OriginObserve (OriginSnapshot fn PG G om inst s) ==>
      active_inst fn inst s
Proof
  ho_match_mp_tac origin_log_ind >> rpt strip_tac >>
  gvs[LAST_APPEND, origin_start_def]
  >> Cases_on `a` >> Cases_on `e` >> gvs[origin_edge_def]
QED

Theorem joint_origin_history_logs_invariant[local]:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    origin_log ctx h /\ EVERY (origin_log ctx) hs /\
    h <> [] /\ LAST h = OriginObserve (OriginSnapshot fn PG G om inst s) /\
    LIST_REL (\f p. SND p <> [] /\ LAST (SND p) = OriginObserve
      (OriginSnapshot f.cf_fn f.cf_params f.cf_prov (FST p) f.cf_inst f.cf_state))
      stk (ZIP (oms,hs)) /\ LENGTH oms = LENGTH stk /\ LENGTH hs = LENGTH stk
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt strip_tac >> gvs[LAST_APPEND]
  >- (irule origin_log_start >> simp[origin_start_def])
  >- (
      irule origin_log_extend >> goal_assum (drule_at Any) >>
      simp[origin_edge_def] >> metis_tac[])
  >- (
      irule origin_log_extend >> goal_assum (drule_at Any) >>
      simp[origin_edge_def] >> metis_tac[])
  >- (irule origin_log_start >> simp[origin_start_def])
  >> irule origin_log_extend >> goal_assum (drule_at Any) >>
  simp[origin_edge_def] >> metis_tac[origin_log_endpoint_active]
QED

Inductive origin_chain:
[~nil:]
  (!ctx a. origin_chain ctx a [])
[~cons:]
  (!ctx a e b rest.
     origin_edge ctx a e b /\ origin_chain ctx b rest ==>
     origin_chain ctx a (e::OriginObserve b::rest))
End

Theorem origin_chain_append:
  !ctx a tail. origin_chain ctx a tail ==>
    !z e b. LAST (OriginObserve a::tail) = OriginObserve z /\
      origin_edge ctx z e b ==>
      origin_chain ctx a (tail ++ [e; OriginObserve b])
Proof
  ho_match_mp_tac origin_chain_ind >> rpt strip_tac
  >- (gvs[] >> metis_tac[origin_chain_rules])
  >> simp[] >> irule origin_chain_cons >> simp[] >>
  first_x_assum irule >> qexists `z` >> gvs[]
QED

Theorem origin_log_chain:
  !ctx h. origin_log ctx h ==>
    ?e a tail. h = e::OriginObserve a::tail /\ origin_start e a /\
      origin_chain ctx a tail
Proof
  ho_match_mp_tac origin_log_ind >> rpt strip_tac
  >- (qexistsl [`e`,`a`,`[]`] >> simp[origin_chain_rules])
  >> qexistsl [`e'`,`a'`,`tail ++ [e; OriginObserve b]`] >>
  simp[] >> irule origin_chain_append >> goal_assum (drule_at Any) >>
  qexists `a` >> gvs[]
QED

Theorem origin_edge_not_observe:
  origin_edge ctx a e b ==> !c. e <> OriginObserve c
Proof
  Cases_on `a` >> Cases_on `b` >> Cases_on `e` >> simp[origin_edge_def]
QED

Theorem origin_start_not_observe:
  origin_start e a ==> !c. e <> OriginObserve c
Proof
  Cases_on `a` >> Cases_on `e` >> simp[origin_start_def]
QED

Theorem origin_chain_completion:
  !ctx a tail. origin_chain ctx a tail ==>
    !pre b rest.
      OriginObserve a::tail = pre ++ OriginObserve b::rest /\ rest <> [] ==>
      ?e c suffix. rest = e::OriginObserve c::suffix /\ origin_edge ctx b e c
Proof
  ho_match_mp_tac origin_chain_ind >> rpt strip_tac
  >- (Cases_on `pre` >> gvs[])
  >> Cases_on `pre`
  >- (gvs[] >> metis_tac[])
  >> gvs[] >> Cases_on `t`
  >- (gvs[] >> metis_tac[origin_edge_not_observe])
  >> gvs[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem origin_log_completion:
  origin_log ctx h /\ h = pre ++ OriginObserve a::rest /\ rest <> [] ==>
    ?e b suffix. rest = e::OriginObserve b::suffix /\ origin_edge ctx a e b
Proof
  rpt strip_tac >> drule origin_log_chain >> strip_tac >>
  Cases_on `pre`
  >- (gvs[] >> metis_tac[origin_start_not_observe])
  >> gvs[] >> drule origin_chain_completion >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem origin_edge_ordinary:
  origin_edge ctx (OriginSnapshot fn PG G om inst s) (OriginOrdinary fuel post)
    (OriginSnapshot fn' PG' G' om' inst' t) ==>
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK post /\ fn' = fn /\ PG' = PG /\
    G' = step_prov PG G inst post /\ om' = origin_step PG om inst post /\
    t = (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[origin_edge_def]
QED

Theorem origin_edge_block:
  origin_edge ctx (OriginSnapshot fn PG G om inst s) (OriginBlock fuel post)
    (OriginSnapshot fn' PG' G' om' inst' t) ==>
    is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
    ~post.vs_halted /\ enters_block fn post t /\ fn' = fn /\ PG' = PG /\
    G' = entry_prov fn post G /\ om' = origin_entry fn post om
Proof
  simp[origin_edge_def]
QED

Theorem origin_edge_resume:
  origin_edge ctx (OriginSnapshot fn PG G om inst s)
    (OriginResume fuel callee rinst rs ret send post)
    (OriginSnapshot fn' PG' G' om' inst' t) ==>
    active_inst callee rinst rs /\ step_inst fuel ctx rinst rs = IntRet ret send /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s send)) = SOME post /\
    fn' = fn /\ PG' = PG /\
    G' = DRESTRICT G (COMPL (set inst.inst_outputs)) /\
    om' = DRESTRICT om (COMPL (set inst.inst_outputs)) /\
    t = (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[origin_edge_def]
QED

Theorem origin_start_initial:
  origin_start (OriginInitial pre) (OriginSnapshot fn PG G om inst s) ==>
    PG = [] /\ G = FEMPTY /\ om = FEMPTY /\ enters_block fn pre s
Proof
  simp[origin_start_def]
QED

Theorem origin_start_callee:
  origin_start (OriginCallee pre) (OriginSnapshot fn PG G om inst s) ==>
    G = FEMPTY /\ om = FEMPTY /\ enters_block fn pre s
Proof
  simp[origin_start_def]
QED

Theorem origin_edge_cases:
  origin_edge ctx a e b ==>
    (?fuel post. e = OriginOrdinary fuel post) \/
    (?fuel post. e = OriginBlock fuel post) \/
    (?fuel fn inst s ret send post. e = OriginResume fuel fn inst s ret send post)
Proof
  Cases_on `a` >> Cases_on `b` >> Cases_on `e` >> simp[origin_edge_def]
QED

Theorem origin_start_cases:
  origin_start e a ==>
    (?pre. e = OriginInitial pre) \/ (?pre. e = OriginCallee pre)
Proof
  Cases_on `a` >> Cases_on `e` >> simp[origin_start_def]
QED

Theorem joint_origin_history_current_log:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    origin_log ctx h
Proof
  metis_tac[joint_origin_history_logs_invariant]
QED

Theorem joint_origin_history_saved_log:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\ n < LENGTH stk ==>
    origin_log ctx (EL n hs)
Proof
  rpt strip_tac >> drule joint_origin_history_logs_invariant >>
  simp[EVERY_MEM] >> metis_tac[MEM_EL]
QED

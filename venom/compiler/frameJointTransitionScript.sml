Theory frameJointTransition
Ancestors
  frameOriginHistory frameOriginReachable frameOriginUpdates ptrDiscipline
  venomExecSemantics venomState venomInst finite_map list

(* This packages, rather than replaces, the existing joint-history endpoint. *)
Datatype:
  joint_config = JointConfig (call_frame list) ((num # num) option list)
    ((string, num # num) fmap) taint ir_function instruction venom_state
    (((string, frame_origin # (num # num)) fmap) list)
    ((string, frame_origin # (num # num)) fmap)
    (origin_event list list) (origin_event list)
End

Definition joint_config_reachable_def:
  joint_config_reachable vs0 ctx (JointConfig stk PG G tn fn inst s oms om hs h) <=>
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h
End

Inductive joint_initial:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\ active_inst fn inst s1 ==>
     joint_initial vs0 ctx (JointConfig [] [] FEMPTY entry_taint fn inst s1 [] FEMPTY []
       [OriginInitial (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>);
        OriginObserve (OriginSnapshot fn [] FEMPTY FEMPTY inst s1)]))
End

(* Only the recursive reachability premise has been removed from each rule.
   No independently-reachable-snapshot shortcut is admitted. *)
Inductive joint_transition:
[~next:]
  (!ctx stk PG G tn fn inst inst' s s' fuel oms om hs h.
     active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
     inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h)
       (SOME (OriginOrdinary fuel s'))
       (JointConfig stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx) oms (origin_step PG om inst s') hs
       (h ++ [OriginOrdinary fuel s'; OriginObserve
         (OriginSnapshot fn PG (step_prov PG G inst s') (origin_step PG om inst s')
           inst' (s' with vs_inst_idx := SUC s.vs_inst_idx))])))
[~block:]
  (!ctx stk PG G tn fn inst inst' s s' s1 fuel oms om hs h.
     active_inst fn inst s /\ is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h)
       (SOME (OriginBlock fuel s'))
       (JointConfig stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1 oms (origin_entry fn s' om) hs
       (h ++ [OriginBlock fuel s'; OriginObserve
         (OriginSnapshot fn PG (entry_prov fn s' G) (origin_entry fn s' om) inst' s1)])))
[~call:]
  (!ctx stk PG G tn caller inv s nm ops callee args cs s1 inst oms om hs h.
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     joint_transition ctx (JointConfig stk PG G tn caller inv s oms om hs h) NONE
       (JointConfig
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
       (om::oms) FEMPTY (h::hs)
       [OriginCallee cs; OriginObserve
         (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst s1)]))
[~ret:]
  (!ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel oms om caller_om hs h caller_h.
     active_inst fn rinst s /\ step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
     active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     joint_transition ctx
       (JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h)
       (SOME (OriginResume fuel fn rinst s ret s_end s'))
       (JointConfig stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
       (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
       (caller_h ++ [OriginResume fuel fn rinst s ret s_end s'; OriginObserve
         (OriginSnapshot f.cf_fn f.cf_params
           (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
           (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
           (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))])))
End

Theorem joint_initial_reachable:
  joint_initial vs0 ctx q ==> joint_config_reachable vs0 ctx q
Proof
  simp[Once joint_initial_cases] >> rpt strip_tac >>
  simp[joint_config_reachable_def] >> metis_tac[joint_origin_history_rules]
QED

Theorem joint_transition_reachable:
  joint_config_reachable vs0 ctx q /\ joint_transition ctx q ev q' ==>
  joint_config_reachable vs0 ctx q'
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  gvs[joint_config_reachable_def] >> metis_tac[joint_origin_history_rules]
QED

Theorem joint_reachable_predecessor:
  joint_config_reachable vs0 ctx q ==>
  joint_initial vs0 ctx q \/
  ?p ev. joint_config_reachable vs0 ctx p /\ joint_transition ctx p ev q
Proof
  Cases_on `q` >> simp[joint_config_reachable_def] >>
  simp[Once joint_origin_history_cases] >> rpt strip_tac >>
  metis_tac[joint_initial_rules, joint_transition_rules, joint_config_reachable_def]
QED

(* Constructor-specific iff boundaries serve both introduction and inversion.
   They keep consumers away from the four-way transition case theorem. *)
Theorem joint_transition_ordinary:
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginOrdinary fuel post)) q <=>
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK post /\
  ?inst'. active_inst fn inst' (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    q = JointConfig stk PG (step_prov PG G inst post)
      (step_taint inst s post tn) fn inst'
      (post with vs_inst_idx := SUC s.vs_inst_idx) oms
      (origin_step PG om inst post) hs
      (h ++ [OriginOrdinary fuel post; OriginObserve
        (OriginSnapshot fn PG (step_prov PG G inst post)
          (origin_step PG om inst post) inst'
          (post with vs_inst_idx := SUC s.vs_inst_idx))])
Proof
  simp[Once joint_transition_cases] >> metis_tac[]
QED

Theorem joint_transition_block_iff:
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h)
    (SOME (OriginBlock fuel post)) q <=>
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK post /\ ~post.vs_halted /\
  ?s1 inst'. enters_block fn post s1 /\ active_inst fn inst' s1 /\
    q = JointConfig stk PG (entry_prov fn post G)
      (entry_taint_vars fn post tn) fn inst' s1 oms (origin_entry fn post om) hs
      (h ++ [OriginBlock fuel post; OriginObserve
        (OriginSnapshot fn PG (entry_prov fn post G)
          (origin_entry fn post om) inst' s1)])
Proof
  simp[Once joint_transition_cases] >> metis_tac[]
QED

Theorem joint_transition_call_iff:
  !inv. joint_transition ctx (JointConfig stk PG G tn caller inv s oms om hs h) NONE q <=>
  active_inst caller inv s /\ inv.inst_opcode = INVOKE /\
  ?nm ops callee args cs s1 inst.
    decode_invoke inv = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    enters_block callee cs s1 /\ active_inst callee inst s1 /\
    q = JointConfig
      (<| cf_fn := caller; cf_inst := inv; cf_state := s;
          cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
      (om::oms) FEMPTY (h::hs)
      [OriginCallee cs; OriginObserve
        (OriginSnapshot callee (MAP (op_prov G) ops) FEMPTY FEMPTY inst s1)]
Proof
  simp[Once joint_transition_cases] >> metis_tac[]
QED

Theorem joint_transition_return:
  joint_transition ctx p (SOME (OriginResume fuel fn rinst s ret send post)) q <=>
  ?f stk PG G tn oms om caller_om hs h caller_h inst'.
    p = JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h /\
    active_inst fn rinst s /\ step_inst fuel ctx rinst s = IntRet ret send /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state send)) = SOME post /\
    active_inst f.cf_fn inst' (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    q = JointConfig stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn inst' (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
      (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) hs
      (caller_h ++ [OriginResume fuel fn rinst s ret send post; OriginObserve
        (OriginSnapshot f.cf_fn f.cf_params
          (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
          (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))) inst'
          (post with vs_inst_idx := SUC f.cf_state.vs_inst_idx))])
Proof
  simp[Once joint_transition_cases] >> metis_tac[]
QED

Theorem joint_transition_label_cases:
  joint_transition ctx p ev q ==>
  ev = NONE \/ (?fuel post. ev = SOME (OriginOrdinary fuel post)) \/
  (?fuel post. ev = SOME (OriginBlock fuel post)) \/
  (?fuel fn inst s ret send post.
     ev = SOME (OriginResume fuel fn inst s ret send post))
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> metis_tac[]
QED

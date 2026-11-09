Theory frameExecutionHistory
Ancestors
  ptrDiscipline contextCodegenRel venomExecSemantics venomState venomInst
  list rich_list finite_map

(* Chronological exposed instruction boundaries, local to each frame.
   The saved histories are pushed and popped with the saved caller frames. *)
Inductive frame_history:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     frame_history vs0 ctx [] [] FEMPTY entry_taint fn inst s1 [] [(inst,s1)])
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel hs h.
     frame_history vs0 ctx stk PG G tn fn inst s hs h /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     frame_history vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx) hs
       (h ++ [(inst',s' with vs_inst_idx := SUC s.vs_inst_idx)]))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel hs h.
     frame_history vs0 ctx stk PG G tn fn inst s hs h /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     frame_history vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1 hs (h ++ [(inst',s1)]))
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst hs h.
     frame_history vs0 ctx stk PG G tn caller inv s hs h /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     frame_history vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
       (h::hs) [(inst,s1)])
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel hs h caller_h.
     frame_history vs0 ctx (f::stk) PG G tn fn rinst s (caller_h::hs) h /\
     active_inst fn rinst s /\
     step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
     active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     frame_history vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) hs
       (caller_h ++ [(inst',s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)]))
End

Theorem frame_history_erasure:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    frame_reachable vs0 ctx stk PG G tn fn inst s
Proof
  ho_match_mp_tac frame_history_ind >> rpt strip_tac >>
  metis_tac[frame_reachable_rules]
QED

Theorem frame_history_endpoints:
  !vs0 ctx stk PG G tn fn inst s hs h.
    frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    h <> [] /\ LAST h = (inst,s) /\
    LIST_REL (\f h0. h0 <> [] /\ LAST h0 = (f.cf_inst,f.cf_state)) stk hs
Proof
  ho_match_mp_tac frame_history_ind >> rpt strip_tac >>
  gvs[LAST_APPEND]
QED

Theorem frame_history_current_endpoint:
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    h <> [] /\ LAST h = (inst,s)
Proof
  metis_tac[frame_history_endpoints]
QED

Theorem frame_history_suspended_endpoints:
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    LIST_REL (\f h0. h0 <> [] /\ LAST h0 = (f.cf_inst,f.cf_state)) stk hs
Proof
  metis_tac[frame_history_endpoints]
QED

Theorem frame_history_stack_length:
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==>
    LENGTH hs = LENGTH stk
Proof
  strip_tac >> drule frame_history_suspended_endpoints >>
  simp[LIST_REL_EL_EQN]
QED

Theorem frame_reachable_has_history:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    ?hs h. frame_history vs0 ctx stk PG G tn fn inst s hs h
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac
  >- metis_tac[frame_history_rules]
  >- metis_tac[frame_history_rules]
  >- metis_tac[frame_history_rules]
  >- metis_tac[frame_history_rules]
  >> `LENGTH hs = LENGTH (f::stk)` by
       metis_tac[frame_history_stack_length] >>
  Cases_on `hs` >> gvs[] >> metis_tac[frame_history_rules]
QED

Theorem frame_history_saved_endpoint:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\ n < LENGTH stk ==>
    EL n hs <> [] /\
    LAST (EL n hs) = ((EL n stk).cf_inst,(EL n stk).cf_state)
Proof
  rpt strip_tac >> drule frame_history_suspended_endpoints >>
  simp[LIST_REL_EL_EQN] >> metis_tac[]
QED

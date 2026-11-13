Theory frameOriginReachable
Ancestors
  frameOriginUpdates ptrDiscipline contextCodegenRel venomExecSemantics
  venomState venomInst finite_map list

Inductive origin_frame_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\ active_inst fn inst s1 ==>
     origin_frame_reachable vs0 ctx [] [] FEMPTY entry_taint fn inst s1 [] FEMPTY)
[~next:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' fuel oms om.
     origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
     active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
     inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     origin_frame_reachable vs0 ctx stk PG (step_prov PG G inst s')
       (step_taint inst s s' tn) fn inst'
       (s' with vs_inst_idx := SUC s.vs_inst_idx) oms (origin_step PG om inst s'))
[~block:]
  (!vs0 ctx stk PG G tn fn inst inst' s s' s1 fuel oms om.
     origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
     active_inst fn inst s /\ is_terminator inst.inst_opcode /\
     step_inst fuel ctx inst s = OK s' /\ ~s'.vs_halted /\
     enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     origin_frame_reachable vs0 ctx stk PG (entry_prov fn s' G)
       (entry_taint_vars fn s' tn) fn inst' s1 oms (origin_entry fn s' om))
[~call:]
  (!vs0 ctx stk PG G tn caller inv s nm ops callee args cs s1 inst oms om.
     origin_frame_reachable vs0 ctx stk PG G tn caller inv s oms om /\
     active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     origin_frame_reachable vs0 ctx
       (<| cf_fn := caller; cf_inst := inv; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
       (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
       (om::oms) FEMPTY)
[~ret:]
  (!vs0 ctx f stk PG G tn fn rinst s ret s_end s' inst' fuel oms om caller_om.
     origin_frame_reachable vs0 ctx (f::stk) PG G tn fn rinst s (caller_om::oms) om /\
     active_inst fn rinst s /\ step_inst fuel ctx rinst s = IntRet ret s_end /\
     bind_outputs f.cf_inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
     active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
     origin_frame_reachable vs0 ctx stk f.cf_params
       (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
       f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) oms
       (DRESTRICT caller_om (COMPL (set f.cf_inst.inst_outputs))))
End

Theorem origin_frame_erasure:
  !vs0 ctx stk PG G tn fn inst s oms om.
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    frame_reachable vs0 ctx stk PG G tn fn inst s
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt strip_tac >>
  metis_tac[frame_reachable_rules]
QED

Theorem origin_frame_maps:
  !vs0 ctx stk PG G tn fn inst s oms om.
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    origin_erase om = G /\
    LIST_REL (\f om0. origin_erase om0 = f.cf_prov) stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt strip_tac >>
  gvs[origin_step_erase, origin_entry_erase, origin_erase_restrict]
QED

Theorem origin_frame_stack_length:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    LENGTH oms = LENGTH stk
Proof
  strip_tac >> drule origin_frame_maps >> simp[LIST_REL_EL_EQN]
QED

Theorem frame_reachable_has_origins:
  !vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==>
    ?oms om. origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac
  >- metis_tac[origin_frame_reachable_rules]
  >- metis_tac[origin_frame_reachable_rules]
  >- metis_tac[origin_frame_reachable_rules]
  >- metis_tac[origin_frame_reachable_rules]
  >> `LENGTH oms = LENGTH (f::stk)` by metis_tac[origin_frame_stack_length] >>
  Cases_on `oms` >> gvs[] >> metis_tac[origin_frame_reachable_rules]
QED

Theorem origin_frame_current_map:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    origin_erase om = G
Proof
  metis_tac[origin_frame_maps]
QED

Theorem origin_frame_saved_maps:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    LIST_REL (\f om0. origin_erase om0 = f.cf_prov) stk oms
Proof
  metis_tac[origin_frame_maps]
QED

Theorem origin_frame_current_lookup:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  FLOOKUP G v = SOME site ==>
    ?tag. FLOOKUP om v = SOME (tag,site)
Proof
  rpt strip_tac >> drule origin_frame_current_map >> strip_tac >>
  gvs[origin_erase_lookup, optionTheory.OPTION_MAP_EQ_SOME] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem origin_frame_saved_lookup:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  n < LENGTH stk /\ FLOOKUP (EL n stk).cf_prov v = SOME site ==>
    ?tag. FLOOKUP (EL n oms) v = SOME (tag,site)
Proof
  rpt strip_tac >> drule origin_frame_saved_maps >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `FLOOKUP (origin_erase (EL n oms)) v = SOME site` by metis_tac[] >>
  pop_assum mp_tac >> simp[origin_erase_lookup, optionTheory.OPTION_MAP_EQ_SOME] >>
  metis_tac[pairTheory.PAIR]
QED

Theorem frame_reachable_origin_witnesses:
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  ?oms om. origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
    (!v site. FLOOKUP G v = SOME site ==>
       ?tag. FLOOKUP om v = SOME (tag,site)) /\
    (!n v site. n < LENGTH stk /\ FLOOKUP (EL n stk).cf_prov v = SOME site ==>
       ?tag. FLOOKUP (EL n oms) v = SOME (tag,site))
Proof
  strip_tac >> drule frame_reachable_has_origins >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[origin_frame_current_lookup, origin_frame_saved_lookup]
QED

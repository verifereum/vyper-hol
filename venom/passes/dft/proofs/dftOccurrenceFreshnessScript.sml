(* Future-address cones for dynamic occurrence freshness. *)
Theory dftOccurrenceFreshness
Ancestors
  dftOccurrenceMachine dftOpenErase dftOpenMachine venomExecSemantics venomExecProofs venomInst arithmetic list pred_set

Definition dft_suffix_cone_def:
  dft_suffix_cone (p:(num # num) list) v bb i x <=>
    ?w id tail. x = p ++ [(w,id)] ++ tail /\
      (v < w \/ (w = v /\ MEM id (MAP (\inst. inst.inst_id) (DROP i bb.bb_instructions))))
End

Definition dft_entry_cone_def:
  dft_entry_cone (p:(num # num) list) v x <=>
    ?w id tail. x = p ++ [(w,id)] ++ tail /\ v <= w
End

Theorem dft_suffix_cone_entry:
  dft_suffix_cone p v bb i x ==> dft_entry_cone p v x
Proof
  simp[dft_suffix_cone_def, dft_entry_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[]
QED

Theorem dft_entry_cone_next:
  dft_entry_cone p (SUC v) x ==> dft_suffix_cone p v bb i x
Proof
  simp[dft_suffix_cone_def, dft_entry_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[]
QED

Theorem dft_suffix_cone_shrink:
  dft_suffix_cone p v bb (SUC i) x ==> dft_suffix_cone p v bb i x
Proof
  simp[dft_suffix_cone_def] >> rpt strip_tac >>
  qexistsl_tac [`w`, `id`, `tail`] >> simp[] >>
  gvs[MEM_MAP, MEM_DROP] >>
  qexists_tac `EL (m + SUC i) bb.bb_instructions` >> simp[] >>
  qexists_tac `SUC m` >> simp[ADD_CLAUSES, ADD_COMM]
QED

Theorem dft_suffix_cone_current:
  get_instruction bb i = SOME inst ==>
  dft_suffix_cone p v bb i (p ++ [(v,inst.inst_id)])
Proof
  simp[get_instruction_def, dft_suffix_cone_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[MEM_MAP, MEM_DROP] >> qexists_tac `EL i bb.bb_instructions` >>
  simp[] >> qexists_tac `0` >> simp[]
QED

Theorem dft_suffix_cone_retire:
  ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
  get_instruction bb i = SOME inst ==>
  ~dft_suffix_cone p v bb (SUC i) (p ++ [(v,inst.inst_id)] ++ tail)
Proof
  simp[dft_suffix_cone_def] >> rpt strip_tac >>
  gvs[get_instruction_def, AllCaseEqs(), MEM_MAP, MEM_DROP] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `EL i (MAP (\inst. inst.inst_id) bb.bb_instructions) =
   EL (m + SUC i) (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  `i = m + SUC i` by metis_tac[EL_ALL_DISTINCT_EL_EQ, LENGTH_MAP] >>
  decide_tac
QED

Theorem dft_entry_cone_descendant:
  get_instruction bb i = SOME inst /\
  dft_entry_cone (p ++ [(v,inst.inst_id)]) 0 x ==>
  dft_suffix_cone p v bb i x
Proof
  strip_tac >>
  `dft_suffix_cone p v bb i (p ++ [(v,inst.inst_id)])` by
    (irule dft_suffix_cone_current >> simp[]) >>
  gvs[dft_entry_cone_def, dft_suffix_cone_def] >>
  qexistsl_tac [`v`, `inst.inst_id`, `[(w,id)] ++ tail`] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]
QED

Theorem dft_entry_cone_not_root:
  ~dft_entry_cone (p ++ [(v,id)]) n (p ++ [(v,id)])
Proof
  simp[dft_entry_cone_def]
QED

Theorem dft_suffix_cone_ancestor_exclusion:
  ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
  get_instruction bb i = SOME inst /\
  dft_entry_cone (p ++ [(v,inst.inst_id)]) 0 x ==>
  ~dft_suffix_cone p v bb (SUC i) x
Proof
  strip_tac >> gvs[dft_entry_cone_def] >>
  drule_all dft_suffix_cone_retire >>
  disch_then (qspecl_then [`v`, `[(w,id)] ++ tail`, `p`] mp_tac) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND, CONS_11] >> simp[]
QED

Definition dft_fn_ids_def:
  dft_fn_ids fn <=> EVERY (\bb. ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)) fn.fn_blocks
End

Definition dft_ctx_ids_def:
  dft_ctx_ids ctx <=> !name fn. lookup_function name ctx.ctx_functions = SOME fn ==> dft_fn_ids fn
End

Definition dft_stack_coherent_def:
  (dft_stack_coherent path [] saved <=> path = [] /\ saved = []) /\
  (dft_stack_coherent path (DftCaller fn b bb call caller::rest) saved <=>
    ?p v ss. saved = (p,v)::ss /\ path = p ++ [(v,call.inst_id)] /\
      get_instruction bb caller.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE /\
      dft_fn_ids fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
      dft_stack_coherent p rest ss)
End

Definition dft_occ_valid_def:
  dft_occ_valid c <=>
    case c.dft_occ_core of DftOpen ctl stack n =>
      (case ctl of
         DftEnter fn b s => dft_fn_ids fn /\
           dft_stack_coherent c.dft_occ_path stack c.dft_occ_saved
       | DftAt fn b bb s => dft_fn_ids fn /\
           ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions) /\
           dft_stack_coherent c.dft_occ_path stack c.dft_occ_saved
       | DftDone r => if stack = [] then c.dft_occ_saved = []
           else dft_stack_coherent c.dft_occ_path stack c.dft_occ_saved)
End

Theorem dft_occ_valid_init:
  dft_fn_ids fn ==>
  dft_occ_valid (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
Proof
  simp[dft_occ_init_def, dft_occ_valid_def, dft_stack_coherent_def]
QED

Theorem dft_stack_coherent_fill[simp]:
  dft_stack_coherent path (MAP (dft_fill_frame b) stack) saved =
  dft_stack_coherent path stack saved
Proof
  qid_spec_tac `path` >> qid_spec_tac `saved` >> Induct_on `stack` >>
  simp[dft_stack_coherent_def] >> Cases_on `h` >>
  simp[dft_fill_frame_def, dft_stack_coherent_def]
QED

Theorem dft_fn_ids_lookup:
  dft_fn_ids fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)
Proof
  simp[dft_fn_ids_def, EVERY_MEM] >> strip_tac >>
  drule lookup_block_MEM >> metis_tac[]
QED

Theorem dft_occ_valid_next:
  dft_ctx_ids ctx /\ dft_occ_valid c ==> dft_occ_valid (dft_occ_next a ctx c)
Proof
  Cases_on `c.dft_occ_core` >> rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl`
  >- suspend "enter"
  >- suspend "at"
  >- suspend "done"
QED

Resume dft_occ_valid_next[enter]:
  rename1 `c.dft_occ_core = DftOpen (DftEnter fn budget s) stack n` >>
  simp[dft_occ_valid_def] >> strip_tac >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (irule dft_fn_ids_lookup >> metis_tac[]) >>
  Cases_on `eval_phis s bb.bb_instructions` >> Cases_on `stack` >>
  gvs[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def,
      dft_stack_coherent_def] >>
  Cases_on `h` >> gvs[dft_fill_frame_def, dft_stack_coherent_def]
QED

Resume dft_occ_valid_next[at]:
  rename1 `c.dft_occ_core = DftOpen (DftAt fn budget bb s) stack n` >>
  simp[dft_occ_valid_def] >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_update_def, dft_occ_valid_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
           dft_open_next_def, dft_erase_def] >>
      Cases_on `decode_invoke inst` >>
      simp[dft_open_invoke_def, dft_fill_def, dft_fill_control_def,
           dft_occ_update_def, dft_occ_valid_def] >>
      rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def] >>
      rename1 `lookup_function _ _ = SOME callee` >>
      `dft_fn_ids callee` by metis_tac[dft_ctx_ids_def] >>
      Cases_on `eval_operands pair1 s` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def] >>
      rename1 `eval_operands _ _ = SOME args` >>
      Cases_on `setup_callee callee args s` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def,
           dft_fill_frame_def, dft_stack_coherent_def] >>
      qexistsl_tac [`c.dft_occ_path`, `c.dft_occ_visit`, `c.dft_occ_saved`] >> simp[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
           dft_open_next_def, dft_erase_def] >>
      Cases_on `inst.inst_outputs` >>
      simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >> Cases_on `stack` >>
      gvs[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
          dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def,
          dft_stack_coherent_def] >>
      Cases_on `h` >> gvs[dft_fill_frame_def, dft_stack_coherent_def]) >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `step_inst_base inst s` >> Cases_on `stack` >>
  gvs[dft_open_deliver_def, dft_open_continue_def,
      dft_fill_def, dft_fill_control_def, dft_occ_update_def, dft_occ_valid_def,
      dft_stack_coherent_def] >>
  rpt (IF_CASES_TAC >> gvs[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
                         dft_occ_valid_def]) >>
  Cases_on `h` >> gvs[dft_fill_frame_def, dft_stack_coherent_def]
QED

Resume dft_occ_valid_next[done]:
  Cases_on `e` >> Cases_on `stack` >>
  simp[dft_occ_valid_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
       dft_open_return_def, dft_occ_update_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
  Cases_on `frame` >>
  simp[dft_fill_frame_def, dft_stack_coherent_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `DftCaller fn budget bb call caller` >>
  Cases_on `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_valid_def,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_occ_update_def] >>
  Cases_on `rest` >> gvs[dft_stack_coherent_def] >>
  Cases_on `h` >> gvs[dft_fill_frame_def, dft_stack_coherent_def]
QED

Finalise dft_occ_valid_next

Definition dft_saved_cone_def:
  (dft_saved_cone [] saved x <=> F) /\
  (dft_saved_cone (DftCaller fn b bb call caller::rest) saved x <=>
    ?p v ss. saved = (p,v)::ss /\
      (dft_suffix_cone p v bb (SUC caller.vs_inst_idx) x \/
       dft_saved_cone rest ss x))
End

Definition dft_occ_future_def:
  dft_occ_future c x <=>
    case c.dft_occ_core of DftOpen ctl stack n =>
      dft_saved_cone stack c.dft_occ_saved x \/
      (case ctl of
         DftEnter fn b s => dft_entry_cone c.dft_occ_path c.dft_occ_visit x
       | DftAt fn b bb s => dft_suffix_cone c.dft_occ_path c.dft_occ_visit bb s.vs_inst_idx x
       | DftDone r => F)
End

Theorem dft_saved_cone_fill[simp]:
  dft_saved_cone (MAP (dft_fill_frame b) stack) saved x =
  dft_saved_cone stack saved x
Proof
  qid_spec_tac `saved` >> Induct_on `stack` >>
  simp[dft_saved_cone_def] >> Cases_on `h` >>
  simp[dft_fill_frame_def, dft_saved_cone_def]
QED

Theorem dft_saved_cone_fill_cons[simp]:
  dft_saved_cone (dft_fill_frame b h :: MAP (dft_fill_frame b) t) saved x =
  dft_saved_cone (h::t) saved x
Proof
  metis_tac[dft_saved_cone_fill, MAP]
QED

Theorem dft_saved_cone_exclusion:
  !stack path saved tail.
    dft_stack_coherent path stack saved ==>
    ~dft_saved_cone stack saved (path ++ tail)
Proof
  Induct >> simp[dft_stack_coherent_def, dft_saved_cone_def] >>
  Cases_on `h` >> simp[dft_stack_coherent_def, dft_saved_cone_def] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[dft_suffix_cone_retire] >>
  qpat_x_assum `dft_saved_cone stack ss _` mp_tac >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> metis_tac[]
QED

Theorem dft_occ_event_future:
  dft_occ_valid c /\ dft_occ_event inst addr c ==> dft_occ_future c addr
Proof
  simp[dft_occ_event_def] >> rpt strip_tac >>
  simp[dft_occ_future_def] >> disj2_tac >>
  irule dft_suffix_cone_current >> simp[]
QED

Theorem dft_occ_future_next:
  dft_ctx_ids ctx /\ dft_occ_valid c ==>
  (dft_occ_future (dft_occ_next a ctx c) x ==> dft_occ_future c x)
Proof
  Cases_on `c.dft_occ_core` >> rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl`
  >- suspend "enter"
  >- suspend "at"
  >- suspend "done"
QED

Resume dft_occ_future_next[enter]:
  rename1 `c.dft_occ_core = DftOpen (DftEnter fn budget s) stack n` >>
  simp[dft_occ_valid_def] >> strip_tac >>
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_future_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
          dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> Cases_on `stack` >>
  gvs[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
      dft_occ_future_def, dft_saved_cone_def] >>
  metis_tac[dft_suffix_cone_entry]
QED

Resume dft_occ_future_next[at]:
  rename1 `c.dft_occ_core = DftOpen (DftAt fn budget bb s) stack n` >>
  simp[dft_occ_valid_def] >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "push" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  suspend "ordinary"
QED

Resume dft_occ_future_next[push]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_future_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_open_invoke_def, dft_fill_def, dft_fill_control_def,
       dft_occ_update_def, dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def, dft_fill_frame_def] >>
  metis_tac[dft_suffix_cone_shrink, dft_entry_cone_descendant]
QED

Resume dft_occ_future_next[gas]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_future_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >> Cases_on `stack` >>
  gvs[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
      dft_fill_def, dft_fill_control_def, dft_occ_update_def,
      dft_occ_future_def, dft_saved_cone_def] >>
  metis_tac[dft_suffix_cone_shrink]
QED

Resume dft_occ_future_next[ordinary]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def, dft_occ_future_def] >>
  Cases_on `step_inst_base inst s` >> Cases_on `stack` >>
  gvs[dft_open_deliver_def, dft_open_continue_def,
      dft_fill_def, dft_fill_control_def, dft_occ_update_def,
      dft_occ_future_def, dft_saved_cone_def] >>
  rpt (IF_CASES_TAC >> gvs[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
                         dft_occ_future_def]) >>
  metis_tac[dft_suffix_cone_shrink, dft_entry_cone_next]
QED

Resume dft_occ_future_next[done]:
  Cases_on `e` >> Cases_on `stack` >>
  simp[dft_occ_valid_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def, dft_erase_def,
       dft_open_return_def, dft_occ_update_def, dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (frame::rest) n` >>
  Cases_on `frame` >>
  simp[dft_fill_frame_def, dft_stack_coherent_def] >>
  strip_tac >> gvs[] >>
  rename1 `DftCaller fn budget bb call caller` >>
  Cases_on `bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_fill_def, dft_fill_control_def,
       dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
       dft_occ_update_def, dft_occ_future_def, dft_saved_cone_def] >>
  metis_tac[]
QED

Finalise dft_occ_future_next

Theorem dft_entry_cone_retire:
  ~dft_entry_cone p (SUC v) (p ++ [(v,id)])
Proof
  simp[dft_entry_cone_def]
QED

Theorem dft_occ_event_retired:
  dft_ctx_ids ctx /\ dft_occ_valid c /\ dft_occ_event inst addr c ==>
  ~dft_occ_future (dft_occ_next a ctx c) addr
Proof
  simp[dft_occ_event_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  gvs[dft_occ_valid_def] >>
  `~dft_saved_cone stack c.dft_occ_saved
      (c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)])` by
    (irule dft_saved_cone_exclusion >> simp[]) >>
  `~dft_suffix_cone c.dft_occ_path c.dft_occ_visit bb (SUC s.vs_inst_idx)
      (c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)])` by
    (drule_all dft_suffix_cone_retire >>
     disch_then (qspecl_then [`c.dft_occ_visit`, `[]`, `c.dft_occ_path`] mp_tac) >> simp[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "push" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  suspend "ordinary"
QED

Resume dft_occ_event_retired[push]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `decode_invoke inst` >>
  simp[dft_open_invoke_def, dft_fill_def, dft_fill_control_def,
       dft_occ_update_def, dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def, dft_fill_frame_def,
       dft_entry_cone_not_root]
QED

Resume dft_occ_event_retired[gas]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_occ_future_def, dft_saved_cone_def] >>
  rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >> Cases_on `stack` >>
  gvs[dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
      dft_fill_def, dft_fill_control_def, dft_occ_update_def,
      dft_occ_future_def, dft_saved_cone_def]
QED

Resume dft_occ_event_retired[ordinary]:
  simp[dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
       dft_open_next_def, dft_erase_def] >>
  Cases_on `step_inst_base inst s` >> Cases_on `stack` >>
  gvs[dft_open_deliver_def, dft_open_continue_def,
      dft_fill_def, dft_fill_control_def, dft_occ_update_def,
      dft_occ_future_def, dft_saved_cone_def] >>
  rpt (IF_CASES_TAC >> gvs[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
                         dft_occ_future_def, dft_entry_cone_retire])
QED

Finalise dft_occ_event_retired

Theorem dft_occ_valid_iter:
  !j c. dft_ctx_ids ctx /\ dft_occ_valid c ==>
    dft_occ_valid (FUNPOW (dft_occ_next a ctx) j c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_occ_valid_next]
QED

Theorem dft_occ_future_iter:
  !j c. dft_ctx_ids ctx /\ dft_occ_valid c /\
    dft_occ_future (FUNPOW (dft_occ_next a ctx) j c) x ==>
    dft_occ_future c x
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  metis_tac[dft_occ_valid_iter, dft_occ_future_next]
QED

Theorem dft_occ_event_later:
  dft_ctx_ids ctx /\ dft_occ_valid c /\ dft_occ_event inst addr c ==>
  ~dft_occ_event inst' addr (FUNPOW (dft_occ_next a ctx) (SUC j) c)
Proof
  rpt strip_tac >>
  `~dft_occ_future (dft_occ_next a ctx c) addr` by
    metis_tac[dft_occ_event_retired] >>
  `dft_occ_valid (dft_occ_next a ctx c)` by metis_tac[dft_occ_valid_next] >>
  `dft_occ_valid (FUNPOW (dft_occ_next a ctx) j (dft_occ_next a ctx c))` by
    metis_tac[dft_occ_valid_iter] >>
  gvs[FUNPOW] >>
  metis_tac[dft_occ_event_future, dft_occ_future_iter]
QED

Theorem dft_occ_event_unique:
  dft_ctx_ids ctx /\ dft_occ_valid c /\
  dft_occ_event inst addr (FUNPOW (dft_occ_next a ctx) j c) /\
  dft_occ_event inst' addr (FUNPOW (dft_occ_next a ctx) k c) ==> j = k
Proof
  wlog_tac `j <= k` [`j`, `k`, `inst`, `inst'`] >- metis_tac[LESS_EQ_CASES] >>
  rpt strip_tac >> Cases_on `j = k` >- simp[] >>
  `?d. k = SUC d + j` by (qexists_tac `k - j - 1` >> decide_tac) >>
  qpat_x_assum `k = _` SUBST_ALL_TAC >>
  qpat_x_assum `dft_occ_event inst' _ _` mp_tac >>
  pure_rewrite_tac [FUNPOW_ADD] >> strip_tac >>
  `dft_occ_valid (FUNPOW (dft_occ_next a ctx) j c)` by
    metis_tac[dft_occ_valid_iter] >>
  metis_tac[dft_occ_event_later]
QED

Theorem dft_occ_gas_event_unique:
  dft_ctx_ids ctx /\ dft_occ_valid c /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a ctx) j c) /\
  dft_occ_gas_event inst' addr (FUNPOW (dft_occ_next a ctx) k c) ==> j = k
Proof
  simp[dft_occ_gas_event_def] >> metis_tac[dft_occ_event_unique]
QED

Theorem dft_occ_init_event_unique:
  dft_ctx_ids ctx /\ dft_fn_ids fn /\
  dft_occ_event inst addr
    (FUNPOW (dft_occ_next a ctx) j (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))) /\
  dft_occ_event inst' addr
    (FUNPOW (dft_occ_next a ctx) k (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))) ==>
  j = k
Proof
  metis_tac[dft_occ_valid_init, dft_occ_event_unique]
QED

Theorem dft_occ_init_gas_event_unique:
  dft_ctx_ids ctx /\ dft_fn_ids fn /\
  dft_occ_gas_event inst addr
    (FUNPOW (dft_occ_next a ctx) j (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))) /\
  dft_occ_gas_event inst' addr
    (FUNPOW (dft_occ_next a ctx) k (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))) ==>
  j = k
Proof
  metis_tac[dft_occ_valid_init, dft_occ_gas_event_unique]
QED

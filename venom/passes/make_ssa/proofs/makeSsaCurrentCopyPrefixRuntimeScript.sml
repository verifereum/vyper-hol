Theory makeSsaCurrentCopyPrefixRuntime
Ancestors
  makeSsaCurrentPrefixRuntime list rich_list arithmetic pred_set venomExecSemantics venomInst venomState stateFrame

Definition current_prefix_steps_def:
  (current_prefix_steps fuel C [] st post <=> post = st) /\
  (current_prefix_steps fuel C (inst::xs) st post <=>
    ~is_terminator inst.inst_opcode /\
    ?mid. step_inst fuel C inst st = OK mid /\
      current_prefix_steps fuel C xs
        (mid with vs_inst_idx := SUC st.vs_inst_idx) post)
End

Definition current_copy_prefix_ready_def:
  (current_copy_prefix_ready D [] <=> T) /\
  (current_copy_prefix_ready D (inst::xs) <=>
    (inst.inst_opcode = NOP /\ inst.inst_operands = [] /\
     inst.inst_outputs = [] /\ current_copy_prefix_ready D xs) \/
    (?dst src. inst.inst_opcode = ASSIGN /\
     inst.inst_outputs = [dst] /\ inst.inst_operands = [Var src] /\
     src IN D /\ current_copy_prefix_ready (dst INSERT D) xs))
End

Theorem current_prefix_steps_index:
  !xs st post. current_prefix_steps fuel C xs st post ==>
    post.vs_inst_idx = st.vs_inst_idx + LENGTH xs
Proof
  Induct >> simp[current_prefix_steps_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem current_prefix_steps_exec_block:
  !xs st post rest.
  current_prefix_steps fuel C xs st post /\
  DROP st.vs_inst_idx bb.bb_instructions = xs ++ rest ==>
  exec_block fuel C bb st = exec_block fuel C bb post
Proof
  Induct >> simp[current_prefix_steps_def] >> rpt strip_tac >>
  `st.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `get_instruction bb st.vs_inst_idx = SOME h` by
    (simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``HD : instruction list -> instruction``) >>
     simp[HD_DROP]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >> simp[] >>
  first_x_assum irule >> simp[] >> qexists_tac `rest` >>
  qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``DROP 1 : instruction list -> instruction list``) >>
  simp[DROP_DROP_T, ADD1, ADD_COMM]
QED

Theorem current_copy_prefix_total:
  !xs D st. current_copy_prefix_ready D xs /\
  (!x. x IN D ==> IS_SOME (lookup_var x st)) ==>
  ?post. current_prefix_steps fuel C xs st post /\
    execution_frame post = execution_frame st /\
    post.vs_current_bb = st.vs_current_bb /\
    post.vs_prev_bb = st.vs_prev_bb /\
    (!x. x IN D UNION set (FLAT (MAP (\inst. inst.inst_outputs) xs)) ==>
      IS_SOME (lookup_var x post))
Proof
  Induct >> simp[current_copy_prefix_ready_def, current_prefix_steps_def] >>
  rpt gen_tac >> strip_tac
  >- (first_x_assum (qspecl_then [`D`, `st with vs_inst_idx := SUC st.vs_inst_idx`] mp_tac) >>
      (impl_tac >- gvs[lookup_var_def]) >>
      strip_tac >> qexists_tac `post` >>
      gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def] >>
      metis_tac[]) >>
  `IS_SOME (lookup_var src st)` by metis_tac[] >>
  drule_all current_prefix_var_copy_success >>
  disch_then (qspecl_then [`fuel`, `C`] strip_assume_tac) >>
  first_x_assum (qspecl_then
    [`dst INSERT D`, `(update_var dst v st) with vs_inst_idx := SUC st.vs_inst_idx`] mp_tac) >>
  (impl_tac >-
    (gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `x = dst` >> gvs[])) >>
  strip_tac >> qexists_tac `post` >>
  gvs[is_terminator_def, update_var_def] >> metis_tac[]
QED

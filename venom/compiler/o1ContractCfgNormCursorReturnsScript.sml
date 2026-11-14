Theory o1ContractCfgNormCursorReturns
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNormCursorCalls o1ContractCfgNorm
  cfgNormSupplySim cfgNormDefs o1PassLift simplifyCfgSimTools
  venomExecSemantics venomExecProofs venomStepProps venomInst venomState
  venomWf unitShapeDefs contextCodegenRel stateFrame stateEquiv opcodeClass
  ctxLookupAgreeHelpers venomRetProps callLayoutDefs list rich_list pair option

Theorem cfg_norm_cursors_return_final[local]:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  active_inst fn callinst a /\ supply_prefix_defined fn a /\ ~a.vs_halted /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a e)) = SOME w /\
  active_inst fn next (w with vs_inst_idx := SUC a.vs_inst_idx) ==>
  cfg_norm_cursors C [(s,fn,NONE)]
    [((next,w with vs_inst_idx := SUC a.vs_inst_idx),NONE)]
Proof
  strip_tac >> `wf_function fn` by gvs[supply_norm_inv_def] >>
  `supply_prefix_defined fn (w with vs_inst_idx := SUC a.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn callinst a` mp_tac >> simp[active_inst_def] >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >>
     irule supply_prefix_defined_return >> metis_tac[]) >>
  `~w.vs_halted` by
    (drule bind_outputs_ok_halted >> Cases_on `ret.iret_adopt_fmp` >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  irule cfg_norm_cursors_final >> simp[]
QED

Theorem cfg_norm_cursors_body_return[local]:
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),pending)::((callinst,v),other)::cursors) /\
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds)
    (((next,w with vs_inst_idx := SUC v.vs_inst_idx),other')::cursors') /\
  callinst.inst_opcode = INVOKE /\ execution_frame e = execution_frame e' /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state v e')) = SOME w ==>
  ?u first. inst.inst_opcode = INVOKE /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state a e)) = SOME u /\
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((first,u with vs_inst_idx := SUC a.vs_inst_idx),NONE)::
        ((next,w with vs_inst_idx := SUC v.vs_inst_idx),other')::cursors')
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_::_) (((inst,a),pending)::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[]
  >- (`wf_function fn` by gvs[supply_norm_inv_def] >>
      `active_inst next_fn next (w with vs_inst_idx := SUC v.vs_inst_idx) /\
       supply_norm_inv s1 next_fn /\ ~(w with vs_inst_idx := SUC v.vs_inst_idx).vs_halted` by
        metis_tac[cfg_norm_cursors_head] >>
      `wf_function next_fn /\ ~w.vs_halted` by gvs[supply_norm_inv_def] >>
      `((EL v.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE) /\
       (EL v.vs_inst_idx bb.bb_instructions).inst_outputs =
       (EL v.vs_inst_idx
         (supply_block_image pred target split repls bb).bb_instructions).inst_outputs` by
        metis_tac[supply_block_image_index] >>
      mp_tac (Q.INST [`fn'` |-> `next_fn`, `next'` |-> `next`]
        supply_body_return_prefix) >> simp[] >> strip_tac >>
      `~u.vs_halted` by
        metis_tac[supply_state_agree_halted, supply_state_agree_inst_idx] >>
      qexistsl [`u`, `EL (SUC a.vs_inst_idx) bb.bb_instructions`] >> simp[] >>
      irule cfg_norm_cursors_body >> gvs[] >> qexists_tac `bb` >> simp[]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by
    gvs[supply_norm_inv_def] >>
  drule_all supply_split_index_shape >> simp[]
QED

Theorem cfg_norm_cursors_intret_head[local]:
  cfg_norm_cursors C (round::rounds)
    (((inst,a),pending)::((next,v),other)::cursors) /\
  step_inst fuel D next v = IntRet ret e ==>
  ?u. step_inst fuel C inst a = IntRet ret u /\ execution_frame u = execution_frame e
Proof
  strip_tac >>
  `is_terminator next.inst_opcode /\ next.inst_opcode <> INVOKE /\
   next.inst_opcode <> ASSIGN /\ next.inst_opcode <> JMP` by
    (drule step_inst_IntRet_opcode >> simp[is_raw_return_opcode_def] >>
     strip_tac >> simp[is_terminator_def]) >>
  qpat_x_assum `cfg_norm_cursors C (_::_) (_::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[]
  >- (`fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
      `inst_wf (EL v.vs_inst_idx bb.bb_instructions)` by
        metis_tac[active_inst_wf] >>
      `label_positions_ok (EL v.vs_inst_idx bb.bb_instructions)` by
        (gvs[fn_insts_def, EVERY_MEM] >>
         metis_tac[EL_MEM, MEM_fn_insts_blocks]) >>
      `is_terminator (EL v.vs_inst_idx bb.bb_instructions).inst_opcode /\
       (EL v.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
        metis_tac[supply_block_image_index] >>
      mp_tac (Q.INST [`inst` |-> `EL v.vs_inst_idx bb.bb_instructions`,
        `i` |-> `v.vs_inst_idx`, `st` |-> `a`, `st'` |-> `v`,
        `ctx` |-> `D`] supply_block_image_step_terminator) >>
      simp[] >> strip_tac >>
      Cases_on `step_inst fuel D (EL v.vs_inst_idx bb.bb_instructions) a` >>
      gvs[lift_result_def, Excl "execution_frame_def"] >>
      rename1 `step_inst fuel D (EL v.vs_inst_idx bb.bb_instructions) a =
        IntRet ret source_end` >>
      qexists_tac `source_end` >> conj_tac
      >- metis_tac[step_inst_non_invoke] >>
      gvs[supply_state_agree_def, Excl "execution_frame_def"]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by
    gvs[supply_norm_inv_def] >>
  drule_all supply_split_index_shape >> simp[]
QED

Theorem cfg_norm_cursors_callee_ret:
  !rounds C cursors inst v fuel D ret e.
  cfg_norm_cursors C rounds cursors /\ LAST cursors = ((inst,v),NONE) /\
  step_inst fuel D inst v = IntRet ret e ==>
  ?first a u pending. HD cursors = ((first,a),pending) /\
    step_inst fuel C first a = IntRet ret u /\ execution_frame u = execution_frame e
Proof
  Induct_on `rounds`
  >- (rpt strip_tac >> drule cfg_norm_cursors_lengths >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `cursors <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors` >> gvs[Excl "execution_frame_def"] >>
  rename1 `cfg_norm_cursors C (h::rounds) (cursor::tail)` >>
  Cases_on `rounds = []`
  >- (gvs[Excl "execution_frame_def"] >>
      qpat_assum `cfg_norm_cursors C [_] (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >>
      gvs[Excl "execution_frame_def"] >> qexists_tac `e` >> simp[] >>
      drule step_inst_IntRet_opcode >> simp[is_raw_return_opcode_def] >> strip_tac >>
      fs[step_inst_non_invoke]) >>
  `cfg_norm_cursors C rounds tail` by metis_tac[cfg_norm_cursors_tail] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `LAST tail = ((inst,v),NONE)` by gvs[LAST_CONS_cond] >>
  first_x_assum drule_all >> strip_tac >>
  `tail = ((first,a),pending)::TL tail` by (Cases_on `tail` >> gvs[]) >>
  PairCases_on `cursor` >> simp[] >>
  `?u1. step_inst fuel C cursor0 cursor1 = IntRet ret u1 /\
    execution_frame u1 = execution_frame u` by
    (irule cfg_norm_cursors_intret_head >> metis_tac[]) >>
  qexists_tac `u1` >> gvs[execution_frame_def]
QED

Theorem cfg_norm_cursors_extend_return[local]:
  cfg_norm_cursors C (round::rounds)
    (cursor::((callinst,v),pending)::tail) /\
  cfg_norm_cursors C rounds
    (((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE)::new_tail) /\
  callinst.inst_opcode = INVOKE /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state v e)) = SOME w ==>
  ?cursor' inst a u after old_pending.
    cursor = ((inst,a),old_pending) /\ inst.inst_opcode = INVOKE /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state a e)) = SOME u /\
    cursor' = ((after,u with vs_inst_idx := SUC a.vs_inst_idx),NONE) /\
    cfg_norm_cursors C (round::rounds)
      (cursor'::((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE)::new_tail)
Proof
  strip_tac >>
  qpat_assum `cfg_norm_cursors C (_::_) (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`e'` |-> `e`] cfg_norm_cursors_body_return)) >>
  strip_tac >> metis_tac[]
QED

(* Restore the saved caller list using this actual return, leaving the
   source caller fixed by its old head cell. *)
Theorem cfg_norm_cursors_return:
  !rounds C saved t fn callinst v ret e8 e9 w next.
  cfg_norm_cursors C rounds saved /\ LAST rounds = (t,fn,NONE) /\
  LAST saved = ((callinst,v),NONE) /\ callinst.inst_opcode = INVOKE /\
  execution_frame e8 = execution_frame e9 /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state v e9)) = SOME w /\
  active_inst fn next (w with vs_inst_idx := SUC v.vs_inst_idx) ==>
  ?saved' first a u after pending.
    cfg_norm_cursors C rounds saved' /\
    LAST saved' = ((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE) /\
    HD saved = ((first,a),pending) /\ first.inst_opcode = INVOKE /\
    bind_outputs first.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state a e8)) = SOME u /\
    HD saved' = ((after,u with vs_inst_idx := SUC a.vs_inst_idx),NONE)
Proof
  Induct_on `rounds`
  >- (rpt strip_tac >> drule cfg_norm_cursors_lengths >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `saved <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `saved` >> gvs[] >>
  rename1 `cfg_norm_cursors C (h::rounds) (cursor::tail)` >>
  Cases_on `rounds = []`
  >- (gvs[] >>
      qpat_assum `cfg_norm_cursors C [_] (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[] >>
      rename1 `bind_outputs callinst.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state v e9)) = SOME w` >>
      `merge_callee_state v e8 = merge_callee_state v e9` by
        (irule execution_frame_merge_callee >> gvs[execution_frame_def]) >>
      qexists_tac `[((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE)]` >> simp[] >>
      irule cfg_norm_cursors_return_final >> simp[] >> metis_tac[]) >>
  `cfg_norm_cursors C rounds tail` by metis_tac[cfg_norm_cursors_tail] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `LAST rounds = (t,fn,NONE) /\ LAST tail = ((callinst,v),NONE)` by
    gvs[LAST_CONS_cond] >>
  first_x_assum drule_all >>
  disch_then (qx_choose_then `new_tail` (qx_choose_then `middle`
    (qx_choose_then `b` (qx_choose_then `x` (qx_choose_then `after`
      (qx_choose_then `old_pending` strip_assume_tac)))))) >>
  `new_tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `tail = ((middle,b),old_pending)::TL tail /\
   new_tail = ((after,x with vs_inst_idx := SUC b.vs_inst_idx),NONE)::TL new_tail` by
    (Cases_on `tail` >> Cases_on `new_tail` >> gvs[]) >>
  `?cursor' first a u done pending.
    cursor = ((first,a),pending) /\ first.inst_opcode = INVOKE /\
    bind_outputs first.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state a e8)) = SOME u /\
    cursor' = ((done,u with vs_inst_idx := SUC a.vs_inst_idx),NONE) /\
    cfg_norm_cursors C (h::rounds) (cursor'::new_tail)` by
    (qpat_assum `new_tail = _` (fn th => ONCE_REWRITE_TAC[th]) >>
     irule cfg_norm_cursors_extend_return >> metis_tac[]) >>
  qexistsl [`cursor'::new_tail`, `first`, `a`, `u`, `done`, `pending`] >>
  simp[LAST_CONS_cond]
QED

Theorem cfg_norm_cursors_ret:
  cfg_norm_cursors C callee_rounds callee_cursors /\
  HD callee_cursors = ((rinst8,s8),ret_pending) /\
  LAST callee_cursors = ((rinst9,s9),NONE) /\
  cfg_norm_cursors C rounds saved /\ LAST rounds = (t,fn,NONE) /\
  HD saved = ((call8,a8),pending) /\ LAST saved = ((call9,a9),NONE) /\
  call9.inst_opcode = INVOKE /\ step_inst fuel D rinst9 s9 = IntRet ret e9 /\
  bind_outputs call9.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state a9 e9)) = SOME w9 /\
  active_inst fn next9 (w9 with vs_inst_idx := SUC a9.vs_inst_idx) ==>
  ?e8 saved' w8 next8.
    step_inst fuel C rinst8 s8 = IntRet ret e8 /\
    execution_frame e8 = execution_frame e9 /\
    bind_outputs call8.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state a8 e8)) = SOME w8 /\
    cfg_norm_cursors C rounds saved' /\
    LAST saved' = ((next9,w9 with vs_inst_idx := SUC a9.vs_inst_idx),NONE) /\
    HD saved' = ((next8,w8 with vs_inst_idx := SUC a8.vs_inst_idx),NONE)
Proof
  strip_tac >> drule_all cfg_norm_cursors_callee_ret >>
  disch_then (qx_choose_then `source_inst` (qx_choose_then `source_state`
    (qx_choose_then `source_end` (qx_choose_then `child_pending` strip_assume_tac)))) >>
  gvs[Excl "execution_frame_def"] >>
  `execution_frame source_end = execution_frame e9` by gvs[execution_frame_def] >>
  drule_all cfg_norm_cursors_return >> strip_tac >>
  gvs[Excl "execution_frame_def"] >> metis_tac[]
QED

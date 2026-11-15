Theory o1ContractCfgNormCursorBlocks
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNorm o1PassLift cfgNormSupplySim
  cfgNormDefs venomExecSemantics venomExecProofs venomStepProps venomInst
  venomState venomWf unitShapeDefs stateFrame stateEquiv contextCodegenRel
  simplifyCfgStruct list rich_list arithmetic pair option ctxLookupAgreeHelpers

Theorem supply_body_terminator_exit_prefix:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s') /\
  MEM bb fn.fn_blocks /\
  a.vs_current_bb = bb.bb_label /\ v.vs_current_bb = bb.bb_label /\
  a.vs_inst_idx = v.vs_inst_idx /\ a.vs_inst_idx < LENGTH bb.bb_instructions /\
  inst = EL a.vs_inst_idx bb.bb_instructions /\
  inst' = EL v.vs_inst_idx
    (supply_block_image pred target split repls bb).bb_instructions /\
  active_inst fn inst a /\ supply_prefix_defined fn a /\ supply_state_agree fn a v /\
  is_terminator inst'.inst_opcode /\ step_inst fuel D inst' v = OK w /\ ~w.vs_halted ==>
  ?u. is_terminator inst.inst_opcode /\ step_inst fuel C inst a = OK u /\
    ~u.vs_halted /\ supply_entry_defined fn u /\
    supply_entry_pair fn s pred target split repls u w
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
  `is_terminator inst.inst_opcode` by metis_tac[supply_block_image_index] >>
  `inst_wf inst /\ label_positions_ok inst` by
    (qpat_x_assum `EVERY label_positions_ok _` mp_tac >>
     rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
     simp[EVERY_MEM] >> strip_tac >> gvs[fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  `bb_well_formed bb` by metis_tac[wf_function_def, EVERY_MEM] >>
  `inst = LAST bb.bb_instructions` by
    metis_tac[bb_well_formed_terminator_last, EL_MEM] >>
  `?u. step_inst fuel D inst a = OK u /\
       supply_body_exit fn pred target split bb u w` by
    (mp_tac (Q.INST [`ctx` |-> `D`, `st` |-> `a`, `st'` |-> `v`,
                    `i` |-> `a.vs_inst_idx`] supply_block_image_step_terminator) >>
     simp[] >> Cases_on `step_inst fuel D inst a` >>
     gvs[lift_result_def, supply_body_exit_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `step_inst fuel C inst a = OK u` by metis_tac[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[supply_body_exit_def, supply_state_agree_halted] >>
  `supply_entry_defined fn u` by metis_tac[supply_prefix_terminator_entry] >>
  qexists_tac `u` >> simp[] >> irule supply_prefix_exit_pair >> metis_tac[]
QED

Theorem cfg_norm_cursors_split_block[local]:
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),SOME(u,k))::((next,v),pending)::cursors) /\
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next',z),pending')::cursors') /\
  is_terminator next.inst_opcode /\ step_inst fuel D next v = OK w /\
  ~w.vs_halted /\ enters_block next_fn w z ==>
  ?cursor'. cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (cursor'::((next',z),pending')::cursors') /\
    ?first b. is_terminator inst.inst_opcode /\ step_inst k C inst a = OK u /\
      ~u.vs_halted /\ enters_block fn u b /\ FST cursor' = (first,b)
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_::_) (((inst,a),SOME(u,k))::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
  qpat_assum `!n ctx. _` (qspecl_then [`fuel`, `D`] strip_assume_tac) >>
  mp_tac (Q.INST [`bb` |-> `split`, `ctx` |-> `D`,
    `inst` |-> `EL v.vs_inst_idx split.bb_instructions`]
    supply_exec_block_step_residual) >> simp[] >> strip_tac >>
  `supply_ready fn pred target split repls u w` by metis_tac[] >>
  `?first b. enters_block fn u b /\
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((first,b),NONE)::((next',z),pending')::cursors')` by
    (irule cfg_norm_cursors_ready_body >> simp[] >> metis_tac[]) >>
  metis_tac[pairTheory.FST]
QED

Theorem cfg_norm_cursors_block_final[local]:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  active_inst fn inst a /\ supply_prefix_defined fn a /\
  is_terminator inst.inst_opcode /\ step_inst fuel D inst a = OK w /\
  ~w.vs_halted /\ enters_block fn w z /\ active_inst fn next z ==>
  cfg_norm_cursors C [(s,fn,NONE)] [((next,z),NONE)]
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
  `supply_entry_defined fn w` by metis_tac[supply_prefix_terminator_entry] >>
  `supply_prefix_defined fn z` by metis_tac[supply_prefix_enters_block] >>
  `~z.vs_halted` by
    (gvs[enters_block_def] >> metis_tac[eval_phis_preserves_halted]) >>
  irule cfg_norm_cursors_final >> simp[]
QED

Theorem cfg_norm_cursors_body_block[local]:
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),NONE)::((next,v),pending)::cursors) /\
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next',z),pending')::cursors') /\
  is_terminator next.inst_opcode /\ step_inst fuel D next v = OK w /\
  ~w.vs_halted /\ enters_block next_fn w z ==>
  ?cursor'. cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (cursor'::((next',z),pending')::cursors') /\
    (FST cursor' = (inst,a) \/
     ?u k first b. is_terminator inst.inst_opcode /\ step_inst k C inst a = OK u /\
       ~u.vs_halted /\ enters_block fn u b /\ FST cursor' = (first,b))
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_::_) (((inst,a),NONE)::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
  `wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  `active_inst next_fn next' z` by metis_tac[cfg_norm_cursors_head] >>
  mp_tac (Q.INST [`s'` |-> `s1`,
    `inst` |-> `EL v.vs_inst_idx bb.bb_instructions`,
    `inst'` |-> `EL v.vs_inst_idx
      (supply_block_image pred target split repls bb).bb_instructions`]
    supply_body_terminator_exit_prefix) >> simp[] >> strip_tac >>
  qpat_x_assum `supply_entry_pair _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[supply_entry_pair_def])
  >- (`?first b. enters_block fn u b /\
        cfg_norm_cursors C
          ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
          (((first,b),NONE)::((next',z),pending')::cursors')` by
        (irule cfg_norm_cursors_ready_body >> simp[] >> metis_tac[]) >>
      metis_tac[pairTheory.FST]) >>
  mp_tac (Q.INST [`fn'` |-> `next_fn`, `s'` |-> `s1`, `next` |-> `next'`,
    `inst` |-> `EL v.vs_inst_idx bb.bb_instructions`]
    supply_pending_split_entry) >> simp[] >> strip_tac >>
  `!n ctx. ?m. exec_block n ctx split z = OK m /\
     supply_ready fn pred target split repls u m` by
    (rpt gen_tac >>
     mp_tac (Q.INST [`fn'` |-> `next_fn`, `s'` |-> `s1`, `next` |-> `next'`,
       `D` |-> `ctx`, `inst` |-> `EL v.vs_inst_idx bb.bb_instructions`]
       supply_pending_split_entry) >> simp[] >> metis_tac[]) >>
  `u.vs_current_bb = target.bb_label /\ u.vs_prev_bb = SOME pred.bb_label` by
    gvs[supply_pending_def] >>
  `0 < LENGTH split.bb_instructions` by
    metis_tac[build_split_block_supply_well_formed, bb_well_formed_def,
              LENGTH_NIL, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((EL v.vs_inst_idx bb.bb_instructions,a),SOME(u,fuel))::
      ((next',z),pending')::cursors')` by
    (irule cfg_norm_cursors_split >> gvs[]) >>
  metis_tac[pairTheory.FST]
QED

Theorem cfg_norm_cursors_extend_block[local]:
  cfg_norm_cursors C (round::rounds) (cursor::cursors) /\
  cfg_norm_cursors C rounds cursors' /\
  (FST (HD cursors') = FST (HD cursors) \/
   ?inst a u k next b. FST (HD cursors) = (inst,a) /\
     is_terminator inst.inst_opcode /\ step_inst k C inst a = OK u /\
     ~u.vs_halted /\ enters_block (FST (SND (HD rounds))) u b /\
     FST (HD cursors') = (next,b)) ==>
  ?cursor'. cfg_norm_cursors C (round::rounds) (cursor'::cursors') /\
    (FST cursor' = FST cursor \/
     ?inst a u k next b. FST cursor = (inst,a) /\
       is_terminator inst.inst_opcode /\ step_inst k C inst a = OK u /\
       ~u.vs_halted /\ enters_block (FST (SND round)) u b /\ FST cursor' = (next,b))
Proof
  strip_tac
  >- (qexists_tac `cursor` >> simp[] >>
      irule cfg_norm_cursors_replace_tail >> metis_tac[]) >>
  `cursors' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors'` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  qpat_assum `cfg_norm_cursors C (_::_) (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[]
  >- metis_tac[cfg_norm_cursors_lengths]
  >- (drule_all cfg_norm_cursors_body_block >> strip_tac >>
      metis_tac[pairTheory.FST]) >>
  drule_all cfg_norm_cursors_split_block >> strip_tac >>
  metis_tac[pairTheory.FST]
QED

Theorem cfg_norm_cursors_block:
  !rounds C cursors t fn inst v fuel D w z next.
  cfg_norm_cursors C rounds cursors /\ LAST rounds = (t,fn,NONE) /\
  LAST cursors = ((inst,v),NONE) /\ is_terminator inst.inst_opcode /\
  step_inst fuel D inst v = OK w /\ ~w.vs_halted /\
  enters_block fn w z /\ active_inst fn next z ==>
  ?cursors'. cfg_norm_cursors C rounds cursors' /\ LAST cursors' = ((next,z),NONE) /\
    (FST (HD cursors') = FST (HD cursors) \/
     ?first a u k after b. FST (HD cursors) = (first,a) /\
       is_terminator first.inst_opcode /\ step_inst k C first a = OK u /\
       ~u.vs_halted /\ enters_block (FST (SND (HD rounds))) u b /\
       FST (HD cursors') = (after,b))
Proof
  Induct_on `rounds`
  >- (rpt strip_tac >> drule cfg_norm_cursors_lengths >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `cursors <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors` >> gvs[] >>
  rename1 `cfg_norm_cursors C (h::rounds) (cursor::tail)` >>
  Cases_on `rounds = []`
  >- (gvs[] >>
      qpat_assum `cfg_norm_cursors C [_] (_::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[] >>
      rename1 `step_inst fuel D inst v = OK w` >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      qexists_tac `[((next,z),NONE)]` >> simp[] >>
      conj_tac >- (irule cfg_norm_cursors_block_final >> simp[] >> metis_tac[]) >>
      disj2_tac >> qexistsl [`w`, `fuel`] >> simp[] >>
      metis_tac[step_inst_non_invoke]) >>
  `cfg_norm_cursors C rounds tail` by metis_tac[cfg_norm_cursors_tail] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `LAST rounds = (t,fn,NONE) /\ LAST tail = ((inst,v),NONE)` by
    gvs[LAST_CONS_cond] >>
  first_x_assum drule_all >>
  disch_then (qx_choose_then `new_tail` strip_assume_tac) >>
  `?new_cursor. cfg_norm_cursors C (h::rounds) (new_cursor::new_tail) /\
    (FST new_cursor = FST cursor \/
     ?first a u k after b. FST cursor = (first,a) /\
       is_terminator first.inst_opcode /\ step_inst k C first a = OK u /\
       ~u.vs_halted /\ enters_block (FST (SND h)) u b /\ FST new_cursor = (after,b))` by
    (irule cfg_norm_cursors_extend_block >> metis_tac[]) >>
  `new_tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  qexists_tac `new_cursor::new_tail` >> simp[LAST_CONS_cond] >> metis_tac[]
QED

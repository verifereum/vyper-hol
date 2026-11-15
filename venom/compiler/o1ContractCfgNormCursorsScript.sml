Theory o1ContractCfgNormCursors
Ancestors
  o1ContractCfgNorm o1PassLift cfgNormSupplySim cfgNormDefs
  venomExecSemantics venomExecProofs venomStepProps venomInst venomState
  venomWf venomWfProps unitShapeDefs stateFrame stateEquiv contextCodegenRel
  list rich_list arithmetic pair option ctxLookupAgreeHelpers

(* Static rounds are fixed before execution. A split keeps its source
   terminator and exact deferred result until its JMP exits. *)
Inductive cfg_norm_cursors:
[~final:]
  (!C s fn inst a.
    supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
    active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted ==>
    cfg_norm_cursors C [(s,fn,NONE)] [((inst,a),NONE)])
[~body:]
  (!C s fn pred target split repls s1 next_fn meta rounds
      inst a next v pending cursors bb.
    cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next,v),pending)::cursors) /\
    supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
    active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted /\
    cfg_norm_round_supply s fn = (next_fn,T,s1) /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
    build_split_block_supply s pred target = (split,repls,s1) /\
    insert_split_supply s fn pred target = (next_fn,s1) /\
    MEM bb fn.fn_blocks /\
    MEM (supply_block_image pred target split repls bb) next_fn.fn_blocks /\
    a.vs_current_bb = bb.bb_label /\ v.vs_current_bb = bb.bb_label /\
    a.vs_inst_idx = v.vs_inst_idx /\ a.vs_inst_idx < LENGTH bb.bb_instructions /\
    phi_prefix_length bb.bb_instructions <= a.vs_inst_idx /\
    inst = EL a.vs_inst_idx bb.bb_instructions /\
    next = EL v.vs_inst_idx
      (supply_block_image pred target split repls bb).bb_instructions /\
    supply_state_agree fn a v ==>
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((inst,a),NONE)::((next,v),pending)::cursors))
[~split:]
  (!C s fn pred target split repls s1 next_fn meta rounds
      inst a next v pending cursors u k.
    cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next,v),pending)::cursors) /\
    supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
    active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted /\
    cfg_norm_round_supply s fn = (next_fn,T,s1) /\
    MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
    build_split_block_supply s pred target = (split,repls,s1) /\
    insert_split_supply s fn pred target = (next_fn,s1) /\
    a.vs_current_bb = pred.bb_label /\ is_terminator inst.inst_opcode /\
    step_inst k C inst a = OK u /\ ~u.vs_halted /\ supply_entry_defined fn u /\
    u.vs_current_bb = target.bb_label /\ u.vs_prev_bb = SOME pred.bb_label /\
    v.vs_current_bb = split.bb_label /\ v.vs_inst_idx < LENGTH split.bb_instructions /\
    next = EL v.vs_inst_idx split.bb_instructions /\ supply_state_agree fn a v /\
    (!n ctx. ?m. exec_block n ctx split v = OK m /\
      supply_ready fn pred target split repls u m) ==>
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((inst,a),SOME(u,k))::((next,v),pending)::cursors))
End

Theorem cfg_norm_cursors_lengths:
  !C rounds cursors. cfg_norm_cursors C rounds cursors ==>
    rounds <> [] /\ cursors <> [] /\ LENGTH rounds = LENGTH cursors
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> simp[]
QED

Theorem cfg_norm_cursors_head:
  cfg_norm_cursors C ((s,fn,meta)::rounds) (((inst,a),pending)::cursors) ==>
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted
Proof
  simp[Once cfg_norm_cursors_cases] >> metis_tac[]
QED

Theorem cfg_norm_cursors_last:
  !C rounds cursors. cfg_norm_cursors C rounds cursors ==>
  ?s fn inst a. LAST rounds = (s,fn,NONE) /\ LAST cursors = ((inst,a),NONE) /\
    supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
    active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> simp[] >> metis_tac[]
QED

Theorem cfg_norm_cursors_entry_final:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  fn_entry_state fn cs /\ enters_block fn cs v /\ active_inst fn inst v ==>
  cfg_norm_cursors C [(s,fn,NONE)] [((inst,v),NONE)]
Proof
  strip_tac >>
  `wf_function fn` by gvs[supply_norm_inv_def] >>
  `supply_entry_defined fn cs` by
    (irule supply_entry_defined_entry >> gvs[fn_entry_state_def]) >>
  `supply_prefix_defined fn v` by metis_tac[supply_prefix_enters_block] >>
  `~v.vs_halted` by
    (gvs[enters_block_def, fn_entry_state_def] >>
     metis_tac[eval_phis_preserves_halted]) >>
  irule cfg_norm_cursors_final >> simp[]
QED

Theorem cfg_norm_cursors_ready_body:
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next,z),pending)::cursors) /\
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_round_supply s fn = (next_fn,T,s1) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s1) /\
  insert_split_supply s fn pred target = (next_fn,s1) /\
  supply_ready fn pred target split repls u v /\ enters_block next_fn v z ==>
  ?inst a. enters_block fn u a /\
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((inst,a),NONE)::((next,z),pending)::cursors)
Proof
  strip_tac >> drule cfg_norm_cursors_head >> strip_tac >>
  `wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    gvs[supply_norm_inv_def] >>
  drule_all supply_ready_body_entry >> strip_tac >>
  `~a.vs_halted` by metis_tac[supply_state_agree_halted] >>
  `MEM (supply_block_image pred target split repls bb) next_fn.fn_blocks` by
    metis_tac[insert_split_supply_image_mem] >>
  `a.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `active_inst fn _ a` mp_tac >> simp[active_inst_def] >>
     disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
     `active_bb = bb` by metis_tac[same_label_same_block] >> gvs[]) >>
  qexistsl [`EL a.vs_inst_idx bb.bb_instructions`, `a`] >> simp[] >>
  irule cfg_norm_cursors_body >> gvs[] >> qexists_tac `bb` >> simp[]
QED

Theorem cfg_norm_cursors_entry_body:
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds) (((next,v),pending)::cursors) /\
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_round_supply s fn = (next_fn,T,s1) /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\ 1 < num_succs pred /\
  build_split_block_supply s pred target = (split,repls,s1) /\
  insert_split_supply s fn pred target = (next_fn,s1) /\
  fn_entry_state fn cs /\ enters_block next_fn cs v ==>
  ?inst a. enters_block fn cs a /\
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((inst,a),NONE)::((next,v),pending)::cursors)
Proof
  strip_tac >> irule cfg_norm_cursors_ready_body >> simp[] >>
  metis_tac[supply_ready_entry]
QED

Theorem cfg_norm_iter_supply_cursors:
  !n s fn fn' s'.
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  ?rounds meta. rounds <> [] /\ HD rounds = (s,fn,meta) /\
    LAST rounds = (s',fn',NONE) /\ LENGTH rounds <= SUC n /\
    !C cs v inst. fn_entry_state fn cs /\ enters_block fn' cs v /\
      active_inst fn' inst v ==>
      ?cursors first a. cfg_norm_cursors C rounds cursors /\
        LAST cursors = ((inst,v),NONE) /\ HD cursors = ((first,a),NONE) /\
        enters_block fn cs a
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def] >>
      qexistsl [`[(s,fn,NONE)]`, `NONE`] >> simp[] >> rpt strip_tac >>
      qexistsl [`[((inst,v),NONE)]`, `inst`, `v`] >>
      simp[] >> irule cfg_norm_cursors_entry_final >> simp[] >> metis_tac[]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (mid,changed,s1)` >>
  `supply_norm_inv s1 mid /\ EVERY label_positions_ok (fn_insts mid) /\
   fn_entry_label mid = fn_entry_label fn` by metis_tac[supply_round_semantics] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- (first_x_assum drule_all >>
      disch_then (qx_choose_then `tail` (qx_choose_then `md` strip_assume_tac)) >>
      `tail = (s1,mid,md)::TL tail` by (Cases_on `tail` >> gvs[]) >>
      drule cfg_norm_round_supply_cases >> simp[] >> strip_tac >>
      Cases_on `build_split_block_supply s pred target` >> PairCases_on `r` >>
      rename1 `build_split_block_supply s pred target = (split,repls,rest)` >>
      `rest = s1` by gvs[insert_split_supply_def] >> gvs[] >>
      qexistsl [`(s,fn,SOME(pred,target,split,repls))::tail`,
                `SOME(pred,target,split,repls)`] >>
      simp[LAST_CONS_cond] >> rpt gen_tac >> strip_tac >>
      `fn_entry_state mid cs` by gvs[fn_entry_state_def] >>
      qpat_x_assum `!C cs v inst. _`
        (qspecl_then [`C`, `cs`, `v`, `inst`] mp_tac) >> simp[] >>
      disch_then (qx_choose_then `curs` (qx_choose_then `first`
        (qx_choose_then `a` strip_assume_tac))) >>
      `curs <> []` by metis_tac[cfg_norm_cursors_lengths] >>
      `curs = ((first,a),NONE)::TL curs` by (Cases_on `curs` >> gvs[]) >>
      `?head b. enters_block fn cs b /\
         cfg_norm_cursors C
           ((s,fn,SOME(pred,target,split,repls))::tail)
           (((head,b),NONE)::curs)` by
        (qpat_assum `tail = _` (fn th => ONCE_REWRITE_TAC[th]) >>
         qpat_assum `curs = _` (fn th => ONCE_REWRITE_TAC[th]) >>
         irule cfg_norm_cursors_entry_body >> simp[] >> metis_tac[]) >>
      qexistsl [`((head,b),NONE)::curs`, `head`, `b`] >> simp[LAST_CONS_cond]) >>
  drule cfg_norm_round_supply_cases >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [`[(s,fn,NONE)]`, `NONE`] >> simp[] >> rpt strip_tac >>
  qexistsl [`[((inst,v),NONE)]`, `inst`, `v`] >> simp[] >>
  irule cfg_norm_cursors_entry_final >> simp[] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_cursors:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  ?rounds meta. rounds <> [] /\ HD rounds = (s,fn,meta) /\
    LAST rounds = (s',fn',NONE) /\ LENGTH rounds <= SUC (2 * LENGTH fn.fn_blocks) /\
    !C cs v inst. fn_entry_state fn cs /\ enters_block fn' cs v /\
      active_inst fn' inst v ==>
      ?cursors first a. cfg_norm_cursors C rounds cursors /\
        LAST cursors = ((inst,v),NONE) /\ HD cursors = ((first,a),NONE) /\
        enters_block fn cs a
Proof
  simp[cfg_norm_function_supply_def] >>
  MATCH_ACCEPT_TAC cfg_norm_iter_supply_cursors
QED

Theorem cfg_norm_cursors_replace_tail:
  cfg_norm_cursors C (round::rounds) (cursor::cursors) /\
  cfg_norm_cursors C rounds cursors' /\
  FST (HD cursors') = FST (HD cursors) ==>
  cfg_norm_cursors C (round::rounds) (cursor::cursors')
Proof
  strip_tac >>
  `cursors' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors'` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  qpat_x_assum `cfg_norm_cursors C (_::_) (_::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
  metis_tac[cfg_norm_cursors_rules, cfg_norm_cursors_lengths]
QED

Theorem cfg_norm_cursors_next_final[local]:
  supply_norm_inv s fn /\ EVERY label_positions_ok (fn_insts fn) /\
  active_inst fn inst a /\ supply_prefix_defined fn a /\ ~a.vs_halted /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel D inst a = OK w /\
  active_inst fn next (w with vs_inst_idx := SUC a.vs_inst_idx) ==>
  cfg_norm_cursors C [(s,fn,NONE)]
    [((next,w with vs_inst_idx := SUC a.vs_inst_idx),NONE)]
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
  `supply_prefix_defined fn (w with vs_inst_idx := SUC a.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst a` mp_tac >> simp[active_inst_def] >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >>
     irule supply_prefix_defined_step >> metis_tac[]) >>
  `~w.vs_halted` by metis_tac[step_inst_ok_halted] >>
  irule cfg_norm_cursors_final >> simp[]
QED

Theorem cfg_norm_cursors_body_next[local]:
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),NONE)::((next,v),pending)::cursors) /\
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds)
    (((next',w with vs_inst_idx := SUC v.vs_inst_idx),pending')::cursors') /\
  ~is_terminator next.inst_opcode /\ next.inst_opcode <> INVOKE /\
  step_inst fuel D next v = OK w ==>
  ?u first. step_inst fuel C inst a = OK u /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    cfg_norm_cursors C
      ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
      (((first,u with vs_inst_idx := SUC a.vs_inst_idx),NONE)::
        ((next',w with vs_inst_idx := SUC v.vs_inst_idx),pending')::cursors')
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_::_) (((inst,a),NONE)::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
  `active_inst next_fn next' (w with vs_inst_idx := SUC v.vs_inst_idx) /\
   supply_norm_inv s1 next_fn /\ ~(w with vs_inst_idx := SUC v.vs_inst_idx).vs_halted` by
    metis_tac[cfg_norm_cursors_head] >>
  `wf_function next_fn /\ ~w.vs_halted` by gvs[supply_norm_inv_def] >>
  `~is_terminator (EL v.vs_inst_idx bb.bb_instructions).inst_opcode /\
   (EL v.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE` by
    metis_tac[supply_block_image_index] >>
  mp_tac (Q.INST [`fn'` |-> `next_fn`,
    `inst` |-> `EL v.vs_inst_idx bb.bb_instructions`,
    `inst'` |-> `EL v.vs_inst_idx
      (supply_block_image pred target split repls bb).bb_instructions`]
    supply_body_next_prefix) >> simp[] >> strip_tac >>
  `~u.vs_halted` by metis_tac[step_inst_ok_halted] >>
  qexistsl [`u`, `EL (SUC a.vs_inst_idx) bb.bb_instructions`] >> simp[] >>
  irule cfg_norm_cursors_body >> gvs[] >> qexists_tac `bb` >> simp[] >> decide_tac
QED

Theorem cfg_norm_cursors_split_next[local]:
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),SOME(u,k))::((next,v),pending)::cursors) /\
  cfg_norm_cursors C ((s1,next_fn,meta)::rounds)
    (((next',w with vs_inst_idx := SUC v.vs_inst_idx),pending')::cursors') /\
  ~is_terminator next.inst_opcode /\ step_inst fuel D next v = OK w ==>
  cfg_norm_cursors C
    ((s,fn,SOME(pred,target,split,repls))::(s1,next_fn,meta)::rounds)
    (((inst,a),SOME(u,k))::
      ((next',w with vs_inst_idx := SUC v.vs_inst_idx),pending')::cursors')
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_::_) (((inst,a),SOME(u,k))::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[] >>
  `ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by gvs[supply_norm_inv_def] >>
  `active_inst next_fn next' (w with vs_inst_idx := SUC v.vs_inst_idx) /\
   supply_norm_inv s1 next_fn` by metis_tac[cfg_norm_cursors_head] >>
  `wf_function next_fn /\ ~v.vs_halted` by
    metis_tac[supply_norm_inv_projections, supply_state_agree_halted] >>
  `!n. ?m. exec_block n D split v = OK m /\
     supply_ready fn pred target split repls u m` by metis_tac[] >>
  mp_tac (Q.INST [`s'` |-> `s1`,
    `inst'` |-> `EL v.vs_inst_idx split.bb_instructions`] supply_split_next_prefix) >>
  simp[] >> strip_tac >>
  `!n ctx. ?m. exec_block n ctx split (w with vs_inst_idx := SUC v.vs_inst_idx) = OK m /\
     supply_ready fn pred target split repls u m` by
    (rpt gen_tac >>
     qpat_assum `!n ctx. _` (qspecl_then [`n`, `ctx`] strip_assume_tac) >>
     `step_inst n ctx (EL v.vs_inst_idx split.bb_instructions) v = OK w` by
       metis_tac[supply_assign_fuel_independent] >>
     mp_tac (Q.INST [`bb` |-> `split`, `fuel` |-> `n`,
       `inst` |-> `EL v.vs_inst_idx split.bb_instructions`]
       supply_exec_block_step_residual) >> simp[] >> strip_tac >> metis_tac[]) >>
  `~MEM split.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    metis_tac[supply_split_label_not_old, fn_labels_def] >>
  `lookup_block split.bb_label next_fn.fn_blocks = SOME split` by
    metis_tac[insert_split_supply_split_lookup] >>
  `MEM split next_fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `SUC v.vs_inst_idx < LENGTH split.bb_instructions /\
   next' = EL (SUC v.vs_inst_idx) split.bb_instructions` by
    (qpat_x_assum `active_inst next_fn next' _` mp_tac >> simp[active_inst_def] >>
     disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
     `active_bb = split` by metis_tac[same_label_same_block] >> gvs[]) >>
  irule cfg_norm_cursors_split >> gvs[]
QED

Theorem cfg_norm_cursors_extend_next[local]:
  cfg_norm_cursors C (round::rounds) (cursor::cursors) /\
  cfg_norm_cursors C rounds cursors' /\
  (FST (HD cursors') = FST (HD cursors) \/
   ?inst a u next. FST (HD cursors) = (inst,a) /\
     ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
     step_inst fuel C inst a = OK u /\
     FST (HD cursors') = (next,u with vs_inst_idx := SUC a.vs_inst_idx)) ==>
  ?cursor'. cfg_norm_cursors C (round::rounds) (cursor'::cursors') /\
    (FST cursor' = FST cursor \/
     ?inst a u next. FST cursor = (inst,a) /\
       ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
       step_inst fuel C inst a = OK u /\
       FST cursor' = (next,u with vs_inst_idx := SUC a.vs_inst_idx))
Proof
  strip_tac
  >- (qexists_tac `cursor` >> simp[] >>
      irule cfg_norm_cursors_replace_tail >> metis_tac[]) >>
  `cursors' <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  Cases_on `cursors'` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  qpat_assum `cfg_norm_cursors C (_::_) (_::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[]
  >- metis_tac[cfg_norm_cursors_lengths]
  >- (drule_all cfg_norm_cursors_body_next >> strip_tac >>
      metis_tac[pairTheory.FST]) >>
  drule_all cfg_norm_cursors_split_next >> strip_tac >>
  metis_tac[pairTheory.FST]
QED

Theorem cfg_norm_cursors_tail:
  cfg_norm_cursors C (round::rounds) (cursor::cursors) /\ rounds <> [] ==>
  cfg_norm_cursors C rounds cursors
Proof
  simp[Once cfg_norm_cursors_cases] >> rpt strip_tac >> gvs[]
QED

Theorem cfg_norm_cursors_next:
  !rounds C cursors t fn inst v fuel D w next.
  cfg_norm_cursors C rounds cursors /\ LAST rounds = (t,fn,NONE) /\
  LAST cursors = ((inst,v),NONE) /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel D inst v = OK w /\
  active_inst fn next (w with vs_inst_idx := SUC v.vs_inst_idx) ==>
  ?cursors'. cfg_norm_cursors C rounds cursors' /\
    LAST cursors' = ((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE) /\
    (FST (HD cursors') = FST (HD cursors) \/
     ?first a u after. FST (HD cursors) = (first,a) /\
       ~is_terminator first.inst_opcode /\ first.inst_opcode <> INVOKE /\
       step_inst fuel C first a = OK u /\
       FST (HD cursors') = (after,u with vs_inst_idx := SUC a.vs_inst_idx))
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
      qexists_tac `[((next,w with vs_inst_idx := SUC v.vs_inst_idx),NONE)]` >> simp[] >>
      conj_tac >- (irule cfg_norm_cursors_next_final >> simp[] >> metis_tac[]) >>
      disj2_tac >> qexists_tac `w` >> simp[] >>
      metis_tac[step_inst_non_invoke]) >>
  `cfg_norm_cursors C rounds tail` by metis_tac[cfg_norm_cursors_tail] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `LAST rounds = (t,fn,NONE) /\ LAST tail = ((inst,v),NONE)` by
    gvs[LAST_CONS_cond] >>
  first_x_assum drule_all >>
  disch_then (qx_choose_then `new_tail` strip_assume_tac) >>
  `?new_cursor. cfg_norm_cursors C (h::rounds) (new_cursor::new_tail) /\
    (FST new_cursor = FST cursor \/
     ?first a u after. FST cursor = (first,a) /\
       ~is_terminator first.inst_opcode /\ first.inst_opcode <> INVOKE /\
       step_inst fuel C first a = OK u /\
       FST new_cursor = (after,u with vs_inst_idx := SUC a.vs_inst_idx))` by
    (irule cfg_norm_cursors_extend_next >> metis_tac[]) >>
  `new_tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  qexists_tac `new_cursor::new_tail` >> simp[LAST_CONS_cond]
QED

Theory o1ContractCfgNormCursorCalls
Ancestors
  o1ContractCfgNormCursors o1ContractCfgNorm cfgNormSupplySim cfgNormDefs
  o1PassLift simplifyCfgSimTools venomExecSemantics venomExecProofs
  venomInst venomState venomWf unitShapeDefs contextCodegenRel stateFrame
  ctxLookupAgreeHelpers list rich_list pair option

Theorem cfg_norm_cursors_call_head[local]:
  cfg_norm_cursors C (round::rounds)
    (((inst,a),pending)::((callinst,v),other)::cursors) /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME(nm,ops) /\
  eval_operands ops v = SOME args /\ setup_callee callee args v = SOME cs ==>
  inst = callinst /\ pending = NONE /\ eval_operands ops a = SOME args /\
  setup_callee callee args a = SOME cs
Proof
  strip_tac >>
  qpat_x_assum `cfg_norm_cursors C (_::_) (_::_)` mp_tac >>
  simp[Once cfg_norm_cursors_cases] >> strip_tac >> gvs[]
  >- (`fn_inst_wf fn` by gvs[supply_norm_inv_def] >>
      `inst_wf (EL v.vs_inst_idx bb.bb_instructions)` by
        metis_tac[active_inst_wf] >>
      `label_positions_ok (EL v.vs_inst_idx bb.bb_instructions)` by
        (gvs[fn_insts_def, EVERY_MEM] >>
         metis_tac[EL_MEM, MEM_fn_insts_blocks]) >>
      mp_tac (Q.INST [`inst` |-> `EL v.vs_inst_idx bb.bb_instructions`,
        `inst'` |-> `EL v.vs_inst_idx
          (supply_block_image pred target split repls bb).bb_instructions`,
        `i` |-> `v.vs_inst_idx`, `callee'` |-> `callee`] supply_body_call_prefix) >>
      simp[] >> metis_tac[]) >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn` by
    gvs[supply_norm_inv_def] >>
  drule_all supply_split_index_shape >> simp[]
QED

Theorem cfg_norm_cursors_execution_frame:
  !C rounds cursors. cfg_norm_cursors C rounds cursors ==>
  !inst v pending. LAST cursors = ((inst,v),pending) ==>
    EVERY (\((i,a),other). execution_frame a = execution_frame v) cursors
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> rpt strip_tac >>
  gvs[Excl "execution_frame_def"] >>
  gvs[supply_state_agree_def, Excl "execution_frame_def"] >> metis_tac[]
QED

Theorem cfg_norm_cursors_invoke:
  !rounds C cursors callinst v nm ops args callee cs.
    cfg_norm_cursors C rounds cursors /\
    LAST cursors = ((callinst,v),NONE) /\ callinst.inst_opcode = INVOKE /\
    decode_invoke callinst = SOME(nm,ops) /\ eval_operands ops v = SOME args /\
    setup_callee callee args v = SOME cs ==>
    EVERY (\((i,a),pending). i = callinst /\ pending = NONE /\
      eval_operands ops a = SOME args /\ setup_callee callee args a = SOME cs)
      cursors
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
        (strip_assume_tac o ONCE_REWRITE_RULE[cfg_norm_cursors_cases]) >> gvs[]) >>
  `cfg_norm_cursors C rounds tail` by metis_tac[cfg_norm_cursors_tail] >>
  `tail <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  `LAST tail = ((callinst,v),NONE)` by gvs[LAST_CONS_cond] >>
  Cases_on `tail` >> gvs[] >> rename1 `cfg_norm_cursors C rounds (middle::rest)` >>
  PairCases_on `middle` >> PairCases_on `cursor` >>
  first_x_assum drule_all >> simp[] >> strip_tac >> gvs[] >>
  drule_all cfg_norm_cursors_call_head >> simp[]
QED

Theorem cfg_norm_cursors_call:
  cfg_norm_cursors C rounds cursors /\
  HD cursors = ((first,a),pending) /\ LAST cursors = ((callinst,v),NONE) /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME(nm,ops) /\
  eval_operands ops v = SOME args /\ setup_callee callee9 args v = SOME cs /\
  fn_entry_label callee8 = fn_entry_label callee9 ==>
  first = callinst /\ pending = NONE /\ eval_operands ops a = SOME args /\
  setup_callee callee8 args a = SOME cs /\
  fn_entry_state callee8 cs /\ fn_entry_state callee9 cs
Proof
  strip_tac >> `cursors <> []` by metis_tac[cfg_norm_cursors_lengths] >>
  drule_all cfg_norm_cursors_invoke >> strip_tac >>
  Cases_on `cursors` >> gvs[] >>
  metis_tac[setup_callee_entry_label, setup_callee_fn_entry_state]
QED

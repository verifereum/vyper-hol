(*
 * Leaf B of the label-discipline proof: the control and terminal steps of
 * a block, run on the symbolic machine without SymBad.  Each statement is
 * codegen's own deep-tier lemma with the symbolic premises and conclusions
 * added, over the same n steps: a step that continues keeps the symbolic
 * frame invariant, a RET leaves the returned values as words above the
 * caller's symbolic stack, and a halt or abort ends the symbolic run.
 *
 * A jump's target is a code label of the program (MEM (AsmLabel l) prog):
 * the symbolic machine jumps only to code labels.
 *
 * TOP-LEVEL:
 *   sym_jmp_frame_sim_deep            - JMP
 *   sym_jnz_frame_sim_deep            - JNZ
 *   sym_ret_frame_sim_deep            - RET
 *   sym_halt_frame_sim_deep           - an instruction that halts
 *   sym_abort_frame_sim_deep          - an instruction that aborts
 *   sym_gas_frame_sim_deep            - GAS
 *   sym_revert_forward_frame_sim_deep - a forwarded revert
 *)
Theory symFrameControl
Ancestors
  asmSplice codegenSymRel fnFrameDeepJmp fnFrameDeepJnz fnFrameDeepRet fnFrameDeepHalt
  fnFrameDeepAbort fnFrameDeepGas fnFrameStepsRevertForwardDeep asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs symPlannerSim symShuffleSim asmSymPc codegenEncodingWf
  spillPlanSim reorderStages inputMaterialised reduceDepthSim mixedPrefixSim
  symEmitSim symInstPieces symControlPrefixOwn symFrameControlFacts symControlScratchOwn symControlReorderOwn symControlReplayOwn symControlJumpOwn symControlRetOwn symControlGasOwn symControlTerminalOwn symControlHaltOwn symControlAbortRegularOwn symControlAbortStaticOwn symControlAbortConditionalOwn symControlTerminalPrepareOwn symControlTerminalSafetyOwn symControlForwardPrepareOwn symControlForwardCopyOwn symControlForwardCopyExecutionOwn symControlForwardRunOwn symControlForwardContinuationOwn symControlForwardSourceFacts
  symControlWordStackOwn symControlTerminalWordStackOwn symFrameControlOwn fnPlanPlaceRevertPostamble

(* Pointwise kind equivalence transports a typed symbolic stack. *)

Theorem list_rel_op_kind_transport:
  !xs vals ys fn ret.
    LIST_REL (op_kind_ok fn ret) xs vals /\
    LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                          op_kind_ok fn ret y sv) xs ys ==>
    LIST_REL (op_kind_ok fn ret) ys vals
Proof
  ACCEPT_TAC symFrameControlFactsTheory.list_rel_op_kind_transport
QED

Theorem stack_poke_op_kind_equiv:
  d < LENGTH xs /\
  (!sv. op_kind_ok fn ret (stack_peek d xs) sv <=>
        op_kind_ok fn ret op sv) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) xs (stack_poke d op xs)
Proof
  ACCEPT_TAC symFrameControlFactsTheory.stack_poke_op_kind_equiv
QED

Theorem stack_exchange_op_kind_equiv:
  d < LENGTH xs /\ f < LENGTH xs /\
  op = stack_peek d xs /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f xs) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv)
    xs (stack_poke f op (stack_poke d (stack_peek f xs) xs))
Proof
  ACCEPT_TAC symFrameControlFactsTheory.stack_exchange_op_kind_equiv
QED

Theorem sym_kinds_ok_stack_transport:
  !cp fn ret srest ps ss xs.
  sym_kinds_ok cp fn ret srest ps ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=>
                       op_kind_ok fn ret y sv) ps.ps_stack xs ==>
  sym_kinds_ok cp fn ret srest (ps with ps_stack := xs) ss
Proof
  ACCEPT_TAC symFrameControlFactsTheory.sym_kinds_ok_stack_transport
QED

Theorem sym_kinds_ok_reorder_relabel:
  !cp fn ret srest ps ss d f op dfg.
  sym_kinds_ok cp fn ret srest ps ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) ss
Proof
  ACCEPT_TAC symFrameControlFactsTheory.sym_kinds_ok_reorder_relabel
QED

(* Restore interpretation agrees on the fields observed by symbolic kinds. *)

Theorem restore_spilled_plan_ss_align:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops, ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    !lo. (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
         (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symFrameControlFactsTheory.restore_spilled_plan_ss_align
QED

(* Projection and exact-stack extraction use sym_kinds_ok_def directly:
 * theorem search checks that simp[sym_kinds_ok_def] closes both interfaces.
 * Releasing spills additionally needs lookup inclusion and stack preservation.
 *)
Theorem sym_frame_inv_release_dead_spills:
  !p env ctx cp fn ret srest labs0 ps cs ss nl.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv p env ctx cp fn ret srest labs0
    (release_dead_spills nl ps) cs ss
Proof
  rpt gen_tac >> rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  metis_tac[SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`]
      (SPEC_ALL sym_frame_inv_release_dead_spills_mode))]
QED

(* The symbolic prefix and the concrete endpoint share an explicit count. *)

Theorem sym_selected_prefix_frame_sim_marked:
  !opc operands nl ps iops prepared dfg selected rops arranged spillbase
    fn r cp p env ret srest labs0 ctx cs ss initial_fmp.
  opc <> INVOKE /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss =
      SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops))
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`,
             `dfg` |-> `dfg_build_function fn`]
      (SPEC_ALL sym_selected_prefix_frame_sim_marked_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

(* Region-local shuffles expose the same frame boundary as input preparation. *)

Theorem sym_prefix_ops_frame_sim:
  !ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs r.
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp (SND (compute_label_offsets p)) ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    (r.sr_spill_base <= b /\ b < r.sr_spill_end) /\
    context_spill_byte cp b) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (apply_prefix_ops initial_fmp (SND (compute_label_offsets p)) ops ps)
      cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_prefix_ops_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_spill_free_prefix_frame_sim:
  !ops initial_fmp p env cp fn ret srest ps ss ctx labs0 cs.
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp (SND (compute_label_offsets p)) ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops) /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (apply_prefix_ops initial_fmp (SND (compute_label_offsets p)) ops ps)
      cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_spill_free_prefix_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem do_restore_symbolic_prefix_facts:
  !op ps ops ps' initial_fmp lo.
  do_restore op ps = (ops,ps') /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  ACCEPT_TAC symControlReorderOwnTheory.do_restore_symbolic_prefix_facts
QED

(* A physical restore exposes kinds at the actual planner result. *)
Theorem sym_do_restore_frame_sim:
  !cp op ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r.
  do_restore op ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_do_restore_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem do_swap_shallow_symbolic_prefix_facts:
  !d ps ops ps' initial_fmp lo.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\
  EVERY is_prefix_op ops /\
  EVERY (\op. !l n. op <> SOPushOfst l n) ops /\
  (!off. ~MEM (SOSpill off) ops)
Proof
  ACCEPT_TAC symControlReorderOwnTheory.do_swap_shallow_symbolic_prefix_facts
QED

Theorem sym_do_swap_shallow_frame_sim:
  !cp d ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r.
  do_swap d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_do_swap_shallow_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem do_spill_at_symbolic_prefix_shape:
  !d ps ops ps' lo.
  do_spill_at d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  EVERY is_prefix_op ops /\ EVERY (\op. !l n. op <> SOPushOfst l n) ops
Proof
  ACCEPT_TAC symControlReorderOwnTheory.do_spill_at_symbolic_prefix_shape
QED

Theorem sym_do_spill_at_frame_sim:
  !cp d ps ops ps' initial_fmp p env fn ret srest ss ctx labs0 cs r base.
  do_spill_at d ps = (ops,ps') /\ d <= 16 /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded base ps /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_do_spill_at_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem selected_spill_marked_budget:
  !base pending ps dist cand hops ps1.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  16 < dist /\ dist < LENGTH ps.ps_stack /\
  select_spill_candidate ps.ps_stack pending dist (LENGTH pending) = SOME cand /\
  do_spill_at cand ps = (hops,ps1) ==>
  cand <= 16 /\ cand < LENGTH ps.ps_stack /\
  residual_budget_wf_marked base pending ps1 /\
  LENGTH pending <= LENGTH ps1.ps_stack
Proof
  ACCEPT_TAC symControlReorderOwnTheory.selected_spill_marked_budget
QED

Theorem sym_reduce_depth_plan_frame_sim:
  !fuel pending op f ps ops ps' base initial_fmp p env cp fn ret srest
    ss ctx labs0 cs r.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reduce_depth_plan fuel pending op f (LENGTH pending) ps = (ops,ps') /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256)) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reduce_depth_plan_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem mem_label_at_from_bytes:
  (!i. i < 32 ==> FLOOKUP labs (off+i) = SOME (l,d,i)) ==>
  mem_label_at labs off = SOME (l,d)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.mem_label_at_from_bytes
QED

Theorem sym_mstore_word_cell:
  ss.sym_stack = Val off :: Val w :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Val w) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_mstore_word_cell
QED

Theorem sym_mstore_label_cell:
  ss.sym_stack = Val off :: Lab l d :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) (Lab l d) /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_mstore_label_cell
QED

Theorem sym_mload_label_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Lab l d :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_mload_label_cell
QED

Theorem scratch_store_preserves_disjoint_cell:
  mem_sval_at labs cell sv /\
  (!b. in_mem_range cell 32 b ==> ~in_mem_range off 32 b) /\
  (!b. ~in_mem_range off 32 b ==> FLOOKUP labs' b = FLOOKUP labs b) ==>
  mem_sval_at labs' cell sv
Proof
  ACCEPT_TAC symControlScratchOwnTheory.scratch_store_preserves_disjoint_cell
QED

Theorem sym_mload_word_cell:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) /\
  asm_mload (ss.sym_base with as_stack := [off]) = AsmOK loaded /\
  loaded.as_stack = [w] ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val w :: tail /\
        ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_mload_word_cell
QED

Theorem sym_scratch_store_step:
  ss.sym_stack = Val off :: sv :: tail ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels (w2n off) sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    (!b. ~in_mem_range (w2n off) 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range (w2n off) 32 b)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_store_step
QED

Theorem sym_scratch_spill_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_spill_steps
QED

Theorem sym_scratch_load_word_step:
  ss.sym_stack = Val off :: tail /\
  mem_sval_at ss.sym_mem_labels (w2n off) (Val w) ==>
  ?ss' v. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val v :: tail /\
          ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_load_word_step
QED

Theorem sym_scratch_load_step:
  ss.sym_stack = Val off :: tail /\ mem_sval_at ss.sym_mem_labels (w2n off) sv ==>
  ?ss' sv'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = sv' :: tail /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_load_step
QED

Theorem sym_scratch_restore_steps:
  off < dimword(:256) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv ==>
  ?ss' sv'. sym_steps p env (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    ss'.sym_stack = sv' :: ss.sym_stack /\
    (case sv of Val w => ?v. sv' = Val v | Lab l d => sv' = sv) /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_restore_steps
QED
Theorem sym_scratch_spill_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SOSpill off]) /\
  ss.sym_stack = sv :: tail ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SOSpill off])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp [SOSpill off])) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    cs'.as_memory = mem_write32 off (HD cs.as_stack) cs.as_memory /\
    cs'.as_stack = TL cs.as_stack /\
    ss'.sym_stack = tail /\ mem_sval_at ss'.sym_mem_labels off sv /\
    cs'.as_pc = cs.as_pc + 2 /\
    (!b. ~in_mem_range off 32 b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ in_mem_range off 32 b)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_scratch_spill_sim_mode_conditional))) >> simp[]
QED

Theorem sym_scratch_restore_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  off < dimword(:256) /\
  asm_block_at p cs.as_pc (execute_plan fmp [SORestore off]) /\
  mem_sval_at ss.sym_mem_labels off sv /\
  (case sv of Val w =>
     word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP off (asm_expand_memory (off + 32) cs.as_memory))) = w
   | Lab l d => T) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp [SORestore off])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp [SORestore off])) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\ ss'.sym_stack = sv :: ss.sym_stack /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ cs'.as_pc = cs.as_pc + 2 /\
    cs'.as_memory = asm_expand_memory (off + 32) cs.as_memory
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_scratch_restore_sim_mode_conditional))) >> simp[]
QED

Theorem sym_scratch_repeated_value_probe:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp [SOSpill 0; SOSpill 32]) /\
  ss.sym_stack = sv :: sv :: tail ==>
  ?ss'. sym_steps p env 4 ss = SymOK ss' /\ ss'.sym_stack = tail /\
    mem_sval_at ss'.sym_mem_labels 0 sv /\ mem_sval_at ss'.sym_mem_labels 32 sv /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 4
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_repeated_value_probe
QED

Theorem scratch_disjoint_bulk_cell:
  EVERY (\off. h + 32 <= off \/ off + 32 <= h) offsets /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP labs' b = FLOOKUP labs b) /\
  mem_sval_at labs h sv ==>
  mem_sval_at labs' h sv
Proof
  ACCEPT_TAC symControlScratchOwnTheory.scratch_disjoint_bulk_cell
QED

Theorem sym_scratch_spill_bulk_steps:
  !offsets ss.
    LENGTH offsets <= LENGTH ss.sym_stack /\
    EVERY (\off. off < dimword(:256)) offsets /\
    (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
      EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
    asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill offsets)) ==>
    ?ss'. sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
      ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 * LENGTH offsets /\
      (!k. k < LENGTH offsets ==>
        mem_sval_at ss'.sym_mem_labels (EL k offsets) (EL k ss.sym_stack)) /\
      (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
      (!b. b IN FDOM ss'.sym_mem_labels ==>
        b IN FDOM ss.sym_mem_labels \/
        EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.sym_scratch_spill_bulk_steps
QED

Theorem sym_scratch_restore_bulk_sim:
  !offsets vals cs ss.
    asm_static_wf p /\ asm_sym_rel p env cs ss /\
    EVERY (\off. off < dimword(:256)) offsets /\
    LIST_REL (\off sv. mem_sval_at ss.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs.as_memory)) = w | Lab l d => T) offsets vals /\
    asm_block_at p cs.as_pc (execute_plan fmp (MAP SORestore offsets)) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (2 * LENGTH offsets) cs = AsmOK cs' /\
      sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
      asm_sym_rel p env cs' ss' /\
      ss'.sym_stack = REVERSE vals ++ ss.sym_stack /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\
      cs'.as_pc = cs.as_pc + 2 * LENGTH offsets
Proof
  rpt gen_tac >> strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_scratch_restore_bulk_sim_mode_conditional))) >> simp[]
QED

Theorem sym_scratch_spill_bulk_sim:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (MAP SOSpill offsets)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (2 * LENGTH offsets) cs = AsmOK cs' /\
    sym_steps p env (2 * LENGTH offsets) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    ss'.sym_stack = DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets /\
    LIST_REL (\off sv. mem_sval_at ss'.sym_mem_labels off sv /\
      case sv of Val w => word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP off cs'.as_memory)) = w | Lab l d => T)
      offsets (TAKE (LENGTH offsets) ss.sym_stack) /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_scratch_spill_bulk_sim_mode_conditional))) >> simp[]
QED

Theorem sym_raw_spill_restore_schedule_steps:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  LENGTH offsets <= LENGTH ss.sym_stack /\
  EVERY (\off. off < dimword(:256)) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  EVERY (\i. i < LENGTH offsets) desired /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp
    (MAP SOSpill offsets ++ MAP SORestore
      (MAP (\i. EL i offsets) (REVERSE desired)))) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) cs = AsmOK cs' /\
    sym_steps p env
      (LENGTH (execute_plan initial_fmp (MAP SOSpill offsets ++
        MAP SORestore (MAP (\i. EL i offsets) (REVERSE desired))))) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    ss'.sym_stack = MAP (\i. EL i (TAKE (LENGTH offsets) ss.sym_stack)) desired ++
      DROP (LENGTH offsets) ss.sym_stack /\
    cs'.as_pc = cs.as_pc + 2 * LENGTH offsets + 2 * LENGTH desired /\
    (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==>
      b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets)
Proof
  strip_tac >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_raw_spill_restore_schedule_steps_mode_conditional))) >> simp[]
QED


Theorem list_rel_reversed_index_schedule:
  LIST_REL R (REVERSE items) vals /\ LENGTH items = d + 1 /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < LENGTH items) ids ==>
  LIST_REL R (REVERSE (MAP (\i. EL i items) ids))
    (MAP (\i. EL i vals) ids)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.list_rel_reversed_index_schedule
QED

Theorem do_swap_deep_symbolic_resources:
  do_swap d ps = (ops,ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  offsets = FST (spill_alloc_n [] ps.ps_alloc (top_n (d + 1) ps.ps_stack)) /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] ==>
  ops = MAP SOSpill offsets ++
    MAP SORestore (MAP (\i. EL i offsets) (REVERSE ids)) /\
  LENGTH offsets = d + 1 /\ ALL_DISTINCT offsets /\
  EVERY (\i. i < LENGTH offsets) ids /\
  EVERY (\off. off < dimword(:256) /\ ps'.ps_alloc.sa_spill_base <= off /\
    off + 32 <= ps'.ps_alloc.sa_next_offset) offsets /\
  (!i j. i < LENGTH offsets /\ j < LENGTH offsets /\ i <> j ==>
    EL i offsets + 32 <= EL j offsets \/ EL j offsets + 32 <= EL i offsets) /\
  (!i op old. i < LENGTH offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= EL i offsets \/ EL i offsets + 32 <= old) /\
  ps'.ps_spilled = ps.ps_spilled /\
  ps'.ps_stack = TAKE (LENGTH ps.ps_stack - (d + 1)) ps.ps_stack ++
    MAP (\i. EL i (top_n (d + 1) ps.ps_stack)) ids
Proof
  ACCEPT_TAC symControlScratchOwnTheory.do_swap_deep_symbolic_resources
QED

Theorem list_rel_deep_swap_schedule:
  LIST_REL R (REVERSE xs) vals /\ d < LENGTH xs /\ 0 < d /\
  ids = [d] ++ GENLIST (\i. i + 1) (d - 1) ++ [0] /\
  EVERY (\i. i < d + 1) ids ==>
  LIST_REL R
    (REVERSE (TAKE (LENGTH xs - (d + 1)) xs ++
      MAP (\i. EL i (top_n (d + 1) xs)) ids))
    (MAP (\i. EL i (TAKE (d + 1) vals)) ids ++ DROP (d + 1) vals)
Proof
  ACCEPT_TAC symControlScratchOwnTheory.list_rel_deep_swap_schedule
QED

Theorem sym_scratch_frame_transfer:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_sym_rel p env cs' ss' /\ ps'.ps_spilled = ps.ps_spilled /\
  ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  EVERY (\off. r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) offsets /\
  (!off op old. MEM off offsets /\ FLOOKUP ps.ps_spilled op = SOME old ==>
    old + 32 <= off \/ off + 32 <= old) /\
  (!b. EVERY (\off. ~in_mem_range off 32 b) offsets ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!b. b IN FDOM ss'.sym_mem_labels ==>
    b IN FDOM ss.sym_mem_labels \/ EXISTS (\off. in_mem_range off 32 b) offsets) ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss'
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  drule_all (SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`]
      (SPEC_ALL sym_scratch_frame_transfer_mode_conditional))) >> simp[]
QED

Theorem sym_do_swap_deep_frame_sim:
  do_swap d ps = (ops, ps') /\ 16 < d /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_do_swap_deep_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

(* Physical swaps expose a single interface at every depth. *)
Theorem sym_do_swap_frame_sim:
  do_swap d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> Cases_on `d <= 16`
  >- (drule_all sym_do_swap_shallow_frame_sim >> simp[]) >>
  `16 < d` by decide_tac >> drule_all sym_do_swap_deep_frame_sim >> simp[]
QED

Theorem sym_do_swap_pair_frame_sim:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (ops1 ++ ops2) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
  ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_do_swap_pair_frame_sim_mode_conditional))) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        drule_all (SRULE [sym_frame_inv_def] sym_do_swap_shallow_frame_sim) >>
        disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
        qexistsl [`ac`, `sy`] >> simp[] >> decide_tac) >>
    metis_tac[asm_sym_steps_lockstep])) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem control_plan_address_bounds:
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops ==>
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  (!off. MEM (SOSpill off) ops ==> off < dimword(:256))
Proof
  ACCEPT_TAC symControlReorderOwnTheory.control_plan_address_bounds
QED

Theorem sym_reorder_restore_frame_sim:
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_restore_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_reorder_prepare_reduce_frame_sim:
  residual_budget_wf_marked spill_base pending ps1 /\
  LENGTH pending <= LENGTH ps1.ps_stack /\
  reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1 =
    (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) reduce_ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps1 mid smid /\
  asm_static_wf p /\
  asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
    (execute_plan initial_fmp reduce_ops) /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
    (LENGTH (execute_plan initial_fmp restore_ops)) cs = AsmOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp restore_ops)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops) ==>
  residual_budget_wf_marked spill_base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  `mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops)` by decide_tac >>
  `asm_block_at p (cs.as_pc + LENGTH (execute_plan initial_fmp restore_ops))
     (execute_plan initial_fmp reduce_ops)` by metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_prepare_reduce_frame_sim_mode_conditional))) >>
  strip_tac >> simp[] >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_reorder_prepare_frame_sim:
  !base.
  residual_budget_wf_marked base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     SOME d => ([],ps)
   | NONE => (case FLOOKUP ps.ps_spilled op of
       SOME off => do_restore op ps | NONE => ([],ps))) = (restore_ops,ps1) /\
  stack_get_unfixed_depth op f (LENGTH pending) ps1.ps_stack = SOME dist /\
  (if dist > 16 then
     reduce_depth_plan (LENGTH ps1.ps_stack) pending op f (LENGTH pending) ps1
   else ([],ps1)) = (reduce_ops,ps2) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (restore_ops ++ reduce_ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= base /\ ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reduce_ops)) ==>
  residual_budget_wf_marked base pending ps2 /\
  LENGTH pending <= LENGTH ps2.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reduce_ops))
Proof
  gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_prepare_frame_sim_mode_conditional))) >>
  strip_tac >> simp[] >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_frame_inv_reorder_relabel:
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  op = stack_peek d ps.ps_stack /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0
    (ps with ps_stack := stack_poke f op
      (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack)) cs ss
Proof
  rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  drule_all (SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`]
      (SPEC_ALL sym_frame_inv_reorder_relabel_mode))) >> simp[]
QED

Theorem sym_reorder_place_frame_sim:
  (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
     NONE => ([],ps)
   | SOME d =>
       if d = f then ([],ps)
       else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
       then ([],ps with ps_stack := stack_poke f op
         (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
       else
         (case do_swap d ps of (ops1,ps1) =>
          case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2))) = (ops,ps') /\
  f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rewrite_tac[sym_frame_inv_def] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_place_frame_sim_mode_conditional))) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  disch_then assume_tac >> strip_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Definition control_reorder_place_def:
  control_reorder_place dfg pending op f ps =
    (case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
       NONE => ([],ps)
     | SOME d => if d = f then ([],ps)
       else if f < LENGTH ps.ps_stack /\ operand_equiv dfg op (stack_peek f ps.ps_stack)
       then ([],ps with ps_stack := stack_poke f op
         (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
       else (case do_swap d ps of (ops1,ps1) =>
         case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)))
End

Theorem control_reorder_place_none:
  stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack = NONE ==>
  control_reorder_place dfg pending op f ps = ([],ps)
Proof
  simp[control_reorder_place_def]
QED

Theorem control_reorder_place_fixed:
  stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack = SOME f ==>
  control_reorder_place dfg pending op f ps = ([],ps)
Proof
  simp[control_reorder_place_def]
QED

Theorem control_reorder_place_frame_sim:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  f < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rewrite_tac[control_reorder_place_def] >>
  MATCH_ACCEPT_TAC sym_reorder_place_frame_sim
QED

Theorem sym_asm_plan_runs_compose:
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops1)) cs = AsmOK mid /\
  sym_steps p env (LENGTH (execute_plan initial_fmp ops1)) ss = SymOK smid /\
  mid.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops1) /\
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp ops2)) mid = AsmOK final /\
  sym_steps p env (LENGTH (execute_plan initial_fmp ops2)) smid = SymOK sfinal /\
  final.as_pc = mid.as_pc + LENGTH (execute_plan initial_fmp ops2) ==>
  asm_steps lo o2pc p (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK final /\
  sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK sfinal /\
  final.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  strip_tac >> drule_all (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] (SPEC_ALL sym_asm_plan_runs_compose_mode))) >> simp[]
QED

Theorem sym_reorder_one_decompose:
  reorder_one dfg pending idx op ps = (ops,ps') ==>
  ?restore_ops ps1.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ((stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps1.ps_stack = NONE /\ ops = restore_ops /\ ps' = ps1) \/
     ?dist reduce_ops ps2 suffix.
       stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
         (LENGTH pending) ps1.ps_stack = SOME dist /\
       (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
         (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
        else ([],ps1)) = (reduce_ops,ps2) /\
       ops = (restore_ops ++ reduce_ops) ++ suffix /\
       ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
       (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
          (LENGTH pending) ps2.ps_stack of
          NONE => ([],ps2)
        | SOME d => if d = LENGTH pending - (idx + 1) then ([],ps2)
          else if LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack /\
            operand_equiv dfg op (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)
          then ([], ps2 with ps_stack := stack_poke (LENGTH pending - (idx + 1)) op
            (stack_poke d (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack) ps2.ps_stack))
          else (case do_swap d ps2 of (os1,p1) =>
            case do_swap (LENGTH pending - (idx + 1)) p1 of (os2,p2) => (os1 ++ os2,p2)))
        = (suffix,ps'))
Proof
  ACCEPT_TAC symControlReorderOwnTheory.sym_reorder_one_decompose
QED

Theorem control_reorder_one_decompose:
  reorder_one dfg pending idx op ps = (ops,ps') ==>
  ?restore_ops ps1.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ((stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
       (LENGTH pending) ps1.ps_stack = NONE /\ ops = restore_ops /\ ps' = ps1) \/
     ?dist reduce_ops ps2 suffix.
       stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
         (LENGTH pending) ps1.ps_stack = SOME dist /\
       (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
         (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
        else ([],ps1)) = (reduce_ops,ps2) /\
       ops = (restore_ops ++ reduce_ops) ++ suffix /\
       ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
       control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps'))
Proof
  pure_rewrite_tac[control_reorder_place_def] >>
  MATCH_ACCEPT_TAC sym_reorder_one_decompose
QED

Theorem sym_reorder_after_reduce_frame_sim:
  residual_budget_wf_marked spill_base pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ idx < LENGTH pending /\
  (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
      (LENGTH pending) ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (restore_ops,ps1) /\
  stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
    (LENGTH pending) ps1.ps_stack = SOME dist /\
  (if dist > 16 then reduce_depth_plan (LENGTH ps1.ps_stack) pending op
     (LENGTH pending - (idx + 1)) (LENGTH pending) ps1
   else ([],ps1)) = (reduce_ops,ps2) /\
  control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps2 = (suffix,ps') /\
  ps2.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T)
      ((restore_ops ++ reduce_ops) ++ suffix) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= spill_base /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc
    (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) cs = AsmOK cs' /\
    sym_steps p env
      (LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc +
      LENGTH (execute_plan initial_fmp ((restore_ops ++ reduce_ops) ++ suffix))
Proof
  rewrite_tac[sym_frame_inv_def, control_reorder_place_def] >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_after_reduce_frame_sim_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  disch_then assume_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  fs[listTheory.EVERY_APPEND] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_reorder_one_frame_sim_marked:
  !base.
  residual_budget_wf_marked base pending ps /\ pending_inventory_wf pending ps /\
  (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
  op <> dead_stack_marker /\ idx < LENGTH pending /\ MEM op pending /\
  LENGTH pending <= LENGTH ps.ps_stack /\
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  residual_budget_wf_marked base pending ps' /\ pending_inventory_wf pending ps' /\
  LENGTH pending <= LENGTH ps'.ps_stack /\
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  gen_tac >> rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_one_frame_sim_marked_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  disch_then assume_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  fs[] >> first_x_assum drule_all >> strip_tac >> simp[] >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_plan_steps_reorder_alloc:
  !items ps ops ps'.
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  ACCEPT_TAC symControlReorderOwnTheory.sym_plan_steps_reorder_alloc
QED

Theorem sym_plan_steps_reorder_cons_frame_sim:
  (!qs tail_ops qs' ac sy.
    residual_budget_wf_marked spill_base pending qs /\ pending_inventory_wf pending qs /\
    LENGTH pending <= LENGTH qs.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items qs = (tail_ops,qs') /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) tail_ops /\
    r.sr_spill_base <= qs'.ps_alloc.sa_spill_base /\
    qs'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 qs' ac' sy' /\
      ac'.as_pc = ac.as_pc + LENGTH (execute_plan initial_fmp tail_ops)) ==>
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
  LENGTH pending <= LENGTH ps.ps_stack /\ idx < LENGTH pending /\ MEM op pending /\
  reorder_one dfg pending idx op ps = (step_ops,ps1) /\
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps1 = (rest_ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (step_ops ++ rest_ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\ asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (step_ops ++ rest_ops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (step_ops ++ rest_ops))
Proof
  rewrite_tac[sym_frame_inv_def] >> strip_tac >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_plan_steps_reorder_cons_frame_sim_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[])) >>
  disch_then assume_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  fs[listTheory.EVERY_APPEND] >> first_x_assum drule_all >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_plan_steps_reorder_frame_sim_marked:
  !items ps ops ps' cs ss.
    EVERY (\(idx,op). idx < LENGTH pending /\ MEM op pending) items /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_plan_steps_reorder_frame_sim_marked_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  disch_then assume_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  fs[] >> first_x_assum drule_all >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_reorder_plan_frame_sim_marked:
  !spill_base.
    residual_budget_wf_marked spill_base pending ps /\ pending_inventory_wf pending ps /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    reorder_plan dfg pending ps = (ops,ps') /\
    dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
    asm_static_wf p /\
    asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
    ?cs' ss'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
      cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  gen_tac >> rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_reorder_plan_frame_sim_marked_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    drule_all (SRULE [sym_frame_inv_def] sym_do_swap_pair_frame_sim) >>
    disch_then (qx_choose_then `ac` (qx_choose_then `sy` strip_assume_tac)) >>
    qexistsl [`ac`, `sy`] >> simp[] >> decide_tac)) >>
  disch_then assume_tac >>
  qpat_x_assum `dfg = dfg_build_function fn` SUBST_ALL_TAC >>
  fs[] >> first_x_assum drule_all >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_restore_spilled_cons_frame_sim:
  (!qs tail_ops qs' ac sy.
    restore_spilled_plan targets qs = (tail_ops,qs') /\
    spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled /\
    (!off. MEM (SORestore off) tail_ops ==> off < dimword(:256)) /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    asm_block_at p ac.as_pc (execute_plan initial_fmp tail_ops) ==>
    ?ac' sy'.
      asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
        (LENGTH (execute_plan initial_fmp tail_ops)) ac = AsmOK ac' /\
      sym_steps p env (LENGTH (execute_plan initial_fmp tail_ops)) sy = SymOK sy' /\
      sym_frame_inv p env ctx cplan fn ret srest labs0 qs' ac' sy' /\
      ac'.as_pc = LENGTH (execute_plan initial_fmp tail_ops) + ac.as_pc) /\
  do_restore op ps = (ops1,ps1) /\
  restore_spilled_plan targets ps1 = (ops2,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops1 \/ MEM (SORestore off) ops2 ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  rewrite_tac[sym_frame_inv_def] >> strip_tac >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_restore_spilled_cons_frame_sim_mode_conditional))) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  impl_tac >- (simp[] >> conj_tac
    >- (rpt gen_tac >> strip_tac >> first_x_assum drule_all >>
        disch_then (qx_choose_then `out` (qx_choose_then `sout` strip_assume_tac)) >>
        qexistsl [`out`, `sout`] >> simp[] >> decide_tac) >> metis_tac[]) >>
  disch_then (qx_choose_then `final` (qx_choose_then `sfinal` strip_assume_tac)) >>
  qexistsl [`final`, `sfinal`] >> simp[]
QED

Theorem sym_restore_spilled_plan_frame_sim:
  !targets ps ops ps' cs ss.
  restore_spilled_plan targets ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_restore_spilled_plan_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_jmp_prepare_frame_sim:
  !base.
  generated_plan_state_wf_marked base ps /\
  pending_inventory_wf pending ps /\
  restore_spilled_plan pending ps = (restore_ops,prepared) /\
  reorder_plan dfg pending prepared = (reorder_ops,arranged) /\
  (!off. MEM (SORestore off) restore_ops ==> off < dimword(:256)) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) reorder_ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (restore_ops ++ reorder_ops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (restore_ops ++ reorder_ops))
Proof
  gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      symControlReorderOwnTheory.sym_jmp_prepare_frame_sim_mode_conditional)) >>
  (impl_tac >- metis_tac[asm_sym_steps_lockstep]) >>
  (impl_tac >- (rpt gen_tac >> simp[GSYM sym_frame_inv_def] >> strip_tac >>
    drule_at (Pat `asm_block_at _ _ _`)
      (SRULE [listTheory.EVERY_APPEND] sym_do_swap_pair_frame_sim) >>
    simp[] >> disch_then drule_all >> strip_tac >>
    rename1 `sym_steps _ _ _ _ = SymOK ss_end` >>
    qexistsl [`cs''`, `ss_end`] >> fs[sym_frame_inv_def])) >>
  disch_then (qspec_then `base'` mp_tac) >> simp[] >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

(* A branch condition cannot carry either class of symbolic label. *)

Theorem sym_jnz_condition_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
  ~is_label_operand cond_op /\ cond_op <> dead_stack_marker /\
  op_kind_ok fn ret cond_op sv ==>
  ?w. sv = Val w
Proof
  metis_tac [Q.INST [`allow_own` |-> `F`]
    (SPEC_ALL symControlJumpOwnTheory.sym_jnz_condition_kind_mode)]
QED

(* Static code-label resolution agrees with the concrete jump map. *)

Theorem sym_code_label_dest:
  asm_static_wf p /\ MEM (AsmLabel l) p /\
  FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc ==>
  sym_jump_dest p (Lab l 0) = SOME pc
Proof
  metis_tac[symFrameControlOwnTheory.sym_code_label_dest_reloc,
    code_labels_agree_refl]
QED

(* The symbolic jump consumes only its explicitly typed destination. *)

Theorem sym_jump_steps:
  asm_block_at p ss.sym_base.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab l 0 :: stk /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] symControlJumpOwnTheory.sym_jump_steps_mode))
QED

Theorem sym_jmp_suffix:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 2 ss =
    SymOK (ss with sym_base := ss.sym_base with as_pc := pc)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] symControlJumpOwnTheory.sym_jmp_suffix_mode))
QED

Theorem sym_jnz_suffix_nonzero:
  asm_block_at p ss.sym_base.as_pc [AsmPushLabel l; AsmOp "JUMPI"] /\
  ss.sym_stack = Val w :: stk /\ w <> 0w /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  sym_steps p env 2 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] symControlJumpOwnTheory.sym_jnz_suffix_nonzero_mode))
QED

Theorem sym_jnz_suffix_zero:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  ss.sym_stack = Val 0w :: stk /\
  sym_jump_dest p (Lab lz 0) = SOME pc ==>
  sym_steps p env 4 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := pc;
                    sym_stack := stk|>)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`] symControlJumpOwnTheory.sym_jnz_suffix_zero_mode))
QED

Theorem sym_kinds_ok_pop:
  !cp fn ret srest ps ss op sv stk base'.
  sym_kinds_ok cp fn ret srest
    (ps with ps_stack := SNOC op ps.ps_stack) ss /\
  ss.sym_stack = sv :: stk ==>
  sym_kinds_ok cp fn ret srest ps
    (ss with <|sym_base := base'; sym_stack := stk|>)
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_kinds_ok_pop
QED

Theorem noncopy_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM out inst.inst_outputs /\
  inst.inst_opcode <> ADD /\ inst.inst_opcode <> ASSIGN ==>
  ~code_end_var fn out
Proof
  ACCEPT_TAC symControlGasOwnTheory.noncopy_output_not_code_end
QED

Theorem sym_gas_output_not_code_end:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  ~code_end_var fn out
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_gas_output_not_code_end
QED

Theorem sym_gas_output_kind:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs ==>
  op_kind_ok fn ret (Var out) (Val w)
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_gas_output_kind
QED

(* GAS reads no symbolic operands or memory and produces a word. *)

Theorem sym_step_gas:
  sym_step p env (AsmOp "GAS") ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_step_gas
QED

Theorem sym_gas_steps:
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|
      sym_base := ss.sym_base with <|as_pc := ss.sym_base.as_pc + 1;
        as_stack := []; as_gas_readings := TL ss.sym_base.as_gas_readings|>;
      sym_stack := Val (HD (ss.sym_base.as_gas_readings ++ [0w])) ::
                   ss.sym_stack|>)
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_gas_steps
QED

Theorem sym_gas_kinds_steps:
  !cp fn ret srest ps ss p env out.
  sym_kinds_ok cp fn ret srest ps ss /\
  op_kind_ok fn ret (Var out)
    (Val (HD (ss.sym_base.as_gas_readings ++ [0w]))) /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"] ==>
  ?ss'. sym_steps p env 1 ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_gas_kinds_steps
QED

Theorem sym_gas_emit_frame_sim:
  !p env ctx cp fn ret srest labs0 ps cs ss inst out.
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = GAS /\ MEM out inst.inst_outputs /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "GAS"] ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      1 cs = AsmOK cs' /\
    sym_steps p env 1 ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (ps with ps_stack := SNOC (Var out) ps.ps_stack) cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"]` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_gas_emit_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[]
QED

(* The return suffix removes the opaque PC and preserves all label memory. *)

Theorem sym_ret_suffix_steps:
  !p env ctx cp fn ret srest labs0 ps cs ss values pc.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "JUMP"] /\
  ss.sym_stack = Lab ret 0 :: (MAP Val (REVERSE values) ++ srest) /\
  sym_jump_dest p (Lab ret 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      1 cs = AsmOK cs' /\
    sym_steps p env 1 ss = SymOK ss' /\ asm_sym_rel p env cs' ss' /\
    cs'.as_pc = pc /\
    ss'.sym_stack = MAP Val (REVERSE values) ++ srest /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
         FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  irule (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL symControlRetOwnTheory.sym_ret_suffix_steps_mode_conditional))) >>
  simp[] >> metis_tac[]
QED

Theorem ret_operand_not_code_end:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  label_flow_ok ctx /\ inst.inst_opcode = RET /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  ACCEPT_TAC (SRULE [] (Q.INST [`allow_own` |-> `F`]
    symControlRetOwnTheory.ret_operand_not_code_end_mode))
QED

Theorem ret_payload_var_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = RET /\ inst.inst_operands = front ++ [Var pc] /\
  MEM (Var x) front /\ Var x <> dead_stack_marker /\
  op_kind_ok fn ret (Var x) sv ==> ?w. sv = Val w
Proof
  ACCEPT_TAC (SRULE [] (Q.INST [`allow_own` |-> `F`]
    symControlRetOwnTheory.ret_payload_var_kind_mode))
QED

Theorem ret_payload_op_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  inst.inst_opcode = RET /\ inst.inst_operands = front ++ [Var pc] /\
  MEM op front /\ op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  ACCEPT_TAC (SRULE [] (Q.INST [`allow_own` |-> `F`]
    symControlRetOwnTheory.ret_payload_op_kind_mode))
QED

Theorem ret_compute_operands_last_retpc:
  MEM inst (fn_insts (reachable_fn fn)) /\ retpc_shape_ok fn /\
  inst.inst_opcode = RET ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x
Proof
  ACCEPT_TAC symControlRetOwnTheory.ret_compute_operands_last_retpc
QED

Theorem ret_source_op_kinds:
  MEM inst (fn_insts (reachable_fn fn)) /\ codegen_ready_fn fn /\
  opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode = RET /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) ==>
  ?front x. compute_operands inst = front ++ [Var x] /\ retpc_var fn x /\
    (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w)
Proof
  ACCEPT_TAC (SRULE [] (Q.INST [`allow_own` |-> `F`]
    symControlRetOwnTheory.ret_source_op_kinds_mode))
QED

Theorem word_kind_concretization:
  MEM op ops /\ op_kind_ok fn ret op sv /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  sval_conc lo sv = SOME w ==> sv = Val w
Proof
  ACCEPT_TAC symFrameControlFactsTheory.word_kind_concretization
QED

Theorem word_kind_prefix_concretization:
  !ops top values.
  LIST_REL (op_kind_ok fn ret) ops top /\
  (!op sv. MEM op ops /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w)
    (top ++ srest) (values ++ rest) /\ LENGTH values = LENGTH ops ==>
  top = MAP Val values
Proof
  ACCEPT_TAC symFrameControlFactsTheory.word_kind_prefix_concretization
QED

Theorem ret_prepared_symbolic_stack:
  !p env cs ss cp fn ret srest ps front x ra values rest.
  asm_sym_rel p env cs ss /\ sym_kinds_ok cp fn ret srest ps ss /\
  ps.ps_stack = front ++ [Var x] /\ retpc_var fn x /\
  Var x <> dead_stack_marker /\
  (!op sv. MEM op front /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = ra :: values ++ rest /\ LENGTH values = LENGTH front ==>
  ss.sym_stack = Lab ret 0 :: MAP Val values ++ srest
Proof
  rpt gen_tac >> strip_tac >> fs[listTheory.APPEND] >>
  drule (SRULE [asm_sym_rel_core_canonical]
    (Q.SPECL [`SND (compute_label_offsets p)`, `asm_data_env_ok p env`]
      symControlRetOwnTheory.ret_prepared_symbolic_stack_core)) >>
  disch_then drule_all >> simp[]
QED

Theorem source_memory_range_label_free:
  !cp labs inst vs off sz.
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  MEM (off,sz) (source_memory_read_ranges inst vs) ==>
  ~mem_labels_hit labs (in_mem_range off sz)
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.source_memory_range_label_free
QED

Theorem terminal_source_memory_reads_safe:
  !cp.
  MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
    CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\ inst_wf inst /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  (!b. b IN FDOM labs ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs ==>
  ~mem_labels_hit labs (asm_op_mem_reads name args)
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.terminal_source_memory_reads_safe
QED

Theorem mem_labels_clear_read_safe:
  ~mem_labels_hit (mem_labels_clear labs P) P
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.mem_labels_clear_read_safe
QED

Theorem sym_steps_terminal_extend:
  sym_terminal (sym_steps p env n ss) ==>
  sym_steps p env (n + k) ss = sym_steps p env n ss
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`]
      symControlTerminalSafetyOwnTheory.sym_steps_terminal_extend_mode))
QED

Theorem sym_step_concrete_word_prefix:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss =
    sym_lift (LENGTH args)
      (mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)) ss
      (asm_step_op FEMPTY name (ss.sym_base with as_stack := args))
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.sym_step_concrete_word_prefix
QED

Theorem sym_step_concrete_word_prefix_not_bad:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  sym_step_concrete name ss <> SymBad e
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.sym_step_concrete_word_prefix_not_bad
QED

Theorem asm_sym_step_rel_terminal:
  asm_sym_step_rel p env sr cr /\ (!e. sr <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal sr
Proof
  metis_tac [SRULE [asm_sym_step_rel_core_canonical]
    (Q.INST [`R` |-> `asm_sym_rel p env`]
      (SPEC_ALL symControlTerminalSafetyOwnTheory.bridge_result_terminal))]
QED

Theorem sym_terminal_opcode_concrete:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] ==>
  sym_step_op p env name ss = sym_step_concrete name ss
Proof
  ACCEPT_TAC symControlTerminalSafetyOwnTheory.sym_terminal_opcode_concrete
QED

Theorem sym_terminal_step_runs:
  asm_block_at p ss.sym_base.as_pc [inst] /\
  sym_terminal (sym_step p env inst ss) ==>
  sym_steps p env 1 ss = sym_step p env inst ss
Proof
  metis_tac [SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
    symControlTerminalSafetyOwnTheory.sym_terminal_step_runs_mode)]
QED

Theorem sym_terminal_opcode_safe:
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) ==>
  !e. sym_step p env (AsmOp name) ss <> SymBad e
Proof
  strip_tac >> simp[sym_step_def, sym_terminal_opcode_concrete] >>
  metis_tac[sym_step_concrete_word_prefix_not_bad]
QED

Theorem sym_terminal_step_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs = cr /\
  (!e. sym_step p env inst ss <> SymBad e) /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps p env 1 ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL symControlTerminalSafetyOwnTheory.sym_terminal_step_transfer_mode_conditional))) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs'.as_pc < LENGTH p /\ EL cs'.as_pc p = ai` by
        fs[asmSemTheory.asm_block_at_def] >>
      drule_all asm_sym_step >>
      Cases_on `sym_step p env ai ss'` >>
      gvs[asm_sym_step_rel_def]) >>
  simp[] >> qexistsl [`cs`, `inst`] >> simp[]
QED

Theorem sym_terminal_opcode_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [AsmOp name] /\
  MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
            "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"] /\
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp name) cs = cr /\
  ((?s. cr = AsmHalt s) \/ (?s. cr = AsmRevert s) \/ (?s. cr = AsmFault s)) ==>
  sym_terminal (sym_steps p env 1 ss)
Proof
  strip_tac >> irule sym_terminal_step_transfer >>
  drule_all sym_terminal_opcode_safe >> metis_tac[]
QED

Theorem sym_revert_postamble_steps:
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps p env 4 ss)
Proof
  ACCEPT_TAC symControlForwardSourceFactsTheory.sym_revert_postamble_steps
QED

Theorem sym_step_concrete_clears_written_labels:
  ss.sym_stack = MAP Val args ++ tail /\ LENGTH args = asm_op_arity name /\
  ~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name args) /\
  sym_step_concrete name ss = SymOK ss' ==>
  ss'.sym_mem_labels =
    mem_labels_clear ss.sym_mem_labels (asm_op_mem_writes name args)
Proof
  ACCEPT_TAC symControlForwardCopyOwnTheory.sym_step_concrete_clears_written_labels
QED

Theorem sym_returndatacopy_clears_range:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  ACCEPT_TAC symControlForwardCopyOwnTheory.sym_returndatacopy_clears_range
QED

Theorem asm_sym_step_rel_ok:
  asm_sym_step_rel p env sr (AsmOK cs') /\ (!e. sr <> SymBad e) ==>
  ?ss'. sr = SymOK ss' /\ asm_sym_rel p env cs' ss'
Proof
  ACCEPT_TAC (SRULE [asm_sym_step_rel_core_canonical]
    (Q.INST [`R` |-> `asm_sym_rel p env`]
      (SPEC_ALL symControlForwardCopyOwnTheory.asm_sym_step_rel_ok_core)))
QED

Theorem sym_ok_step_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [inst] /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) inst cs = AsmOK cs' /\
  (!e. sym_step p env inst ss <> SymBad e) ==>
  ?ss'. sym_step p env inst ss = SymOK ss' /\ asm_sym_rel p env cs' ss'
Proof
  strip_tac >>
  `cs.as_pc < LENGTH p /\ EL cs.as_pc p = inst` by fs[asmSemTheory.asm_block_at_def] >>
  metis_tac[symEmitSimTheory.asm_sym_step_success_from_safe]
QED

Theorem sym_returndatacopy_success_inventory:
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' ==>
  ss'.sym_stack = tail /\
  (!b. b IN FDOM ss'.sym_mem_labels ==> b IN FDOM ss.sym_mem_labels)
Proof
  ACCEPT_TAC symControlForwardCopyOwnTheory.sym_returndatacopy_success_inventory
QED

Theorem sym_returndatacopy_success_transfer:
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  asm_block_at p cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  ss.sym_stack = Val dst :: Val src :: Val sz :: tail /\
  asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss'. sym_step p env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
        asm_sym_rel p env cs' ss' /\
        ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  strip_tac >> irule (SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`]
      (SPEC_ALL symControlForwardCopyOwnTheory.sym_returndatacopy_success_transfer_core))) >>
  metis_tac[]
QED

Theorem restore_swap_sequence_member:
  MEM i idxs ==>
  MEM (SORestore (EL i offsets))
    (FLAT (MAP (\j. [SORestore (EL j offsets); SOSwap 1]) idxs))
Proof
  ACCEPT_TAC symControlReplayOwnTheory.restore_swap_sequence_member
QED

Theorem deep_dup_restore_sequence_member:
  31 < d ==>
  MEM (SORestore (EL (d - 16) offsets))
    (FLAT (MAP (\i. [SORestore (EL i offsets); SOSwap 1])
      (GENLIST (\i. d - (i + 16)) (d - 15))))
Proof
  ACCEPT_TAC symControlReplayOwnTheory.deep_dup_restore_sequence_member
QED

Theorem do_dup_no_restore_shallow:
  do_dup d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 15
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_dup_no_restore_shallow
QED

Theorem do_dup_read_only_shallow:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 15
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_dup_read_only_shallow
QED

Theorem do_restore_read_only_replay:
  do_restore op ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_restore_read_only_replay
QED

Theorem do_dup_read_only_replay:
  do_dup d ps = (ops, ps') /\ d < LENGTH ps.ps_stack /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_dup_read_only_replay
QED

Theorem emit_var_input_unspilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_var_input_unspilled_read_only_replay
QED

Theorem emit_var_input_spilled_read_only_replay:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_var_input_spilled_read_only_replay
QED

Theorem emit_one_input_read_only_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_one_input_read_only_replay
QED

Theorem emit_input_plan_read_only_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ins) /\
  (!off. MEM (SORestore off) ins ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ins qs /\
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack /\
  (apply_prefix_ops fmp lo ins qs).ps_spilled = ps1.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_input_plan_read_only_replay
QED

Theorem do_dup_spill_free_stack_replay:
  do_dup d ps = (ops, ps') /\ qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_dup_spill_free_stack_replay
QED

Theorem emit_var_input_unspilled_stack_replay:
  FLOOKUP ps.ps_spilled (Var v) = NONE /\
  emit_one_input opc nl (Var v) ps = (ops, ps') /\
  qs.ps_stack = ps.ps_stack /\ (!off. ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_var_input_unspilled_stack_replay
QED

Theorem emit_var_input_spilled_has_restore:
  FLOOKUP ps.ps_spilled (Var v) = SOME off /\
  emit_one_input opc nl (Var v) ps = (ops, ps') ==>
  MEM (SORestore off) ops
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_var_input_spilled_has_restore
QED

Theorem emit_one_input_spill_free_stack_replay:
  emit_one_input opc nl op ps = (ops, ps') /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack = ps'.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_one_input_spill_free_stack_replay
QED

Theorem emit_input_plan_spill_free_stack_replay:
  !inputs ps qs opc nl ins ps1 fmp lo.
  emit_input_plan opc inputs nl ps = (ins, ps1) /\ opc <> INVOKE /\
  qs.ps_stack = ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ins /\ ~MEM (SORestore off) ins) ==>
  (apply_prefix_ops fmp lo ins qs).ps_stack = ps1.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.emit_input_plan_spill_free_stack_replay
QED

Theorem do_restore_read_only_kind_replay:
  do_restore op ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_restore_read_only_kind_replay
QED

Theorem do_swap_read_only_shallow:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  (!off. ~MEM (SOSpill off) ops) ==> d <= 16
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_read_only_shallow
QED

Theorem do_swap_no_restore_shallow:
  do_swap d ps = (ops, ps') /\
  (!off. ~MEM (SORestore off) ops) ==> d <= 16
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_no_restore_shallow
QED

Theorem list_rel_stack_swap:
  LIST_REL R xs ys ==> LIST_REL R (stack_swap d xs) (stack_swap d ys)
Proof
  ACCEPT_TAC symControlReplayOwnTheory.list_rel_stack_swap
QED

Theorem do_swap_spill_free_kind_replay:
  do_swap d ps = (ops, ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_spill_free_kind_replay
QED

Theorem do_swap_read_only_kind_replay:
  do_swap d ps = (ops, ps') /\ ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled /\
  ps'.ps_stack <> []
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_read_only_kind_replay
QED

Theorem do_swap_pair_read_only_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) (ops1 ++ ops2)) ==>
  prefix_spill_wf fmp lo (ops1 ++ ops2) qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_spilled = ps2.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_pair_read_only_kind_replay
QED

Theorem list_rel_op_kind_equiv_trans:
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs ys /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) ys zs ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv) xs zs
Proof
  ACCEPT_TAC symControlReplayOwnTheory.list_rel_op_kind_equiv_trans
QED

Theorem reorder_restore_no_restore_identity:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SORestore off) ops) ==> ops = [] /\ ps1 = ps
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_restore_no_restore_identity
QED

Theorem do_swap_pair_spill_free_kind_replay:
  do_swap d ps = (ops1,ps1) /\ do_swap f ps1 = (ops2,ps2) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) (ops1 ++ ops2)) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (ops1 ++ ops2) qs).ps_stack ps2.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.do_swap_pair_spill_free_kind_replay
QED

Theorem stack_exchange_kind_replay:
  stack_get_unfixed_depth op f n ps.ps_stack = SOME d /\
  f < LENGTH ps.ps_stack /\ dfg = dfg_build_function fn /\
  ssa_form fn /\ fn_shape_ok fn /\
  operand_equiv dfg op (stack_peek f ps.ps_stack) /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack (stack_poke f op (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
Proof
  ACCEPT_TAC symControlReplayOwnTheory.stack_exchange_kind_replay
QED

Theorem reorder_swap_pair_case_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_swap_pair_case_kind_replay
QED

Theorem reorder_swap_pair_case_read_only_kind_replay:
  (case do_swap d ps of (ops1,ps1) =>
     case do_swap f ps1 of (ops2,ps2) => (ops1 ++ ops2,ps2)) = (ops,ps') /\
  ps.ps_stack <> [] /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_swap_pair_case_read_only_kind_replay
QED

Theorem control_reorder_place_read_only_kind_replay:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!off. ~MEM (SOSpill off) ops) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  rewrite_tac[control_reorder_place_def] >>
  ACCEPT_TAC symControlReplayOwnTheory.control_reorder_place_read_only_kind_replay_expr
QED

Theorem control_reorder_place_spill_free_kind_replay:
  control_reorder_place dfg pending op f ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  rewrite_tac[control_reorder_place_def] >>
  ACCEPT_TAC symControlReplayOwnTheory.control_reorder_place_spill_free_kind_replay_expr
QED

Theorem reorder_reduce_no_spill_identity:
  (if (dist:num) > 16 then reduce_depth_plan (LENGTH ps.ps_stack) pending op f n ps
   else ([],ps)) = (ops,ps1) /\
  (!off. ~MEM (SOSpill off) ops) ==> ops = [] /\ ps1 = ps
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_reduce_no_spill_identity
QED

Theorem reorder_restore_read_only_kind_replay:
  (case stack_get_unfixed_depth op f n ps.ps_stack of
     NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                | SOME off => do_restore op ps)
   | SOME d => ([],ps)) = (ops,ps') /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_restore_read_only_kind_replay
QED

Theorem reorder_one_read_only_decompose:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops) ==>
  ?restore_ops ps1 suffix.
    (case stack_get_unfixed_depth op (LENGTH pending - (idx + 1))
        (LENGTH pending) ps.ps_stack of
       NONE => (case FLOOKUP ps.ps_spilled op of NONE => ([],ps)
                  | SOME off => do_restore op ps)
     | SOME d => ([],ps)) = (restore_ops,ps1) /\
    ops = restore_ops ++ suffix /\
    control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps1 = (suffix,ps')
Proof
  rewrite_tac[control_reorder_place_def] >>
  ACCEPT_TAC symControlReplayOwnTheory.reorder_one_read_only_decompose_expr
QED

Theorem reorder_one_read_only_kind_replay:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_one_read_only_kind_replay
QED

Theorem reorder_steps_read_only_kind_replay:
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_steps_read_only_kind_replay
QED

Theorem reorder_plan_read_only_kind_replay:
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) ops) /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo ops qs /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack /\
  (apply_prefix_ops fmp lo ops qs).ps_spilled = ps'.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.reorder_plan_read_only_kind_replay
QED

Theorem sym_frame_inv_kind_transport:
  !p env ctx cp fn ret srest labs0 ps cs ss qs.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    ps.ps_stack qs.ps_stack /\ ps.ps_spilled = qs.ps_spilled ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 qs cs ss
Proof
  ACCEPT_TAC symControlReplayOwnTheory.sym_frame_inv_kind_transport
QED

Theorem selected_prefix_read_only_kind_replay:
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp lo.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) ==>
  prefix_spill_wf fmp lo (iops ++ rops) ps /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_stack ps2.ps_stack /\
  (apply_prefix_ops fmp lo (iops ++ rops) ps).ps_spilled = ps2.ps_spilled
Proof
  ACCEPT_TAC symControlReplayOwnTheory.selected_prefix_read_only_kind_replay
QED

Theorem sym_read_only_selected_prefix_frame_sim:
  !opc inputs nl ps iops ps1 dfg rops ps2 fn ret fmp p env ctx cp srest labs0 cs ss.
  emit_input_plan opc inputs nl ps = (iops,ps1) /\
  reorder_plan dfg inputs ps1 = (rops,ps2) /\ opc <> INVOKE /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  (!op1 off1 op2 off2.
    FLOOKUP ps.ps_spilled op1 = SOME off1 /\
    FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
    off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  prefix_wf (SND (compute_label_offsets p)) (LENGTH ps.ps_stack) (iops ++ rops) /\
  EVERY is_prefix_op (iops ++ rops) /\
  EVERY (\op. !l d. op <> SOPushOfst l d) (iops ++ rops) /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps2 cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel p env cs ss /\ sym_steps p env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n cs = AsmOK cs' /\
      asm_sym_rel p env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
             `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`,
             `dfg` |-> `dfg_build_function fn`]
      (SPEC_ALL symControlReplayOwnTheory.sym_read_only_selected_prefix_frame_sim_mode_conditional))) >>
  strip_tac >> qexistsl [`cs'`, `ss'`] >> simp[]
QED

Theorem sym_ret_prepare_frame_sim:
  !inputs nl ps iops prepared dfg rops arranged fn ret fmp p env ctx cp srest labs0 cs ss base.
  emit_input_plan RET inputs nl ps = (iops,prepared) /\
  reorder_plan dfg inputs prepared = (rops,arranged) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  generated_plan_state_wf_marked base ps /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!l. MEM (Label l) inputs ==> IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l)) /\
  (!off. ~MEM (SOSpill off) (iops ++ rops)) /\
  (!off. MEM (SORestore off) (iops ++ rops) ==> off < dimword(:256)) /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc (execute_plan fmp (iops ++ rops)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  irule
    (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
                       COND_CLAUSES, GSYM sym_frame_inv_def]
      (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
               `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
        (SPEC_ALL symControlRetOwnTheory.sym_ret_prepare_frame_sim_mode_conditional))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule sym_read_only_selected_prefix_frame_sim >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem sym_ret_generated_prepare_frame_sim:
  !base cp.
  inst.inst_opcode = RET /\ inst_wf inst /\
  MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  generate_inst_plan lv (dfg_build_function fn) cfg fn inst nl halting term label ps =
    SOME (ops,final) /\ final.ps_stack = [] /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  asm_block_at p cs.as_pc (execute_plan fmp ops) /\ asm_static_wf p /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss ==>
  ?iops prepared rops arranged cs' ss'.
    emit_input_plan RET (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan (dfg_build_function fn) (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "JUMP"] /\
    final.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack /\
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan fmp (iops ++ rops))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan fmp (iops ++ rops))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan fmp (iops ++ rops)) /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >>
  irule
    (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
                       COND_CLAUSES, GSYM sym_frame_inv_def]
      (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
               `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
        (SPEC_ALL symControlRetOwnTheory.sym_ret_generated_prepare_frame_sim_mode_conditional))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule sym_read_only_selected_prefix_frame_sim >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem reorder_one_spill_free_placement:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  control_reorder_place dfg pending op (LENGTH pending - (idx + 1)) ps = (ops,ps')
Proof
  rewrite_tac[control_reorder_place_def] >>
  match_mp_tac symControlForwardPrepareOwnTheory.reorder_one_spill_free_placement_conditional >>
  simp_tac bool_ss [GSYM control_reorder_place_def] >> rpt conj_tac
  >- ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- ACCEPT_TAC list_rel_op_kind_transport
  >- MATCH_ACCEPT_TAC (SRULE [listTheory.APPEND_ASSOC] control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SRULE []
        (Q.INST [`dfg` |-> `dfg_build_function fn`]
          (SPEC_ALL control_reorder_place_spill_free_kind_replay))))
  >- MATCH_ACCEPT_TAC reorder_restore_no_restore_identity
  >- MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity
  >- MATCH_ACCEPT_TAC do_swap_no_restore_shallow
  >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem reorder_one_spill_free_kind_replay:
  reorder_one dfg pending idx op ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.reorder_one_spill_free_kind_replay_conditional >>
  simp_tac bool_ss [GSYM control_reorder_place_def] >> rpt conj_tac
  >- ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- ACCEPT_TAC list_rel_op_kind_transport
  >- MATCH_ACCEPT_TAC (SRULE [listTheory.APPEND_ASSOC] control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SRULE []
        (Q.INST [`dfg` |-> `dfg_build_function fn`]
          (SPEC_ALL control_reorder_place_spill_free_kind_replay))))
  >- MATCH_ACCEPT_TAC reorder_restore_no_restore_identity
  >- MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity
  >- MATCH_ACCEPT_TAC do_swap_no_restore_shallow
  >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem reorder_steps_spill_free_kind_replay:
  !items ps qs ops ps' dfg pending fn ret fmp lo.
  plan_steps (\(idx,op) ps. reorder_one dfg pending idx op ps) items ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.reorder_steps_spill_free_kind_replay_conditional >>
  simp_tac bool_ss [GSYM control_reorder_place_def] >> rpt conj_tac
  >- ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- ACCEPT_TAC list_rel_op_kind_transport
  >- MATCH_ACCEPT_TAC (SRULE [listTheory.APPEND_ASSOC] control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SRULE []
        (Q.INST [`dfg` |-> `dfg_build_function fn`]
          (SPEC_ALL control_reorder_place_spill_free_kind_replay))))
  >- MATCH_ACCEPT_TAC reorder_restore_no_restore_identity
  >- MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity
  >- MATCH_ACCEPT_TAC do_swap_no_restore_shallow
  >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem reorder_plan_spill_free_kind_replay:
  reorder_plan dfg pending ps = (ops,ps') /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    qs.ps_stack ps.ps_stack /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) ==>
  LIST_REL (\x y. !sv. op_kind_ok fn ret x sv <=> op_kind_ok fn ret y sv)
    (apply_prefix_ops fmp lo ops qs).ps_stack ps'.ps_stack
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.reorder_plan_spill_free_kind_replay_conditional >>
  simp_tac bool_ss [GSYM control_reorder_place_def] >> rpt conj_tac
  >- ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- ACCEPT_TAC list_rel_op_kind_transport
  >- MATCH_ACCEPT_TAC (SRULE [listTheory.APPEND_ASSOC] control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC (SRULE []
        (Q.INST [`dfg` |-> `dfg_build_function fn`]
          (SPEC_ALL control_reorder_place_spill_free_kind_replay))))
  >- MATCH_ACCEPT_TAC reorder_restore_no_restore_identity
  >- MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity
  >- MATCH_ACCEPT_TAC do_swap_no_restore_shallow
  >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

(* Diagnostic: the spill-free prefix contract needs no spill kinds or budget. *)
Theorem sym_spill_free_stack_only_prefix_sim:
  !ops lo ps ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest
      (apply_prefix_ops fmp lo ops (ps with ps_spilled := FEMPTY)) ss' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symControlForwardPrepareOwnTheory.sym_spill_free_stack_only_prefix_sim
QED

Theorem sym_rf_preparation_stack_sim:
  !opc inputs nl ps ins ps1 fn ros ps2 (lo:string |-> num) ss top srest ret cp p fmp env.
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ ssa_form fn /\ fn_shape_ok fn /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (ins ++ ros)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.sym_rf_preparation_stack_sim_conditional >>
  rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
  >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem assign_output_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs ==>
  (op_kind_ok fn ret rhs sv <=> op_kind_ok fn ret (Var out) sv)
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.assign_output_op_kind
QED

Theorem assign_prepared_stack_op_kind:
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [rhs])) top ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (stack_push (Var out) tail)) top
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.assign_prepared_stack_op_kind
QED

Theorem simple_do_swap_replay_wf:
  do_swap d ps = (ops,ps') /\ d < LENGTH ps.ps_stack /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.simple_do_swap_replay_wf_conditional >>
  rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
  >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem optimistic_simple_replay_wf:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  EVERY is_simple_stack_op ops ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  apply_prefix_ops fmp lo ops ps = ps'
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.optimistic_simple_replay_wf_conditional >>
  rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
  >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem simple_prefix_equal_stack_replay:
  !ops ps qs fmp lo.
  EVERY is_simple_stack_op ops /\ qs.ps_stack = ps.ps_stack ==>
  (apply_prefix_ops fmp lo ops qs).ps_stack =
    (apply_prefix_ops fmp lo ops ps).ps_stack
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.simple_prefix_equal_stack_replay
QED

Theorem sym_simple_prefix_stack_sim:
  !ops lo ps ps' ss top srest fn ret cp p fmp env.
  EVERY is_simple_stack_op ops /\
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  (apply_prefix_ops fmp lo ops ps).ps_stack = ps'.ps_stack /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.sym_simple_prefix_stack_sim
QED

Theorem assign_postfix_simple_replay_wf:
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) ==>
  prefix_wf lo (LENGTH ps.ps_stack) (pops ++ opts) /\
  (apply_prefix_ops fmp lo (pops ++ opts) ps).ps_stack =
    (release_dead_spills nl ps9).ps_stack
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.assign_postfix_simple_replay_wf_conditional >>
  rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
  >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem sym_assign_postfix_stack_sim:
  !ps out tail halting nl pops ps8 dfg inst term opts ps9 (lo:string |-> num) ss top srest fn ret cp p fmp env.
  ps.ps_stack = stack_push (Var out) tail /\
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  EVERY is_simple_stack_op (pops ++ opts) /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (pops ++ opts)) ==>
  ?ss' top'.
    sym_steps p env (LENGTH (execute_plan fmp (pops ++ opts))) ss = SymOK ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (release_dead_spills nl ps9).ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  match_mp_tac symControlForwardPrepareOwnTheory.sym_assign_postfix_stack_sim_conditional >>
  rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
  >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
  >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts
QED

Theorem rf_assign_preparation_stack_facts:
  emit_input_plan ASSIGN [rhs] nl ps = (ins,ps1) /\
  reorder_plan dfg [rhs] ps1 = (ros,ps2) /\
  ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) ==>
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf (lo:string |-> num) (LENGTH ps.ps_stack) (ins ++ ros) /\
  ps2.ps_stack = stack_pop 1 ps2.ps_stack ++ [rhs]
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.rf_assign_preparation_stack_facts
QED

Theorem sym_assign_prepared_stack_sim:
  !ps2 tail rhs fn inst out ret ss top srest.
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  ps2.ps_stack = tail ++ [rhs] /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top ==>
  LIST_REL (op_kind_ok fn ret)
    (REVERSE (ps2 with ps_stack := stack_push (Var out) tail).ps_stack) top
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.sym_assign_prepared_stack_sim
QED

Theorem sym_rf_suffix_preparation_execution:
  !fn ps opc inputs nl ins ps1 ros ps2 ra lo entry s stk st rest prog fmp
   env ss top srest ret cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  emit_input_plan opc inputs nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) inputs ps1 = (ros,ps2) /\
  opc <> INVOKE /\ LENGTH inputs <= 16 /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inputs /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. MEM op inputs ==> operand_val (frame_view fn ra s) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) (ins ++ ros) /\
         ~MEM (SORestore off) (ins ++ ros)) /\
  EVERY is_simple_stack_op (ins ++ ros) /\
  prefix_wf lo (LENGTH ps.ps_stack) (ins ++ ros) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp (ins ++ ros)) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s) ps2.ps_stack stk' /\
    rf_inventory_inv fn ra lo entry ps2 s /\
    ps2.ps_stack = stack_pop (LENGTH inputs) ps2.ps_stack ++ inputs /\
    sym_steps prog env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    asm_sym_rel prog env mid ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  mp_tac symControlForwardPrepareOwnTheory.sym_rf_suffix_preparation_execution_mode_conditional >>
  (impl_tac >-
    (rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
     >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
     >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts)) >>
  disch_then (fn th => drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL th)))) >> simp[]
QED

Theorem rf_assign_postfix_simple:
  (if halting then ([],ps)
   else popmany_plan (if MEM out nl then [] else [Var out]) ps) = (pops,ps8) /\
  (if MEM out nl then optimistic_swap_plan dfg inst nl term ps8
   else ([],ps8)) = (opts,ps9) /\
  (!off. ~MEM (SOSpill off) (pops ++ opts) /\
         ~MEM (SORestore off) (pops ++ opts)) ==>
  EVERY is_simple_stack_op (pops ++ opts)
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.rf_assign_postfix_simple
QED

Theorem sym_plan_runs_compose:
  sym_steps p env (LENGTH (execute_plan fmp ops1)) ss = SymOK mid /\
  sym_steps p env (LENGTH (execute_plan fmp ops2)) mid = SymOK final ==>
  sym_steps p env (LENGTH (execute_plan fmp (ops1 ++ ops2))) ss = SymOK final
Proof
  MATCH_ACCEPT_TAC symControlForwardPrepareOwnTheory.sym_plan_runs_compose
QED

Theorem sym_rf_assign_plan_execution:
  !fn inst ps rhs out ra lo entry s fuel ctx s' lv cfg nl halting term lbl ops ps'
   stk st rest prog fmp env ss top srest ret cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra s') ps'.ps_stack stk' /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    asm_sym_rel prog env st' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  mp_tac symControlForwardPrepareOwnTheory.sym_rf_assign_plan_execution_mode_conditional >>
  (impl_tac >-
    (rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac
     >- MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay
     >- MATCH_ACCEPT_TAC list_rel_op_kind_transport
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_one_decompose)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_restore_no_restore_identity)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity)
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_no_restore_shallow) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts)) >>
  disch_then (fn th => drule_all (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL th)))) >> simp[]
QED

Theorem label_flow_noncopy_operand_not_code_end:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\ label_flow_ok ctx /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> CODECOPY /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  MATCH_ACCEPT_TAC (SRULE []
    (Q.INST [`allow_own` |-> `F`] (SPEC_ALL label_flow_noncopy_operand_not_code_end_mode)))
QED

Theorem ordinary_noncopy_operand_word_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
  inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
  inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  MATCH_ACCEPT_TAC (SRULE []
    (Q.INST [`allow_own` |-> `F`] (SPEC_ALL ordinary_noncopy_operand_word_kind_mode)))
QED

Theorem terminal_operand_word_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  MEM op (compute_operands inst) /\ op <> dead_stack_marker /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  simp [listTheory.MEM] >>
  MATCH_ACCEPT_TAC (SRULE []
    (Q.INST [`allow_own` |-> `F`] (SPEC_ALL terminal_operand_word_kind_mode)))
QED

Theorem word_prepared_symbolic_stack:
  asm_sym_rel p env cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = tail ++ operands /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = values ++ rest /\ LENGTH values = LENGTH operands ==>
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  MATCH_ACCEPT_TAC (SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`code_ok` |-> `asm_data_env_ok p env`,
             `lo` |-> `SND (compute_label_offsets p)`]
      (SPEC_ALL word_prepared_symbolic_stack_core)))
QED

Theorem arranged_word_prepared_symbolic_stack:
  venom_asm_rel lo ps vs mid /\
  ps.ps_stack = tail ++ operands /\
  EVERY (\op. op <> dead_stack_marker) operands /\
  (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
  eval_operands (REVERSE operands) vs = SOME values /\
  asm_sym_rel p env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) ==>
  mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  MATCH_ACCEPT_TAC (SRULE [asm_sym_rel_core_canonical]
    (Q.INST [`code_ok` |-> `asm_data_env_ok p env`,
             `bridge_lo` |-> `SND (compute_label_offsets p)`]
      (SPEC_ALL symControlWordStackOwnTheory.arranged_word_prepared_symbolic_stack_core_split_maps)))
QED

Theorem sym_frame_entry_selected_prefix_sim_marked:
  opc <> INVOKE /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  (!l. MEM (Label l) operands ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op operands /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan opc operands nl ps = (iops,prepared) /\
  reorder_plan dfg selected prepared = (rops,arranged) /\
  PERM operands selected /\ LENGTH operands <= 16 /\
  LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked spillbase ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  (!op at. MEM op operands /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at operands) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  ops = iops ++ rops ++ suffix /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  plan_state_residual_wf_marked spillbase selected (LENGTH selected) arranged /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected /\
  ?mid ss_mid.
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged
      (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    context_memory_rel cplan vs.vs_memory mid.as_memory /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss =
      SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  strip_tac >> gvs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlTerminalPrepareOwnTheory.sym_frame_entry_selected_prefix_sim_marked_mode_conditional)
      |> Q.INST [`dfg` |-> `dfg_build_function fn`, `ops` |-> `iops ++ rops ++ suffix`,
                 `o2pc` |-> `build_offset_to_pc prog`])) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem terminal_operands_not_retpc:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
  MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x
Proof
  strip_tac >> irule symControlTerminalWordStackOwnTheory.terminal_operands_not_retpc >>
  metis_tac[listTheory.MEM]
QED

Theorem terminal_arranged_word_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
  (mid.as_stack ++ rest = values ++
     DROP (LENGTH (compute_operands inst)) (mid.as_stack ++ rest)) /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >>
  `!x. MEM (Var x) (compute_operands inst) ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule frameViewFactsTheory.ordinary_operand_not_retpc >>
     conj_tac >- gvs[listTheory.MEM] >>
     qexists `inst` >> gvs[compute_operands_def, listTheory.MEM]) >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME values` by
    metis_tac[frameViewFactsTheory.eval_operands_frame_view, listTheory.MEM_REVERSE] >>
  `!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
    ?w. sv = Val w` by
    (rpt strip_tac >>
     `op <> dead_stack_marker` by
       (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        disch_then (qspec_then `op` mp_tac) >> simp[]) >>
     `MEM op inst.inst_operands /\ ~is_label_operand op /\
      inst.inst_opcode <> ASSIGN /\ inst.inst_opcode <> PHI /\
      inst.inst_opcode <> RET /\ inst.inst_opcode <> RETFMP /\
      inst.inst_opcode <> DRET /\ inst.inst_opcode <> CODECOPY` by
       (gvs[listTheory.MEM, compute_operands_def] >>
        gvs[label_positions_ok_def, listTheory.EVERY_MEM]) >>
     drule_all ordinary_noncopy_operand_word_kind >> simp[]) >>
  drule_all arranged_word_prepared_symbolic_stack >> strip_tac >>
  `LENGTH values = LENGTH (compute_operands inst)` by
    metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length,
              listTheory.LENGTH_REVERSE] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.as_stack` by
    metis_tac[listTheory.LENGTH_APPEND, arithmeticTheory.LE_ADD] >>
  `LENGTH (compute_operands inst) - LENGTH mid.as_stack = 0` by decide_tac >>
  simp[listTheory.DROP_APPEND] >>
  qpat_x_assum `mid.as_stack = values ++ _`
    (mp_tac o AP_TERM ``\xs:bytes32 list. xs ++ rest``) >>
  simp[listTheory.APPEND_ASSOC]
QED

Theorem sym_frame_terminal_prefix_setup_marked:
  !cp base.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ codegen_ready_fn fn /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss ==>
  ?n mid name ss_mid.
    asm_steps lo o2pc prog n st = AsmOK mid /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    venom_to_evm_name inst.inst_opcode = SOME name /\
    context_memory_rel cp vs.vs_memory mid.as_memory /\
    venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
    (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
      mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack /\
      ?suffix. ss_mid.sym_stack = MAP Val values ++ suffix) /\
    sym_steps prog env n ss = SymOK ss_mid /\
    asm_sym_rel prog env mid ss_mid /\
    (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `MEM r cplan.cp_regions` >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name /\
    inst.inst_outputs = [] /\ ~is_commutative inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term label ps =
      (ops,final)` by
    (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
        venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def,
        venomEffectsTheory.is_commutative_def, compute_operands_def]) >>
  drule_all fnFrameTerminalHaltTheory.output_free_regular_plan >> strip_tac >>
  `ssa_form fn /\ label_positions_ok inst` by
    metis_tac[stackPlanGenTheory.codegen_ready_fn_def,
              unitShapeDefsTheory.fn_shape_ok_def,
              unitShapeDefsTheory.inst_shape_ok_def, listTheory.EVERY_MEM] >>
  `PERM (compute_operands inst) (compute_operands inst) /\
   LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
   arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset` by gvs[] >>
  drule_all sym_frame_entry_selected_prefix_sim_marked >>
  strip_tac >>
  qexistsl [`LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))`,
    `mid with as_stack := mid.as_stack ++ rest`, `name`, `ss_mid`] >>
  simp[] >>
  `asm_block_at prog mid.as_pc [AsmOp name]` by
    gvs[stackOpSimTheory.execute_plan_append, stackOpSimTheory.asm_block_at_append,
        execute_plan_def, exec_stack_op_def] >>
  `asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
   sym_kinds_ok cplan fn ret srest arranged ss_mid /\
   (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cplan b)` by
    metis_tac[sym_frame_inv_def, sym_kinds_ok_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[] >> conj_tac
  >- (qpat_x_assum `venom_asm_rel _ _ _ mid` mp_tac >>
      simp[venom_asm_rel_def, frame_view_def]) >>
  gen_tac >> disch_tac >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
   MEM inst.inst_opcode
     [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
      INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL]` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all terminal_arranged_word_stack >> simp[]
QED

Theorem assert_selected_prefix_decompose:
  inst.inst_opcode = ASSERT /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symControlTerminalPrepareOwnTheory.assert_selected_prefix_decompose
QED

Theorem assert_unreachable_selected_prefix_decompose:
  inst.inst_opcode = ASSERT_UNREACHABLE /\ inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) ==>
  compute_operands inst = [cond] /\
  ?iops prepared rops arranged lbl.
    emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++ [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl] /\
    arranged.ps_alloc.sa_spill_base = final.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= final.ps_alloc.sa_next_offset
Proof
  MATCH_ACCEPT_TAC symControlTerminalPrepareOwnTheory.assert_unreachable_selected_prefix_decompose
QED

Theorem sym_conditional_abort_frame_prefix_deep:
  !base.
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst_wf inst /\ inst.inst_operands = [cond] /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  ?pre arranged mid ss_mid suffix.
    ops = pre ++ suffix /\
    ((inst.inst_opcode = ASSERT /\
      suffix = [SOEmit "ISZERO"; SOPushLabel "revert"; SOEmit "JUMPI"]) \/
     (inst.inst_opcode = ASSERT_UNREACHABLE /\ ?lbl.
      suffix = [SOPushLabel lbl; SOEmit "JUMPI"; SOEmit "INVALID"; SOLabel lbl])) /\
    arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc (execute_plan cplan.cp_initial_fmp suffix) /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  qx_gen_tac `spillbase` >> strip_tac >> gvs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`,
             `dfg` |-> `dfg_build_function fn`, `o2pc` |-> `build_offset_to_pc prog`]
      (SPEC_ALL (Q.SPEC `spillbase`
        symControlTerminalPrepareOwnTheory.sym_conditional_abort_frame_prefix_deep_mode_conditional)))) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem sym_regular_abort_frame_prefix_deep:
  !base.
  venom_to_evm_name inst.inst_opcode = SOME name /\
  inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st /\
  asm_block_at prog st.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  asm_static_wf prog /\ sym_frame_inv prog env ctx cplan fn ret srest labs0 ps st ss ==>
  ?pre arranged mid ss_mid.
    arranged.ps_stack = stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack ++
      compute_operands inst /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cplan.cp_initial_fmp pre)) st =
      AsmOK (mid with as_stack := mid.as_stack ++ rest) /\
    venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := st.as_memory) mid /\
    venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
    asm_block_at prog mid.as_pc [AsmOp name] /\
    sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp pre)) ss = SymOK ss_mid /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 arranged
      (mid with as_stack := mid.as_stack ++ rest) ss_mid
Proof
  qx_gen_tac `spillbase` >> strip_tac >> gvs[sym_frame_inv_def] >>
  `!n cs ss ss'. asm_sym_rel prog env cs ss /\ sym_steps prog env n ss = SymOK ss' ==>
    ?cs'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel prog env cs' ss'` by metis_tac[asm_sym_steps_lockstep] >>
  mp_tac (SRULE [asm_sym_rel_core_canonical, sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`,
             `dfg` |-> `dfg_build_function fn`, `o2pc` |-> `build_offset_to_pc prog`]
      (SPEC_ALL (Q.SPEC `spillbase`
        symControlTerminalPrepareOwnTheory.sym_regular_abort_frame_prefix_deep_mode_conditional)))) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem sym_rf_copy_preparation_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?mid ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp (ins ++ ros))) st = AsmOK mid /\
    mid.as_pc = st.as_pc + LENGTH (execute_plan fmp (ins ++ ros)) /\
    mid.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs) ps2.ps_stack stk' /\
    ps2.ps_stack = stack_pop 3 ps2.ps_stack ++ [zop;sop;dop] /\
    sym_steps prog env (LENGTH (execute_plan fmp (ins ++ ros))) ss = SymOK ss' /\
    asm_sym_rel prog env mid ss' /\ ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps2.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    asm_block_at prog mid.as_pc [AsmOp "RETURNDATACOPY"] /\
    ops = ins ++ ros ++ [SOEmit "RETURNDATACOPY"] /\
    ps' = release_dead_spills nl (ps2 with ps_stack := stack_pop 3 ps2.ps_stack)
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (DISCH_ALL (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`]
      (Q.SPECL [`F`, `asm_data_env_ok prog env`, `[]`]
        (UNDISCH sym_rf_copy_preparation_execution_mode_conditional))))) >>
  impl_tac
  >- (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
      FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
        MATCH_ACCEPT_TAC list_rel_op_kind_transport,
        MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
          (GEN_ALL sym_reorder_one_decompose)),
        MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
        MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
        MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
        MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
        MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  disch_then (qspec_then `cp0` mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  simp[]
QED

Theorem sym_rf_copy_operand_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  metis_tac[sym_rf_copy_operand_kind_mode,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_rf_copy_prepared_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_sym_rel prog env cs ss /\ cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;src;sz] ++ suffix
Proof
  strip_tac >> irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`] sym_rf_copy_prepared_stack_core)) >>
  metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_rf_copy_success_stack:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  cs.as_stack = dst :: src :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_step prog env (AsmOp "RETURNDATACOPY") ss = SymOK ss' /\
    asm_sym_rel prog env cs' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  qx_gen_tac `cp0` >> strip_tac >>
  mp_tac (PURE_REWRITE_RULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`] sym_rf_copy_success_stack_core)) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]) >> simp[]
QED

Theorem sym_rf_copy_prepared_success:
  !cp.
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel (SND (compute_label_offsets prog)) current
    (tail ++ [zop;sop;dop]) stk /\
  operand_val current (SND (compute_label_offsets prog)) dop = SOME dst /\
  operand_val current (SND (compute_label_offsets prog)) sop = SOME src /\
  operand_val current (SND (compute_label_offsets prog)) zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmOK cs' ==>
  ?ss' top'.
    sym_steps prog env 1 ss = SymOK ss' /\
    asm_sym_rel prog env cs' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE tail) top' /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss'.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  qx_gen_tac `cp0` >> strip_tac >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      sym_rf_copy_prepared_success_mode_core)) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]) >> simp[]
QED

Theorem sym_rf_copy_success_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  w2n src + w2n sz <= LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz))
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      (INST_TYPE [``:'cfg`` |-> ``:'a``]
        sym_rf_copy_success_execution_mode_conditional))) >>
  impl_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`]
       sym_rf_copy_preparation_execution)) >> simp[]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]) >> simp[]
QED

Theorem sym_rf_copy_fault_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  cs.as_stack = dst :: src :: sz :: rest /\ ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;sop;dop])) top /\
  asm_block_at prog cs.as_pc [AsmOp "RETURNDATACOPY"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "RETURNDATACOPY") cs = AsmFault cs' ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >> irule (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      sym_rf_copy_fault_stack_mode_core)) >>
  metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_rf_copy_fault_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  w2n src + w2n sz > LENGTH vs.vs_returndata /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan fmp ops)) ss)
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      (INST_TYPE [``:'cfg`` |-> ``:'a``]
        sym_rf_copy_fault_execution_mode_conditional))) >>
  impl_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`]
       sym_rf_copy_preparation_execution)) >> simp[]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]) >> simp[]
QED

Theorem sym_rf_entry_copy_execution:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ rf_spills_separated ps /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  emit_input_plan RETURNDATACOPY (compute_operands inst) nl ps = (ins,ps1) /\
  reorder_plan (dfg_build_function fn) (compute_operands inst) ps1 = (ros,ps2) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
    operand_val (frame_view fn ra vs) lo at =
    operand_val (frame_view fn ra vs) lo
      (normalize_operand (dfg_build_function fn) [] at)) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo sop = SOME src /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  vs' = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) vs.vs_returndata)) vs /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  if w2n src + w2n sz <= LENGTH vs.vs_returndata then
  (?out ss_out stk_out top_out.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK out /\
    out.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    out.as_stack = stk_out ++ rest /\
    plan_stack_rel lo (frame_view fn ra vs') ps'.ps_stack stk_out /\
    venom_asm_terminal_rel vs' out /\
    TAKE (w2n sz) (DROP (w2n dst) vs'.vs_memory) =
      TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss_out /\
    asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top_out /\
    (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
    ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)))
  else
  (?out. asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmFault out /\
    venom_asm_terminal_rel (halt_state (set_returndata [] vs)) out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan fmp ops)) ss))
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      (INST_TYPE [``:'cfg`` |-> ``:'a``]
        sym_rf_entry_copy_execution_mode_conditional))) >>
  impl_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`]
       sym_rf_copy_preparation_execution)) >> simp[]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]) >> simp[]
QED

Theorem sym_revert_operand_kind:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  MATCH_ACCEPT_TAC (SRULE [] (Q.INST [`allow_own` |-> `F`]
    symControlForwardRunOwnTheory.sym_revert_operand_kind_mode))
QED

Theorem sym_revert_prepared_stack:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  asm_sym_rel prog env cs ss /\ cs.as_stack = dst :: sz :: rest /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top ==>
  ?suffix. ss.sym_stack = MAP Val [dst;sz] ++ suffix
Proof
  MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      sym_revert_prepared_stack_core))
QED

Theorem sym_revert_prepared_terminal:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = REVERT /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  plan_stack_rel (SND (compute_label_offsets prog)) current (tail ++ [zop;dop]) stk /\
  operand_val current (SND (compute_label_offsets prog)) dop = SOME dst /\
  operand_val current (SND (compute_label_offsets prog)) zop = SOME sz /\
  cs.as_stack = stk ++ rest /\ asm_sym_rel prog env cs ss /\ asm_static_wf prog /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) /\
  asm_block_at prog cs.as_pc [AsmOp "REVERT"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "REVERT") cs = AsmRevert out ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >>
  irule (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical,
      GSYM asm_sym_step_rel_core_canonical]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`]
      sym_revert_prepared_terminal_mode_conditional)) >>
  simp[] >> conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `cs'.as_pc < LENGTH prog` by gvs[asm_block_at_def] >>
     drule_all asm_sym_step >>
     Cases_on `sym_step prog env (EL cs'.as_pc prog) ss'` >>
     gvs[asm_block_at_def, asm_sym_step_rel_def]) >>
  metis_tac[]
QED

Theorem sym_rf_suffix_revert_abort:
  !cp.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = REVERT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  rf_inventory_inv fn ra lo entry ps vs /\
  (!op. MEM op (compute_operands inst) ==>
    operand_val (frame_view fn ra vs) lo op =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] op)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  plan_stack_rel lo (frame_view fn ra vs) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel vs st /\
  TAKE (w2n sz) (DROP (w2n dst) vs.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  a = Revert_abort /\
  ?out. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
    AsmRevert out /\ venom_asm_terminal_rel vs' out /\
    sym_terminal (sym_steps prog env (LENGTH (execute_plan initial_fmp ops)) ss)
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical,
      GSYM asm_sym_step_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      (INST_TYPE [``:'cfg`` |-> ``:'a``] sym_rf_suffix_revert_abort_mode_conditional))) >>
  impl_tac >-
    (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
       MATCH_ACCEPT_TAC list_rel_op_kind_transport,
       MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
         (GEN_ALL sym_reorder_one_decompose)),
       MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
       MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
       MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
       MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
       MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> conj_tac >-
       (rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     rename1 `asm_sym_rel prog env cs0 ss0` >>
     `cs0.as_pc < LENGTH prog` by gvs[asm_block_at_def] >>
     drule_all asm_sym_step >>
     Cases_on `sym_step prog env (EL cs0.as_pc prog) ss0` >>
     gvs[asm_block_at_def, asm_sym_step_rel_def]) >> simp[]
QED

Theorem sym_plan_stack_rel_inst_idx:
  plan_stack_rel lo (frame_view fn ra (s with vs_inst_idx := k)) ops stk <=>
  plan_stack_rel lo (frame_view fn ra s) ops stk
Proof
  MATCH_ACCEPT_TAC symControlForwardRunOwnTheory.sym_plan_stack_rel_inst_idx
QED

Theorem sym_terminal_rel_inst_idx:
  venom_asm_terminal_rel (s with vs_inst_idx := k) st <=>
  venom_asm_terminal_rel s st
Proof
  MATCH_ACCEPT_TAC symControlForwardRunOwnTheory.sym_terminal_rel_inst_idx
QED

Theorem sym_assign_success_state:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ step_inst fuel ctx inst s = OK s' ==>
  ?w. s' = s with vs_vars := s.vs_vars |+ (out,w)
Proof
  MATCH_ACCEPT_TAC symControlForwardRunOwnTheory.sym_assign_success_state
QED

Theorem sym_assign_block_abort_continuation:
  s.vs_inst_idx = k /\ get_instruction bb k = SOME inst /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ exec_block fuel ctx bb s = Abort a s_end ==>
  ?s'. step_inst fuel ctx inst s = OK s' /\
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC k) = Abort a s_end
Proof
  MATCH_ACCEPT_TAC symControlForwardRunOwnTheory.sym_assign_block_abort_continuation
QED

Theorem sym_rf_future_non_phi:
  revert_forward_pair bb i j /\ i < k ==>
  !r ti. SUC k <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  MATCH_ACCEPT_TAC symControlForwardRunOwnTheory.sym_rf_future_non_phi
QED

Theorem sym_rf_assign_continuation_execution:
  !cp. lo = SND (compute_label_offsets prog) /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  rf_spills_separated ps /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [rhs] /\
  inst.inst_outputs = [out] /\ ~is_label_operand rhs /\
  (is_var_operand rhs ==> MEM rhs ps.ps_stack \/ rhs IN FDOM ps.ps_spilled) /\
  rf_inventory_inv fn ra lo entry ps s /\
  operand_val (frame_view fn ra s) lo rhs =
    operand_val entry lo (normalize_operand (dfg_build_function fn) [] rhs) /\
  step_inst fuel ctx inst s = OK s' /\
  generate_regular_inst_plan lv (dfg_build_function fn) cfg fn inst
    nl halting term lbl ps = (ops,ps') /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  asm_block_at prog st.as_pc (execute_plan fmp ops) /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) ==>
  ?st' ss' stk' top'.
    asm_steps lo (build_offset_to_pc prog) prog
      (LENGTH (execute_plan fmp ops)) st = AsmOK st' /\
    st'.as_pc = st.as_pc + LENGTH (execute_plan fmp ops) /\
    st'.as_stack = stk' ++ rest /\
    plan_stack_rel lo (frame_view fn ra (s' with vs_inst_idx := k)) ps'.ps_stack stk' /\
    st'.as_memory = st.as_memory /\ s'.vs_memory = s.vs_memory /\
    venom_asm_terminal_rel (s' with vs_inst_idx := k) st' /\
    sym_steps prog env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    asm_sym_rel prog env st' ss' /\
    ss'.sym_stack = top' ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top' /\
    (!b. FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      (INST_TYPE [``:'cfg`` |-> ``:'a``]
        sym_rf_assign_continuation_execution_mode_conditional))) >>
  impl_tac >-
    (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
       MATCH_ACCEPT_TAC list_rel_op_kind_transport,
       MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
         (GEN_ALL sym_reorder_one_decompose)),
       MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
       MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
       MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
       MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
       MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >> simp[]
QED

Theorem sym_rf_strict_suffix_abort:
  !k s st ps stk ops ps_end ss top.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i < k /\ k <= j /\ s.vs_inst_idx = k /\
  LENGTH (get_params bb.bb_instructions) <= k /\
  get_instruction bb i = SOME copy /\ copy.inst_operands = [cdop;csop;czop] /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] cdop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] czop) = SOME sz /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\ rf_value_inv fn ra bb j lo entry k s /\
  rf_inventory_inv fn ra lo entry ps s /\
  (!op. rf_live_use bb k j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  plan_stack_rel lo (frame_view fn ra s) ps.ps_stack stk /\
  st.as_stack = stk ++ rest /\ venom_asm_terminal_rel s st /\
  TAKE (w2n sz) (DROP (w2n dst) s.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) st.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (k - LENGTH (get_params bb.bb_instructions)) (DROP k bb.bb_instructions)
    ps = SOME (ops,ps_end) /\
  (!off. ~MEM (SOSpill off) ops /\ ~MEM (SORestore off) ops) /\
  asm_block_at prog st.as_pc (execute_plan initial_fmp ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ asm_sym_rel prog env st ss /\
  ss.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps.ps_stack) top /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b) /\
  ~mem_labels_hit ss.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  exec_block fuel ctx bb s = Abort a s_end ==>
  a = Revert_abort /\
  ?n out. asm_steps lo o2pc prog n st = AsmRevert out /\
    venom_asm_terminal_rel s_end out /\ sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical,
      GSYM asm_sym_step_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      sym_rf_strict_suffix_abort_mode_conditional)) >>
  impl_tac >-
    (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
       MATCH_ACCEPT_TAC list_rel_op_kind_transport,
       MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
         (GEN_ALL sym_reorder_one_decompose)),
       MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
       MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
       MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
       MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
       MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  disch_then (mp_tac o SPEC_ALL) >> impl_tac >-
    (simp[] >> conj_tac >-
       (rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     rename1 `asm_sym_rel prog env cs0 ss0` >>
     `cs0.as_pc < LENGTH prog` by gvs[asm_block_at_def] >>
     drule_all asm_sym_step >>
     Cases_on `sym_step prog env (EL cs0.as_pc prog) ss0` >>
     gvs[asm_block_at_def, asm_sym_step_rel_def]) >> simp[]
QED

Theorem sym_rf_current_normalized_value:
  rf_value_inv fn ra bb j lo entry k s /\
  get_instruction bb k = SOME inst /\ k <= j /\
  MEM op (compute_operands inst) /\
  operand_val (frame_view fn ra s) lo op = value ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] op) = value
Proof
  MATCH_ACCEPT_TAC symControlForwardSourceFactsTheory.sym_rf_current_normalized_value
QED

Theorem sym_rf_copy_normalized_range:
  rf_value_inv fn ra bb j lo entry i s /\
  get_instruction bb i = SOME inst /\ i <= j /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [dop;sop;zop] /\
  operand_val (frame_view fn ra s) lo dop = SOME dst /\
  operand_val (frame_view fn ra s) lo zop = SOME sz ==>
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] dop) = SOME dst /\
  operand_val entry lo (normalize_operand (dfg_build_function fn) [] zop) = SOME sz
Proof
  MATCH_ACCEPT_TAC symControlForwardSourceFactsTheory.sym_rf_copy_normalized_range
QED

Theorem sym_rf_abort_source_fault:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault ==>
  a = ExHalt_abort /\ vs_end = fault
Proof
  MATCH_ACCEPT_TAC symControlForwardSourceFactsTheory.sym_rf_abort_source_fault
QED

Theorem sym_rf_abort_source_success:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = OK copied ==>
  exec_block fuel ctx bb (copied with vs_inst_idx := SUC i) = Abort a vs_end
Proof
  MATCH_ACCEPT_TAC symControlForwardSourceFactsTheory.sym_rf_abort_source_success
QED

Theorem sym_rf_revert_runs_compose:
  asm_steps lo o2pc prog n1 ast = AsmOK mid /\
  asm_steps lo o2pc prog n2 mid = AsmRevert out /\
  sym_steps prog env n1 ss = SymOK ss_mid /\
  sym_terminal (sym_steps prog env n2 ss_mid) ==>
  asm_steps lo o2pc prog (n1 + n2) ast = AsmRevert out /\
  sym_terminal (sym_steps prog env (n1 + n2) ss)
Proof
  MATCH_ACCEPT_TAC (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
    symControlForwardSourceFactsTheory.sym_rf_revert_runs_compose_mode))
QED

Theorem sym_rf_entry_fault_terminal:
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i <= j /\
  get_instruction bb i = SOME inst /\ exec_block fuel ctx bb vs = Abort a vs_end /\
  step_inst fuel ctx inst vs = Abort ExHalt_abort fault /\
  asm_steps lo o2pc prog n ast = AsmFault out /\
  venom_asm_terminal_rel fault out /\ sym_terminal (sym_steps prog env n ss) ==>
  ?m ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog m ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog m ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\ sym_terminal (sym_steps prog env m ss)
Proof
  MATCH_ACCEPT_TAC (SRULE [sym_steps_mode_def] (Q.INST [`allow_own` |-> `F`]
    symControlForwardSourceFactsTheory.sym_rf_entry_fault_terminal_mode))
QED

Theorem sym_rf_entry_future_non_phi:
  revert_forward_pair bb i j ==>
  !r ti. SUC i <= r /\ r <= j /\ get_instruction bb r = SOME ti ==>
    ti.inst_opcode <> PHI
Proof
  MATCH_ACCEPT_TAC symControlForwardSourceFactsTheory.sym_rf_entry_future_non_phi
QED

Theorem sym_rf_entry_success_terminal:
  !cp.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\ i < j /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  get_instruction bb i = SOME inst /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_outputs = [] /\
  inst.inst_operands = [dop;sop;zop] /\
  EVERY (\ti. EVERY (\op. ~is_label_operand op) ti.inst_operands)
    (DROP i bb.bb_instructions) /\
  rf_spills_separated ps /\
  rf_value_inv fn ra bb j lo (frame_view fn ra vs) i vs /\
  rf_inventory_inv fn ra lo (frame_view fn ra vs) ps vs /\
  (!op. rf_live_use bb i j op /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_regular_inst_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn inst (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
    halting term bb.bb_label ps = (step_ops,ps1) /\
  (!off. ~MEM (SOSpill off) step_ops /\ ~MEM (SORestore off) step_ops) /\
  operand_val (frame_view fn ra vs) lo dop = SOME dst /\
  operand_val (frame_view fn ra vs) lo zop = SOME sz /\
  step_inst fuel ctx inst vs = OK copied /\
  exec_block fuel ctx bb vs = Abort a vs_end /\
  asm_steps lo (build_offset_to_pc prog) prog
    (LENGTH (execute_plan fmp step_ops)) ast = AsmOK out /\
  out.as_pc = ast.as_pc + LENGTH (execute_plan fmp step_ops) /\
  out.as_stack = stk_out ++ rest /\
  plan_stack_rel lo (frame_view fn ra copied) ps1.ps_stack stk_out /\
  venom_asm_terminal_rel copied out /\
  TAKE (w2n sz) (DROP (w2n dst) copied.vs_memory) =
    TAKE (w2n sz) (DROP (w2n dst) out.as_memory) /\
  generate_block_insts_plan (liveness_analyze fn) (dfg_build_function fn)
    (cfg_analyze fn) fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (SUC i - LENGTH (get_params bb.bb_instructions)) (DROP (SUC i) bb.bb_instructions)
    ps1 = SOME (rest_ops,ps_end) /\
  (!off. ~MEM (SOSpill off) rest_ops /\ ~MEM (SORestore off) rest_ops) /\
  asm_block_at prog (ast.as_pc + LENGTH (execute_plan fmp step_ops))
    (execute_plan fmp rest_ops) /\
  MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\
  sym_steps prog env (LENGTH (execute_plan fmp step_ops)) ss = SymOK ss_out /\
  asm_sym_rel prog env out ss_out /\ ss_out.sym_stack = top_out ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps1.ps_stack) top_out /\
  (!b. b IN FDOM ss_out.sym_mem_labels ==> context_spill_byte cp b) /\
  ~mem_labels_hit ss_out.sym_mem_labels (in_mem_range (w2n dst) (w2n sz)) ==>
  ?n ast_end.
    ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
    venom_asm_terminal_rel vs_end ast_end /\ sym_terminal (sym_steps prog env n ss)
Proof
  qx_gen_tac `cp0` >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical,
      GSYM asm_sym_step_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      sym_rf_entry_success_terminal_mode_conditional)) >>
  impl_tac >-
    (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
       MATCH_ACCEPT_TAC list_rel_op_kind_transport,
       MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
         (GEN_ALL sym_reorder_one_decompose)),
       MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
       MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
       MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
       MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
       MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  disch_then (qspec_then `cp0` mp_tac) >> impl_tac >-
    (simp[] >> conj_tac >-
       (rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     rename1 `asm_sym_rel prog env cs0 ss0` >>
     `cs0.as_pc < LENGTH prog` by gvs[asm_block_at_def] >>
     drule_all asm_sym_step >>
     Cases_on `sym_step prog env (EL cs0.as_pc prog) ss0` >>
     gvs[asm_block_at_def, asm_sym_step_rel_def]) >> simp[]
QED

Theorem sym_rf_entry_forward_abort:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j ps vs ast ops
   ps_end ra rest mem0 a vs_end env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\ rf_spills_separated ps /\
    (!k inst op. i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\ label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps ast ss /\
    exec_block fuel ctx bb vs = Abort a vs_end ==>
    ?n ast_end.
      ((a = Revert_abort /\ asm_steps lo o2pc prog n ast = AsmRevert ast_end) \/
       (a = ExHalt_abort /\ asm_steps lo o2pc prog n ast = AsmFault ast_end)) /\
      venom_asm_terminal_rel vs_end ast_end /\
      sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  mp_tac (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES, asm_sym_rel_core_canonical,
      GSYM asm_sym_step_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `allow_own` |-> `F`]
      sym_rf_entry_forward_abort_mode_conditional)) >>
  impl_tac >-
    (pure_rewrite_tac[GSYM control_reorder_place_def] >> rpt conj_tac >>
     FIRST [MATCH_ACCEPT_TAC emit_input_plan_spill_free_stack_replay,
       MATCH_ACCEPT_TAC list_rel_op_kind_transport,
       MATCH_ACCEPT_TAC (PURE_REWRITE_RULE [GSYM control_reorder_place_def]
         (GEN_ALL sym_reorder_one_decompose)),
       MATCH_ACCEPT_TAC control_reorder_place_spill_free_kind_replay,
       MATCH_ACCEPT_TAC reorder_restore_no_restore_identity,
       MATCH_ACCEPT_TAC reorder_reduce_no_spill_identity,
       MATCH_ACCEPT_TAC do_swap_no_restore_shallow,
       MATCH_ACCEPT_TAC do_swap_shallow_symbolic_prefix_facts]) >>
  impl_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`]
       sym_rf_copy_preparation_execution)) >> simp[]) >>
  disch_then irule >> simp[] >> conj_tac >-
    (rpt gen_tac >> strip_tac >> rename1 `asm_sym_rel prog env cs0 ss0` >>
     `cs0.as_pc < LENGTH prog` by gvs[asm_block_at_def] >>
     drule_all asm_sym_step >>
     Cases_on `sym_step prog env (EL cs0.as_pc prog) ss0` >>
     gvs[asm_block_at_def, asm_sym_step_rel_def]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  gvs[sym_frame_inv_def, sym_kinds_ok_def] >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `run_block_non_phis _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl [`top`, `srest`, `ret`, `j`] >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem sym_jmp_suffix_frame_sim:
  !p env ctx cp fn ret srest labs0 ps cs ss l pc.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc [AsmPushLabel l; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab l 0) = SOME pc ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 2 cs = AsmOK cs' /\
    sym_steps p env 2 ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps cs' ss' /\
    cs'.as_pc = pc
Proof
  rpt gen_tac >> strip_tac >>
  irule (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES,
      asm_sym_rel_core_canonical, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      sym_jmp_suffix_frame_sim_mode_conditional)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  (metis_tac[asm_sym_steps_lockstep])
QED

Theorem sym_jmp_plan_decompose:
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label target] /\
  inst.inst_outputs = [] /\
  lookup_block target fn.fn_blocks = SOME target_bb /\
  targets = MAP Var (input_vars_from lbl target_bb.bb_instructions
                       (live_vars_at lv target 0)) /\
  generate_inst_plan lv dfg cfg fn inst nl ih nit lbl ps = SOME (ops, qs) ==>
  ?rops prepared sops arranged.
    restore_spilled_plan targets ps = (rops, prepared) /\
    reorder_plan dfg targets prepared = (sops, arranged) /\
    ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
    qs = release_dead_spills nl arranged
Proof
  MATCH_ACCEPT_TAC symControlJumpOwnTheory.sym_jmp_plan_decompose
QED

Theorem sym_jmp_plan_frame_sim:
  !base.
  generated_plan_state_wf_marked base ps /\
  pending_inventory_wf pending ps /\
  restore_spilled_plan pending ps = (rops, prepared) /\
  reorder_plan dfg pending prepared = (sops, arranged) /\
  ops = rops ++ sops ++ [SOPushLabel target; SOEmit "JUMP"] /\
  qs = release_dead_spills nl arranged /\
  (!off. MEM (SORestore off) rops ==> off < dimword(:256)) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) pending /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\ MEM (AsmLabel target) p /\
  FLOOKUP (SND (compute_label_offsets p)) target = SOME off /\
  FLOOKUP (build_offset_to_pc p) off = SOME pc /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?ac sy.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK ac /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK sy /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 qs ac sy /\
    ac.as_pc = pc
Proof
  qx_gen_tac `spillbase` >> strip_tac >>
  irule (PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES,
      asm_sym_rel_core_canonical, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      sym_jmp_plan_frame_sim_mode_conditional)) >>
  simp[] >> conj_tac >- metis_tac[sym_code_label_dest] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  qexistsl [`arranged`, `spillbase`, `nl`, `pending`, `prepared`, `ps`, `r`, `rops`, `sops`] >>
  simp[] >> conj_tac >-
    (rpt gen_tac >> strip_tac >>
     drule_all (SRULE [] (Q.INST [`dfg` |-> `dfg_build_function fn`]
       sym_jmp_prepare_frame_sim)) >> simp[]) >>
  gvs[]
QED

Theorem sym_jmp_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   target target_bb target_stack off pc_t
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label target] /\
    inst.inst_outputs = [] /\
    lookup_block target fn.fn_blocks = SOME target_bb /\
    target_stack =
      MAP Var (input_vars_from bb_label target_bb.bb_instructions
                 (live_vars_at liveness target 0)) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    (!off. MEM (SORestore off) (FST (restore_spilled_plan target_stack ps)) ==>
           off < dimword(:256)) /\
    LENGTH target_stack <=
      LENGTH (SND (restore_spilled_plan target_stack ps)).ps_stack /\
    pending_inventory_wf target_stack ps /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      target_stack /\
    (!op at. MEM op target_stack /\
       (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg op at ==>
       operand_val (frame_view fn ra vs) lo op =
       operand_val (frame_view fn ra vs) lo at) /\
    FLOOKUP lo target = SOME off /\ off < dimword (:256) /\
    FLOOKUP o2pc off = SOME pc_t /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA: planner-equivalent operands have the same kind. *)
    codegen_ready_fn fn /\
    MEM (AsmLabel target) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = pc_t /\
        vs' = jump_to target vs /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  irule
    (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
       boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`, `p` |-> `prog`]
      (SPEC_ALL sym_jmp_frame_sim_deep_mode_conditional))) >>
  conj_tac >- metis_tac[sym_code_label_dest] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  simp[] >>
  first_assum (irule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `MEM _ _.cp_regions`)) >>
  first_assum (irule_at (Pat `step_inst _ _ _ _ = _`)) >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >> irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] sym_jmp_prepare_frame_sim) >>
  first_assum (irule_at (Pat `restore_spilled_plan _ _ = _`)) >>
  first_assum (irule_at (Pat `reorder_plan _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `MEM _ _.cp_regions`)) >> simp[]
QED

Theorem sym_jnz_arranged_word:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label ln; Label lz] /\
  ~is_label_operand cond /\ cond <> dead_stack_marker /\
  venom_asm_rel lo ps v mid /\ ps.ps_stack = tail ++ [cond] /\
  operand_val v lo cond = SOME w /\
  asm_sym_rel p env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  ?stk. ss.sym_stack = Val w :: stk
Proof
  strip_tac >>
  `eval_operand cond v = SOME w` by metis_tac[emitSimTheory.operand_val_eq_eval] >>
  `!op sv. MEM op [cond] /\ op_kind_ok fn ret op sv ==> ?u. sv = Val u` by
    (simp[] >> rpt strip_tac >> drule_all sym_jnz_condition_kind >> simp[]) >>
  mp_tac (Q.INST [`operands` |-> `[cond]`, `values` |-> `[w]`, `vs` |-> `v`]
    (SPEC_ALL arranged_word_prepared_symbolic_stack)) >>
  simp[eval_operands_def, GSYM emitSimTheory.operand_val_eq_eval] >>
  disch_then drule_all >> simp[]
QED

Theorem sym_jnz_suffix_steps:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  ss.sym_stack = Val w :: stk /\
  sym_jump_dest p (Lab ln 0) = SOME pn /\
  sym_jump_dest p (Lab lz 0) = SOME pz ==>
  sym_steps p env (if w = 0w then 4 else 2) ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc :=
      (if w = 0w then pz else pn); sym_stack := stk|>)
Proof
  metis_tac[sym_jnz_suffix_steps_mode, sym_steps_mode_def]
QED

Theorem sym_jnz_suffix_frame_sim:
  !p env ctx cp fn ret srest labs0 ps cs ss tail cond w stk ln lz pn pz.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  ps.ps_stack = tail ++ [cond] /\ ss.sym_stack = Val w :: stk /\
  asm_block_at p cs.as_pc
    [AsmPushLabel ln; AsmOp "JUMPI"; AsmPushLabel lz; AsmOp "JUMP"] /\
  sym_jump_dest p (Lab ln 0) = SOME pn /\
  sym_jump_dest p (Lab lz 0) = SOME pz ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (if w = 0w then 4 else 2) cs = AsmOK cs' /\
    sym_steps p env (if w = 0w then 4 else 2) ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0
      (ps with ps_stack := tail) cs' ss' /\
    cs'.as_pc = (if w = 0w then pz else pn)
Proof
  rpt gen_tac >> strip_tac >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_jnz_suffix_frame_sim_mode_conditional))) >>
  simp[] >> metis_tac[asm_sym_steps_lockstep]
QED

Theorem sym_jnz_prepare_frame_sim:
  !base.
  generated_plan_state_wf_marked base ps /\
  emit_input_plan JNZ [cond] nl ps = (iops, prepared) /\
  reorder_plan dfg [cond] prepared = (rops, arranged) /\
  ops = iops ++ rops ++ suffix /\
  (is_var_operand cond ==> IS_SOME (stack_get_depth cond ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond)) /\
  1 <= LENGTH prepared.ps_stack /\
  cond <> dead_stack_marker /\
  (!at. operand_equiv dfg cond at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg cond at ==>
    operand_val (frame_view fn ra vs) lo cond =
    operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label ln; Label lz] /\ ~is_label_operand cond /\
  operand_val (frame_view fn ra vs) lo cond = SOME w /\
  asm_static_wf p /\ sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss ==>
  arranged.ps_stack = stack_pop 1 arranged.ps_stack ++ [cond] /\
  ?mid sy stk.
    asm_steps lo o2pc p (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
    sym_steps p env (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops))) ss = SymOK sy /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 arranged mid sy /\
    mid.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) /\
    sy.sym_stack = Val w :: stk
Proof
  gen_tac >> strip_tac >> gvs[] >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        (SPEC_ALL sym_jnz_prepare_frame_sim_mode_conditional)))) >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  first_assum (irule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `reorder_plan _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `MEM _ _.cp_regions`)) >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `MEM _ (fn_insts _)`)) >>
  qexists `suffix` >> simp[] >> metis_tac[]
QED

Theorem sym_jnz_plan_frame_sim:
  !base.
  generated_plan_state_wf_marked base ps /\
  emit_input_plan JNZ [cond] nl ps = (iops, prepared) /\
  reorder_plan dfg [cond] prepared = (rops, arranged) /\
  ops = iops ++ rops ++ [SOPushLabel ln; SOEmit "JUMPI"; SOPushLabel lz; SOEmit "JUMP"] /\
  final = release_dead_spills nl (arranged with ps_stack := stack_pop 1 arranged.ps_stack) /\
  (is_var_operand cond ==> IS_SOME (stack_get_depth cond ps.ps_stack) \/
    IS_SOME (FLOOKUP ps.ps_spilled cond)) /\
  1 <= LENGTH prepared.ps_stack /\ cond <> dead_stack_marker /\
  (!at. operand_equiv dfg cond at ==> at <> dead_stack_marker) /\
  (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
    operand_equiv dfg cond at ==>
    operand_val (frame_view fn ra vs) lo cond =
    operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs cs /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  fn_shape_ok fn /\ label_flow_ok ctx /\ inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label ln; Label lz] /\ ~is_label_operand cond /\
  operand_val (frame_view fn ra vs) lo cond = SOME w /\
  MEM (AsmLabel ln) p /\ MEM (AsmLabel lz) p /\
  FLOOKUP lo ln = SOME offn /\ FLOOKUP o2pc offn = SOME pn /\
  FLOOKUP lo lz = SOME offz /\ FLOOKUP o2pc offz = SOME pz /\
  asm_static_wf p /\ sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss ==>
  ?ac sy.
    asm_steps lo o2pc p
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
        (if w = 0w then 4 else 2)) cs = AsmOK ac /\
    sym_steps p env
      (LENGTH (execute_plan cplan.cp_initial_fmp (iops ++ rops)) +
        (if w = 0w then 4 else 2)) ss = SymOK sy /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 final ac sy /\
    ac.as_pc = (if w = 0w then pz else pn)
Proof
  gen_tac >> strip_tac >> gvs[] >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
      (SPEC_ALL sym_jnz_plan_frame_sim_mode_conditional))) >>
  conj_tac >- metis_tac[sym_code_label_dest] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  first_assum (irule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `reorder_plan _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `MEM _ _.cp_regions`)) >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >> metis_tac[]
QED

Theorem sym_jnz_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   cond_op if_nz if_z off_nz off_z pc_nz pc_z
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [cond_op; Label if_nz; Label if_z] /\
    (* The planner drops label operands of jumps, so a label condition would
       emit nothing; label_positions_ok excludes it. *)
    ~is_label_operand cond_op /\
    inst.inst_outputs = [] /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    1 <= LENGTH (SND (emit_input_plan JNZ [cond_op] next_liveness ps)).ps_stack /\
    (is_var_operand cond_op ==>
      IS_SOME (stack_get_depth cond_op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled cond_op)) /\
    eval_operand cond_op vs = operand_val (frame_view fn ra vs) lo cond_op /\
    (!at. (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled) /\
       operand_equiv dfg cond_op at ==>
       operand_val (frame_view fn ra vs) lo cond_op =
       operand_val (frame_view fn ra vs) lo at) /\
    cond_op <> dead_stack_marker /\
    (!at. operand_equiv dfg cond_op at ==> at <> dead_stack_marker) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    FLOOKUP lo if_nz = SOME off_nz /\ off_nz < dimword (:256) /\
    FLOOKUP o2pc off_nz = SOME pc_nz /\
    FLOOKUP lo if_z = SOME off_z /\ off_z < dimword (:256) /\
    FLOOKUP o2pc off_z = SOME pc_z /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst next_liveness is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (* SSA, and the shape facts that keep labels out of the condition. *)
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
    MEM (AsmLabel if_nz) prog /\ MEM (AsmLabel if_z) prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        ((vs' = jump_to if_nz vs /\ as'.as_pc = pc_nz) \/
         (vs' = jump_to if_z vs /\ as'.as_pc = pc_z)) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  irule
    (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
       boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`, `p` |-> `prog`]
      (SPEC_ALL sym_jnz_frame_sim_deep_mode_conditional))) >>
  conj_tac >- metis_tac[sym_code_label_dest] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >> simp[] >>
  first_assum (irule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `MEM _ _.cp_regions`)) >>
  first_assum (irule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[] >> metis_tac[]
QED

Theorem ret_label_concrete_head:
  asm_sym_rel p env cs ss /\ cs.as_stack = ra :: tail /\
  ss.sym_stack = Lab ret 0 :: stail ==>
  sval_conc (SND (compute_label_offsets p)) (Lab ret 0) = SOME ra
Proof
  strip_tac >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical]
    (Q.INST [`lo` |-> `SND (compute_label_offsets p)`,
      `code_ok` |-> `asm_data_env_ok p env`]
      (SPEC_ALL symControlRetOwnTheory.ret_label_concrete_head_core))) >>
  metis_tac[]
QED

Theorem ret_label_jump_destination:
  asm_static_wf p /\ MEM (AsmLabel ret) p /\
  sval_conc (SND (compute_label_offsets p)) (Lab ret 0) = SOME ra /\
  FLOOKUP (build_offset_to_pc p) (w2n ra) = SOME pc ==>
  sym_jump_dest p (Lab ret 0) = SOME pc
Proof
  metis_tac[symControlRetOwnTheory.ret_label_jump_destination_reloc,
    fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl]
QED

Theorem ret_preparation_arranged_stack:
  !base ps inputs nl iops prepared rops arranged final dfg.
  generated_plan_state_wf_marked base ps /\ LENGTH inputs <= 16 /\
  LENGTH inputs <= LENGTH prepared.ps_stack /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan RET inputs nl ps = (iops,prepared) /\
  reorder_plan dfg inputs prepared = (rops,arranged) /\
  final.ps_stack = stack_pop (LENGTH inputs) arranged.ps_stack /\
  final.ps_stack = [] ==> arranged.ps_stack = inputs
Proof
  metis_tac[symControlRetOwnTheory.ret_preparation_arranged_stack]
QED

Theorem sym_ret_ready_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
   base ps vs cs ops final ra rest mem0 pc_ret env ret srest labs0 ss rv vs'.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs cs /\
  (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  final.ps_stack = [] /\ asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = IntRet rv vs' ==>
  ?mid smid arranged.
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops) - 1) cs = AsmOK mid /\
    sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp ops) - 1) ss = SymOK smid /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 arranged mid smid /\
    asm_block_at prog mid.as_pc [AsmOp "JUMP"] /\
    smid.sym_stack = Lab ret 0 :: MAP Val (REVERSE rv.iret_values) ++ srest /\
    sym_jump_dest prog (Lab ret 0) = SOME pc_ret /\
    0 < LENGTH (execute_plan cp.cp_initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, listTheory.APPEND, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL sym_ret_ready_frame_sim_mode_conditional))) >>
  simp[fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        sym_read_only_selected_prefix_frame_sim) >> simp[] >> metis_tac[]) >>
  first_assum (irule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[] >> metis_tac[]
QED

Theorem sym_ret_symbolic_exact:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst nl halting term label
   base ps vs cs ops final ra rest mem0 pc_ret env ret srest labs0 ss rv vs' final_cs.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  inst.inst_opcode = RET /\ MEM inst (fn_insts (reachable_fn fn)) /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\ inst_wf inst /\
  generated_plan_state_wf_marked base ps /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs cs /\
  (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  final.ps_stack = [] /\ asm_block_at prog cs.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss /\
  step_inst fuel ctx inst vs = IntRet rv vs' /\
  asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp ops)) cs = AsmOK final_cs ==>
  ?ss'. sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp ops)) ss = SymOK ss' /\
    asm_sym_rel prog env final_cs ss' /\
    ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
    (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
    (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL sym_ret_symbolic_exact_mode_conditional))) >>
  simp[fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        sym_read_only_selected_prefix_frame_sim) >> simp[] >> metis_tac[]) >>
  first_assum (irule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[] >> metis_tac[]
QED

Theorem sym_ret_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf_marked base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    ps'.ps_stack = [] /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !rv vs'. step_inst fuel ctx inst vs = IntRet rv vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        as'.as_pc = pc_ret /\
        as'.as_stack = REVERSE rv.iret_values ++ rest /\
        context_memory_rel cp vs'.vs_memory as'.as_memory /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             read_byte b as'.as_memory = read_byte b mem0) /\
        shared_state_rel vs' as' /\
        sym_steps prog env n ss = SymOK ss' /\
        asm_sym_rel prog env as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac fnFrameDeepRetTheory.gen_ret_frame_sim_deep_exact >>
  gvs[] >>
  irule (PURE_REWRITE_RULE [asm_sym_rel_core_canonical, sym_steps_mode_def,
    boolTheory.COND_CLAUSES, GSYM sym_frame_inv_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
      `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL sym_ret_frame_sim_deep_mode_conditional))) >>
  simp[fnPlanPlaceRevertPostambleTheory.code_labels_agree_refl] >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM]
        sym_read_only_selected_prefix_frame_sim) >> simp[] >> metis_tac[]) >>
  first_assum (irule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  first_assum (irule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `step_inst _ _ _ _ = _`)) >> simp[] >>
  first_assum (irule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  metis_tac[]
QED

Theorem terminal_return_prepared_step:
  !cp.
  inst.inst_opcode = RETURN /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  context_memory_rel cp vs.vs_memory mid.as_memory /\
  source_memory_reads_disjoint cp inst vs /\
  venom_asm_terminal_rel vs mid /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >> strip_tac >>
  `inst.inst_operands = [off_op; sz_op]` by metis_tac[] >>
  `name = "RETURN" /\ mid.as_stack = off :: sz :: DROP 2 mid.as_stack` by
    gvs[asmIRTheory.venom_to_evm_name_def, compute_operands_def,
        python_stack_operands_def, ir_specific_operand_order_def, eval_operands_def] >>
  `MEM (w2n off, w2n sz) (source_memory_read_ranges inst vs)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  drule_all fnFrameTerminalPrepTheory.context_source_payload_agree >> disch_tac >>
  metis_tac[fnFrameTerminalHaltTheory.terminal_return_payload_step]
QED

Theorem terminal_selfdestruct_prepared_step:
  inst.inst_opcode = SELFDESTRUCT /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >> strip_tac
  >~ [`eval_operands _ _ = NONE`] >- gvs[eval_operands_def] >>
  `name = "SELFDESTRUCT" /\ mid.as_stack = addr :: DROP 1 mid.as_stack` by
    gvs[asmIRTheory.venom_to_evm_name_def, compute_operands_def,
        python_stack_operands_def, ir_specific_operand_order_def, eval_operands_def] >>
  qpat_x_assum `name = _` SUBST_ALL_TAC >>
  metis_tac[SIMP_RULE bool_ss [COND_RATOR, combinTheory.I_THM]
              fnFrameTerminalHaltTheory.terminal_selfdestruct_rel_step]
QED

Theorem terminal_halt_prepared_step:
  !cp.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
   inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  context_memory_rel cp vs.vs_memory mid.as_memory /\
  source_memory_reads_disjoint cp inst vs /\
  venom_asm_terminal_rel vs mid /\ mid.as_call_ctx = vs.vs_call_ctx /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    mid.as_stack = values ++ DROP (LENGTH (compute_operands inst)) mid.as_stack) /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?out. asm_steps lo o2pc prog 1 mid = AsmHalt out /\
    venom_asm_terminal_rel vs' out
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _ \/ _` strip_assume_tac
  >- (gvs[Once step_inst_def, step_inst_base_def, asmIRTheory.venom_to_evm_name_def] >>
      metis_tac[genBlockSimTheory.terminal_stop_step])
  >- metis_tac[terminal_return_prepared_step]
  >> metis_tac[terminal_selfdestruct_prepared_step]
QED

Theorem terminal_halt_operand_values:
  (inst.inst_opcode = RETURN \/ inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?args. eval_operands inst.inst_operands vs = SOME args /\
    eval_operands (REVERSE (compute_operands inst)) vs = SOME args /\
    LENGTH args = asm_op_arity name
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  fs[venomWfTheory.inst_wf_def, asmIRTheory.venom_to_evm_name_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute, compute_operands_def,
      python_stack_operands_def, ir_specific_operand_order_def] >>
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  (simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, AllCaseEqs(), eval_operands_def,
       asm_op_arity_def, asm_op_arity_table_def]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem sym_stop_prepared_terminal:
  asm_static_wf prog /\ asm_sym_rel prog env mid ss /\
  asm_block_at prog mid.as_pc [AsmOp "STOP"] /\
  asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp "STOP") mid = AsmHalt out ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >> irule sym_terminal_opcode_transfer >> conj_tac >- simp[] >>
  qexistsl [`[]`, `AsmHalt out`, `mid`, `"STOP"`, `ss.sym_stack`] >>
  simp[asm_op_arity_def, asm_op_arity_table_def,
       asm_op_mem_reads_def, log_table_def, mem_labels_hit_def]
QED

Theorem sym_halt_prepared_step:
  !cp.
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
   inst.inst_opcode = SELFDESTRUCT) /\ inst_wf inst /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_static_wf prog /\ asm_sym_rel prog env mid ss_mid /\
  asm_block_at prog mid.as_pc [AsmOp name] /\
  (!values. eval_operands (REVERSE (compute_operands inst)) vs = SOME values ==>
    ?suffix. ss_mid.sym_stack = MAP Val values ++ suffix) /\
  (!b. b IN FDOM ss_mid.sym_mem_labels ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  step_inst fuel ctx inst vs = Halt vs' /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog 1 mid = AsmHalt out ==>
  sym_terminal (sym_steps prog env 1 ss_mid)
Proof
  qx_gen_tac `cplan` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    (AsmOp name) mid = AsmHalt out` by
    (qpat_x_assum `asm_steps _ _ _ 1 _ = _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.ONE, asm_steps_def] >>
     gvs[asm_block_at_def, AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = STOP`
  >- (gvs[asmIRTheory.venom_to_evm_name_def] >>
      metis_tac[sym_stop_prepared_terminal]) >>
  drule_at (Pat `step_inst _ _ _ _ = Halt _`) terminal_halt_operand_values >>
  disch_then (qspec_then `name` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
    CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL]` by
    (simp[] >> metis_tac[]) >>
  `context_source_memory_writes_disjoint cplan inst vs` by
    (gvs[context_source_memory_writes_disjoint_def, source_memory_write_ranges_def]) >>
  drule_all terminal_source_memory_reads_safe >> disch_tac >>
  `MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
    "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"]` by
    gvs[asmIRTheory.venom_to_evm_name_def] >>
  metis_tac[sym_terminal_opcode_transfer]
QED

Theorem sym_halt_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >> gvs[sym_frame_inv_def] >>
  gen_tac >> strip_tac >>
  irule (SRULE [asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlHaltOwnTheory.sym_halt_frame_sim_deep_mode_kernel))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs.as_pc < LENGTH prog /\ EL cs.as_pc prog = ai` by
        gvs[asm_block_at_def] >>
      drule_all asm_sym_step >> simp[]) >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem regular_abort_operand_order:
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  inst_wf inst ==>
  compute_operands inst = REVERSE inst.inst_operands
Proof
  ACCEPT_TAC symControlAbortRegularOwnTheory.regular_abort_operand_order
QED

Theorem regular_abort_source_arguments:
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  inst_wf inst /\ inst.inst_opcode <> INVALID /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?args. eval_operands inst.inst_operands vs = SOME args
Proof
  ACCEPT_TAC symControlAbortRegularOwnTheory.regular_abort_source_arguments
QED

Theorem regular_abort_prepared_step:
  MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  inst_wf inst /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  cs.as_stack = args ++ tail /\ cs.as_call_ctx = vs.vs_call_ctx /\
  cs.as_outcomes = vs.vs_outcomes /\
  venom_asm_terminal_rel vs cs ==>
  LENGTH args = asm_op_arity name /\
  ((?out. asm_step lo o2pc (AsmOp name) cs = AsmRevert out) \/
   (?out. asm_step lo o2pc (AsmOp name) cs = AsmFault out))
Proof
  ACCEPT_TAC symControlAbortRegularOwnTheory.regular_abort_prepared_step
QED

Theorem sym_invalid_prepared_terminal:
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  asm_block_at prog cs.as_pc [AsmOp "INVALID"] ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >>
  irule (SRULE [asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlAbortRegularOwnTheory.sym_invalid_prepared_terminal_mode_conditional))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs'.as_pc < LENGTH prog /\ EL cs'.as_pc prog = ai` by
        gvs[asm_block_at_def] >>
      drule_all asm_sym_step >> simp[]) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem sym_regular_abort_prepared_terminal:
  !cp. MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  inst_wf inst /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  eval_operands inst.inst_operands vs = SOME args /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  cs.as_stack = args ++ tail /\ cs.as_call_ctx = vs.vs_call_ctx /\
  cs.as_outcomes = vs.vs_outcomes /\
  venom_asm_terminal_rel vs cs /\
  ss.sym_stack = MAP Val args ++ suffix /\
  (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b) /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\
  asm_static_wf prog /\ asm_sym_rel prog env cs ss /\
  asm_block_at prog cs.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  gen_tac >> strip_tac >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; INVALID;
      CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
   MEM name ["STOP"; "RETURN"; "REVERT"; "INVALID"; "SELFDESTRUCT";
      "CREATE"; "CREATE2"; "RETURNDATACOPY"; "CALL"; "STATICCALL"; "DELEGATECALL"]` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def] >>
  drule_all terminal_source_memory_reads_safe >> strip_tac >>
  drule_all regular_abort_prepared_step >> strip_tac >>
  irule sym_terminal_opcode_transfer >> metis_tac[]
QED

Theorem sym_regular_abort_arranged_terminal:
  !cp.
  lo = SND (compute_label_offsets prog) /\
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  inst_wf inst /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cp fn ret srest arranged ss /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\ asm_static_wf prog /\
  venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  gen_tac >> strip_tac >>
  rename1 `sym_kinds_ok cplan fn ret srest arranged ss` >>
  Cases_on `inst.inst_opcode = INVALID`
  >- (irule sym_invalid_prepared_terminal >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      goal_assum (drule_at (Pat `asm_sym_rel _ _ _ _`)) >>
      gvs[asmIRTheory.venom_to_evm_name_def]) >>
  drule_all regular_abort_source_arguments >> strip_tac >>
  `compute_operands inst = REVERSE inst.inst_operands` by
    metis_tac[regular_abort_operand_order] >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT;
      ASSERT_UNREACHABLE; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
   eval_operands (REVERSE (compute_operands inst)) vs = SOME args` by
    gvs[listTheory.MEM] >>
  drule_all terminal_arranged_word_stack >> strip_tac >>
  `MEM inst.inst_opcode [REVERT; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
   (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b)` by
    ((conj_tac >- metis_tac[listTheory.MEM]) >>
     fs[sym_kinds_ok_def]) >>
  `mid.as_call_ctx = vs.vs_call_ctx /\ mid.as_outcomes = vs.vs_outcomes` by
    fs[venom_asm_rel_def, frame_view_def] >>
  irule sym_regular_abort_prepared_terminal >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `source_memory_reads_disjoint _ _ _`)) >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `venom_asm_terminal_rel _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem sym_abort_regular_terminal_exists:
  !fuel ctx cp lo o2pc prog lv dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 env ret srest labs0 ss a vs'.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL] /\
  source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps prog env m ss)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `fn_frame_inv ctx cplan lo fn ra rest mem0 ps vs st` >>
  `?name. venom_to_evm_name inst.inst_opcode = SOME name` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_commutative inst.inst_opcode /\
   generate_regular_inst_plan lv dfg cfg fn inst nl halting term label ps = (ops,final)` by
    gvs[listTheory.MEM, venomEffectsTheory.is_commutative_def, generate_inst_plan_def,
        is_pre_codegen_opcode_def, is_param_opcode_def,
        is_unlowered_fmp_opcode_def, is_raw_fmp_opcode_def,
        is_unlowered_internal_call_opcode_def] >>
  `ssa_form fn` by fs[codegen_ready_fn_def] >>
  drule_all sym_regular_abort_frame_prefix_deep >> strip_tac >>
  `asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss_mid /\
   sym_kinds_ok cplan fn ret srest arranged ss_mid` by fs[sym_frame_inv_def] >>
  `label_positions_ok inst` by
    (fs[fn_shape_ok_def, listTheory.EVERY_MEM, inst_shape_ok_def] >>
     metis_tac[]) >>
  `EVERY (\op. op <> dead_stack_marker) (compute_operands inst)` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `sym_terminal (sym_steps prog env 1 ss_mid)` by
    (irule sym_regular_abort_arranged_terminal >> metis_tac[]) >>
  qexists `LENGTH (execute_plan cplan.cp_initial_fmp pre) + 1` >>
  simp[sym_steps_add]
QED

(* Static writes use ordinary word operands even though their runs abort. *)
Theorem sym_static_regular_arranged_terminal[local]:
  MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL] /\
  inst_wf inst /\ vs.vs_call_ctx.cc_static /\
  step_inst fuel ctx inst vs = Abort a vs' /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  source_memory_reads_disjoint cplan inst vs /\
  context_source_memory_writes_disjoint cplan inst vs /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  asm_static_wf prog /\ venom_to_evm_name inst.inst_opcode = SOME name /\
  asm_block_at prog mid.as_pc [AsmOp name] ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  strip_tac >>
  `MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL; CREATE; CREATE2]` by
    fs[listTheory.MEM] >>
  drule_all step_inst_static_abort >> strip_tac >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule fnBlockBodyHelpersTheory.label_positions_ok_other >> gvs[listTheory.MEM]) >>
  `compute_operands inst = REVERSE inst.inst_operands /\
   (!op. MEM op (compute_operands inst) ==>
     MEM op inst.inst_operands /\ ~is_label_operand op) /\
   ~MEM inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET; CODECOPY]` by
    (gvs[listTheory.MEM, compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, venomWfTheory.inst_wf_def,
         listTheory.LENGTH_EQ_NUM_compute] >>
     gvs[label_positions_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!op sv. MEM op (compute_operands inst) /\ op_kind_ok fn ret op sv ==>
    ?w. sv = Val w` by
    (rpt strip_tac >> irule ordinary_noncopy_operand_word_kind >>
     qexistsl [`ctx`, `fn`, `inst`, `op`, `ret`] >>
     fs[listTheory.EVERY_MEM, listTheory.MEM] >> metis_tac[]) >>
  `eval_operands (REVERSE (compute_operands inst))
      (frame_view fn ra vs with vs_memory := m) = SOME vals` by
    (`eval_operands inst.inst_operands (frame_view fn ra vs with vs_memory := m) =
      eval_operands inst.inst_operands vs` by
       (irule ordinary_selected_operands_frame_view >> simp[] >>
        qexists `inst` >> fs[listTheory.MEM]) >> simp[]) >>
  `!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op` by
    simp[venomMemPropsTheory.eval_operand_with_memory,
         genFrameSimTheory.operand_val_memory_update] >>
  drule_all arranged_word_prepared_symbolic_stack >> strip_tac >>
  `LENGTH vals = LENGTH inst.inst_operands` by
    metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length] >>
  `mid.as_call_ctx = vs.vs_call_ctx /\ mid.as_outcomes = vs.vs_outcomes` by
    fs[venom_asm_rel_def, frame_view_def] >>
  `MEM (name,LENGTH vals)
    [("SSTORE",2); ("TSTORE",2); ("SELFDESTRUCT",1); ("CREATE",3);
     ("CREATE2",4); ("CALL",7)] /\
   LENGTH vals = asm_op_arity name /\
   (name = "CALL" ==> EL 2 vals <> 0w \/ mid.as_outcomes = [])` by
    gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def,
        venomWfTheory.inst_wf_def, asm_op_arity_def, asm_op_arity_table_def] >>
  `?out. asm_steps lo o2pc prog 1
      (mid with as_stack := mid.as_stack ++ rest) = AsmFault out` by
    (qspecl_then [`lo`, `o2pc`, `prog`, `mid with as_stack := mid.as_stack ++ rest`,
       `name`, `vals`, `DROP (LENGTH (compute_operands inst)) mid.as_stack ++ rest`, `vs`]
       mp_tac static_write_fault_step >>
     simp[] >> impl_tac >- gvs[listTheory.APPEND_ASSOC] >> metis_tac[]) >>
  `asm_step lo o2pc (AsmOp name)
     (mid with as_stack := mid.as_stack ++ rest) = AsmFault out` by
    (`mid.as_pc < LENGTH prog /\ EL mid.as_pc prog = AsmOp name` by
       (qpat_x_assum `asm_block_at _ _ [AsmOp name]` mp_tac >>
        simp_tac (srw_ss()) [asm_block_at_def,
          GSYM arithmeticTheory.ADD1, GSYM arithmeticTheory.LESS_EQ]) >>
     qspecl_then [`lo`, `o2pc`, `prog`, `mid with as_stack := mid.as_stack ++ rest`]
       mp_tac asmOpSimTheory.asm_step_one >> simp[]) >>
  `!b. asm_op_mem_reads name vals b ==>
     source_memory_read_byte inst vs b \/
     (?rng. MEM rng (source_memory_write_ranges inst vs) /\
            byte_in_memory_range rng b)` by
    (rpt strip_tac >>
     Cases_on `MEM inst.inst_opcode [CALL; CREATE; CREATE2]`
     >- (irule memory_family_source_read_coverage >> metis_tac[listTheory.MEM]) >>
     gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def,
         asm_op_mem_reads_def, asmSemTheory.log_table_def]) >>
  `!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cplan b` by
    fs[sym_kinds_ok_def] >>
  `~mem_labels_hit ss.sym_mem_labels (asm_op_mem_reads name vals)` by
    (simp[mem_labels_hit_def] >>
     metis_tac[source_read_byte_no_labels, source_write_byte_no_labels]) >>
  `!msg. sym_step prog env (AsmOp name) ss <> SymBad msg` by
    (simp[sym_step_def] >>
     `sym_step_op prog env name ss = sym_step_concrete name ss` by
       gvs[listTheory.MEM, asmIRTheory.venom_to_evm_name_def, sym_step_op_def,
           asmSemTheory.dup_table_def, asmSemTheory.swap_table_def] >>
     simp[] >> metis_tac[sym_step_concrete_word_prefix_not_bad]) >>
  mp_tac (sym_terminal_step_transfer |> Q.INST
    [`p` |-> `prog`, `cs` |-> `mid with as_stack := mid.as_stack ++ rest`,
     `inst` |-> `AsmOp name`, `cr` |-> `AsmFault out`]) >>
  qpat_x_assum `lo = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `o2pc = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem sym_static_log_arranged_terminal[local]:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: selected /\
  LENGTH selected = w2n tc + 2 /\ w2n tc <= 4 /\
  vs.vs_call_ctx.cc_static /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) selected /\
  (!op. MEM op selected ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ selected /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  venom_asm_terminal_rel vs (mid with as_stack := mid.as_stack ++ rest) /\
  asm_sym_rel prog env (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest arranged ss /\
  source_memory_reads_disjoint cplan inst vs /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  asm_static_wf prog /\
  asm_block_at prog mid.as_pc [AsmOp ("LOG" ++ num_to_dec_string (w2n tc))] ==>
  sym_terminal (sym_steps prog env 1 ss)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  irule (SRULE [asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlAbortStaticOwnTheory.sym_static_log_arranged_terminal_mode_kernel))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs.as_pc < LENGTH prog /\ EL cs.as_pc prog = ai` by
        gvs[asm_block_at_def] >>
      drule_all asm_sym_step >> simp[]) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem sym_abort_static_regular_terminal_exists[local]:
  !fuel ctx cp lo o2pc prog lv dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 env ret srest labs0 ss a vs'.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL] /\
  vs.vs_call_ctx.cc_static /\ source_memory_reads_disjoint cp inst vs /\
  context_source_memory_writes_disjoint cp inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps prog env m ss)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[sym_frame_inv_def] >>
  irule (SRULE [asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlAbortStaticOwnTheory.sym_abort_static_regular_terminal_exists_mode_kernel))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs.as_pc < LENGTH prog /\ EL cs.as_pc prog = ai` by
        gvs[asm_block_at_def] >>
      drule_all asm_sym_step >> simp[]) >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem sym_abort_static_log_terminal_exists[local]:
  !fuel ctx cp lo o2pc prog lv dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 env ret srest labs0 ss a vs'.
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  inst.inst_opcode = LOG /\
  source_memory_reads_disjoint cp inst vs /\
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
  label_flow_ok ctx /\ asm_static_wf prog /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?m. sym_terminal (sym_steps prog env m ss)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[sym_frame_inv_def] >>
  irule (SRULE [asm_sym_rel_core_canonical, asm_sym_step_rel_core_canonical,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlAbortStaticOwnTheory.sym_abort_static_log_terminal_exists_mode_kernel))) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `cs.as_pc < LENGTH prog /\ EL cs.as_pc prog = ai` by
        gvs[asm_block_at_def] >>
      drule_all asm_sym_step >> simp[]) >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem sym_assert_unreachable_suffix_terminal:
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel l; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel l] /\
  ss.sym_stack = Val 0w :: stk ==>
  sym_terminal (sym_steps p env 3 ss)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`]
      (SPEC_ALL symControlAbortConditionalOwnTheory.sym_assert_unreachable_suffix_terminal_mode)))
QED

Theorem sym_assert_zero_iszero:
  asm_block_at p ss.sym_base.as_pc [AsmOp "ISZERO"] /\
  ss.sym_stack = Val 0w :: stk ==>
  sym_steps p env 1 ss = SymOK
    (ss with <|sym_base := asm_next (ss.sym_base with as_stack := []);
               sym_stack := Val 1w :: stk|>)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`]
      (SPEC_ALL symControlAbortConditionalOwnTheory.sym_assert_zero_iszero_mode)))
QED

Theorem sym_assert_suffix_terminal:
  asm_block_at p ss.sym_base.as_pc
    [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"] /\
  ss.sym_stack = Val 0w :: stk /\
  sym_jump_dest p (Lab "revert" 0) = SOME pc /\
  asm_block_at p pc (execute_plan fmp revert_postamble) ==>
  sym_terminal (sym_steps p env 7 ss)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`]
      (SPEC_ALL symControlAbortConditionalOwnTheory.sym_assert_suffix_terminal_mode)))
QED

Theorem sym_conditional_abort_zero_stack:
  !cp.
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands = [cond] /\ eval_operand cond vs = SOME 0w /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ label_flow_ok ctx /\ label_positions_ok inst /\
  EVERY (\op. op <> dead_stack_marker) (compute_operands inst) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  arranged.ps_stack = tail ++ compute_operands inst /\
  venom_asm_rel lo arranged (frame_view fn ra vs with vs_memory := m) mid /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 arranged
    (mid with as_stack := mid.as_stack ++ rest) ss ==>
  ?stk. ss.sym_stack = Val 0w :: stk
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM inst.inst_opcode [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT;
     ASSERT_UNREACHABLE; INVALID; CREATE; CREATE2; RETURNDATACOPY] /\
   eval_operands (REVERSE (compute_operands inst)) vs = SOME [0w]` by
    (Cases_on `inst.inst_opcode = ASSERT` >>
     gvs[compute_operands_def, python_stack_operands_def,
         ir_specific_operand_order_def, eval_operands_def]) >>
  drule_then (map_every assume_tac o CONJUNCTS) (iffLR sym_frame_inv_def) >>
  `MEM inst.inst_opcode
    [STOP; RETURN; SELFDESTRUCT; REVERT; ASSERT; ASSERT_UNREACHABLE;
     INVALID; CREATE; CREATE2; RETURNDATACOPY; CALL; STATICCALL; DELEGATECALL]` by
    (fs[listTheory.MEM] >> metis_tac[]) >>
  drule_all terminal_arranged_word_stack >> simp[]
QED

Theorem sym_conditional_abort_inversion:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?cond. inst.inst_operands = [cond] /\ eval_operand cond vs = SOME 0w
Proof
  ACCEPT_TAC symControlAbortConditionalOwnTheory.sym_conditional_abort_inversion
QED

Theorem sym_abort_conditional_terminal_exists:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss a vs'.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\ opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\ asm_static_wf prog /\
    (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss /\
    step_inst fuel ctx inst vs = Abort a vs' /\
    (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) ==>
    ?m. sym_terminal (sym_steps prog env m ss)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[] >>
  irule (SRULE [asm_sym_rel_core_canonical, GSYM sym_frame_inv_def,
                 sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
             `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
      (SPEC_ALL symControlAbortConditionalOwnTheory.sym_abort_conditional_terminal_exists_mode_kernel))) >>
  asm_rewrite_tac[] >> conj_tac >- (metis_tac[sym_code_label_dest]) >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  conj_tac
  >- (qpat_assum `asm_static_wf prog`
        (fn th => POP_ASSUM_LIST (K (assume_tac th))) >>
      rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gnvs[] >>
      drule_all (GEN_ALL (SRULE []
        (Q.INST [`lo` |-> `SND (compute_label_offsets prog)`,
                 `o2pc` |-> `build_offset_to_pc prog`,
                 `dfg` |-> `dfg_build_function fn`]
          (SPEC_ALL sym_conditional_abort_frame_prefix_deep)))) >>
      simp[]) >>
  rpt (goal_assum (drule_at Any) >> simp[]) >> first_assum (irule_at Any)
QED

Theorem sym_abort_terminal_counts_join:
  ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert out) \/
   (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault out)) /\
  venom_asm_terminal_rel vs out /\
  sym_terminal (sym_steps prog env m ss) ==>
  ?k fin.
    ((a = Revert_abort /\ asm_steps lo o2pc prog k st = AsmRevert fin) \/
     (a = ExHalt_abort /\ asm_steps lo o2pc prog k st = AsmFault fin)) /\
    venom_asm_terminal_rel vs fin /\ sym_terminal (sym_steps prog env k ss)
Proof
  ACCEPT_TAC (SRULE [sym_steps_mode_def]
    (Q.INST [`allow_own` |-> `F`]
      (SPEC_ALL symControlTerminalOwnTheory.sym_abort_terminal_counts_join_mode)))
QED

Theorem sym_abort_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    (inst.inst_opcode = ASSERT ==> MEM (AsmLabel "revert") prog) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?m. sym_terminal (sym_steps prog env m ss)` by
    (Cases_on `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE`
     >- (drule_all sym_abort_conditional_terminal_exists >> simp[]) >>
     Cases_on `vs.vs_call_ctx.cc_static /\
       MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL; LOG]`
     >- (qpat_x_assum `vs.vs_call_ctx.cc_static /\ _` strip_assume_tac >>
         Cases_on `inst.inst_opcode = LOG`
         >- (drule_all sym_abort_static_log_terminal_exists >> simp[]) >>
         `MEM inst.inst_opcode [SSTORE; TSTORE; SELFDESTRUCT; CALL]` by
           gvs[listTheory.MEM] >>
         drule_all sym_abort_static_regular_terminal_exists >> simp[]) >>
     `MEM inst.inst_opcode [REVERT; INVALID; CREATE; CREATE2; RETURNDATACOPY;
         CALL; STATICCALL; DELEGATECALL]` by
       (drule opcodeClassTheory.step_inst_abort_opcodes >> fs[listTheory.MEM] >> metis_tac[]) >>
     drule_all sym_abort_regular_terminal_exists >> simp[]) >>
  drule_all gen_inst_abort_frame_sim_deep >>
  disch_then (qx_choose_then `n` (qx_choose_then `out` assume_tac)) >>
  irule sym_abort_terminal_counts_join >> metis_tac[]
QED

Theorem sym_pop_pushed_steps:
  ss.sym_stack = sv :: stk /\
  asm_block_at p ss.sym_base.as_pc [AsmOp "POP"] ==>
  sym_steps p env 1 ss =
    SymOK (ss with <|sym_base := ss.sym_base with as_pc := ss.sym_base.as_pc + 1;
                    sym_stack := stk|>)
Proof
  ACCEPT_TAC symControlGasOwnTheory.sym_pop_pushed_steps
QED

Theorem sym_pop_pushed_frame_sim:
  !p env ctx cp fn ret srest labs0 ps op cs ss.
  sym_frame_inv p env ctx cp fn ret srest labs0
    (ps with ps_stack := SNOC op ps.ps_stack) cs ss /\
  asm_static_wf p /\ asm_block_at p cs.as_pc [AsmOp "POP"] ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 cs = AsmOK cs' /\
    sym_steps p env 1 ss = SymOK ss' /\
    sym_frame_inv p env ctx cp fn ret srest labs0 ps cs' ss' /\
    cs'.as_pc = cs.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "POP"]` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_pop_pushed_kinds_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  metis_tac[asm_sym_rel_pc]
QED

Theorem sym_gas_emit_pc:
  asm_sym_rel p env cs ss /\ asm_sym_rel p env cs' ss' /\
  asm_block_at p cs.as_pc [AsmOp "GAS"] /\
  sym_steps p env 1 ss = SymOK ss' ==>
  cs'.as_pc = cs.as_pc + 1
Proof
  strip_tac >> imp_res_tac asm_sym_rel_pc >>
  `asm_block_at p ss.sym_base.as_pc [AsmOp "GAS"]` by metis_tac[] >>
  drule sym_gas_steps >> disch_then (qspec_then `env` assume_tac) >> gvs[]
QED

Theorem sym_gas_optimistic_frame_sim:
  optimistic_swap_plan dfg inst nl term ps = (ops,ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops)` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_gas_optimistic_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >> conj_tac
  >- metis_tac[sym_frame_region_labels_transfer] >>
  metis_tac[asm_sym_rel_pc, arithmeticTheory.ADD_COMM]
QED

Theorem sym_gas_live_plan_frame_sim:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  optimistic_swap_plan dfg inst nl term
    (ps with ps_stack := SNOC (Var out) ps.ps_stack) = (tail, arranged) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) tail /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp (SOEmit "GAS" :: tail)) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp (SOEmit "GAS" :: tail))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp (SOEmit "GAS" :: tail))) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 (release_dead_spills nl arranged) cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp (SOEmit "GAS" :: tail))
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (SOEmit "GAS" :: tail))` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_gas_live_plan_steps >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `last`] >> simp[] >> conj_tac
  >- metis_tac[sym_frame_region_labels_transfer] >>
  metis_tac[asm_sym_rel_pc, arithmeticTheory.ADD_COMM]
QED
Theorem sym_gas_retained_plan_frame_sim:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp [SOEmit "GAS"]) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp [SOEmit "GAS"])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp [SOEmit "GAS"])) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0
      (release_dead_spills nl (ps with ps_stack := SNOC (Var out) ps.ps_stack)) cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp [SOEmit "GAS"])
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOEmit "GAS"])` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_gas_retained_plan_steps >>
  disch_then (qspecl_then [`nl`, `env`] strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  metis_tac[asm_sym_rel_pc, arithmeticTheory.ADD_COMM]
QED
Theorem sym_gas_pop_plan_frame_sim:
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1]) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1])) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1])) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 (release_dead_spills nl ps) cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1])
Proof
  strip_tac >> fs[sym_frame_inv_def] >>
  `asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp [SOEmit "GAS"; SOPop 1])` by
    metis_tac[asm_sym_rel_pc] >>
  drule_all symControlGasOwnTheory.sym_gas_pop_plan_steps >>
  disch_then (qspecl_then [`nl`, `env`] strip_assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  qexistsl [`cs'`, `ss'`] >> simp[] >>
  metis_tac[asm_sym_rel_pc, arithmeticTheory.ADD_COMM]
QED
Theorem sym_gas_plan_frame_sim:
  inst.inst_opcode = GAS /\ inst.inst_operands = [] /\ inst.inst_outputs = [out] /\
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  generate_inst_plan lv dfg cfg fn inst nl halting term label ps = SOME (ops,ps') /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
  ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss /\
  asm_static_wf p /\
  asm_block_at p cs.as_pc (execute_plan initial_fmp ops) ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan initial_fmp ops)) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 ps' cs' ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    (GEN_ALL (SRULE [asm_sym_rel_core_canonical, GSYM sym_frame_inv_def,
                      sym_steps_mode_def]
      (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets p)`,
               `code_ok` |-> `asm_data_env_ok p env`, `own` |-> `[]`]
        (SPEC_ALL symControlGasOwnTheory.sym_gas_plan_frame_sim_mode_conditional)))) >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >> simp[] >>
  disch_then (qspec_then `r` mp_tac) >> simp[] >>
  impl_tac >- metis_tac[asm_sym_steps_lockstep] >> simp[]
QED

Theorem sym_gas_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode = GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input must be owned by the planner: each is either
       on the stack at any depth or available from the spill map.
       generated_plan_state_wf_marked is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
        sym_steps prog env n ss = SymOK ss' /\
        sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[] >>
  drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL (SRULE [asm_sym_rel_core_canonical, GSYM sym_frame_inv_def,
                      sym_steps_mode_def]
      (Q.INST [`allow_own` |-> `F`, `lo` |-> `SND (compute_label_offsets prog)`,
               `code_ok` |-> `asm_data_env_ok prog env`, `own` |-> `[]`]
        (SPEC_ALL symControlGasOwnTheory.sym_gas_frame_sim_deep_mode_kernel)))) >>
  disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then assume_tac >> gen_tac >> strip_tac >>
  first_x_assum irule >>
  conj_tac >- metis_tac[asm_sym_steps_lockstep] >>
  metis_tac[]
QED

Theorem sym_revert_forward_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\
        sym_terminal (sym_steps prog env n ss)
Proof
  rpt strip_tac >>
  drule rf_spills_separated_entry_marked >> disch_tac >>
  drule_all sym_rf_entry_forward_abort >> simp[]
QED

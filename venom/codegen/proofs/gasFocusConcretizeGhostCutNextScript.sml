Theory gasFocusConcretizeGhostCutNext
Ancestors
  concretizePtrDallocaRuntimeHistory concretizePtrDallocaEndpointDemands
  concretizePtrDallocaGhostInterface concretizePtrStructuralTranscript
  concretizePtrPairedPrefix concretizePtrRequestHistory
  concretizePtrTaintContent concretizePtrOpaqueRetpc concretizePtrSharedFields
  concretizePtrObservationInterface concretizeMemLocDefs
  ptrDiscipline venomWf venomInst venomState opcodeClass venomExecSemantics
  list finite_map pred_set words memLocDefs pointerConfinedDefs
  concretizeStepStructure contextCodegenRel arithmetic passSharedDefs

(* Scalar reads cannot use a runtime pointer for their address/key. *)
Theorem cut_scalar_read_clean[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ FDOM G SUBSET fn_pv P fn /\
  MEM inst.inst_opcode [ILOAD;SLOAD;TLOAD] /\ inst.inst_operands = [op] ==>
  ptr_nonopaque_operand fn op /\ op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[EVERY_MEM, MEM] >>
  conj_tac
  >- (Cases_on `op` >> gvs[op_prov_def, SUBSET_DEF, TO_FLOOKUP, MEM] >>
      metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  gvs[taint_ok_def, MEM]
QED

Theorem cut_iload_bound[local]:
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [op] /\
  eval_operand op s = SOME x /\ op_prov G op = NONE /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s ==>
  w2n x + 32 <= lo
Proof
  strip_tac >> spose_not_then assume_tac >>
  `MEM (w2n x,32) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, eval_operands_def] >>
  `?ops v b sz. mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
    FLOOKUP G v = SOME (b,sz) /\ b <= w2n x /\ w2n x+32 <= b+sz` by
    (fs[access_ok_def] >>
     qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges inst s) /\ _ ==> _`
       (qspecl_then [`w2n x`,`32`] mp_tac) >> simp[] >>
     `lo < 32+w2n x` by decide_tac >> simp[ADD_COMM]) >>
  gvs[mem_read_ops_def, op_prov_def]
QED

Theorem cut_unary_mask_demands[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ FDOM G SUBSET fn_pv P fn /\
  ptr_ledger_erases dyn births TG G /\ ptr_mixed_vars births positions TG tn fn ft s t /\
  s.vs_labels = t.vs_labels /\ access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (!i. i < lo ==> i IN tnt.t_mem ==> i IN tn.t_mem) /\
  tnt.t_stor SUBSET tn.t_stor /\ tnt.t_trans SUBSET tn.t_trans /\
  (!a w wt k. inst.inst_opcode = MLOAD /\ inst.inst_operands = [a] /\
     eval_operand a s = SOME w /\ eval_operand a t = SOME wt /\ k < 32 ==>
     w2n wt + k IN tnt.t_mem ==> w2n w + k IN tn.t_mem) ==>
  !a wt. inst.inst_operands = [a] /\ eval_operand a t = SOME wt ==>
     ?w. eval_operand a s = SOME w /\
       ((inst.inst_opcode = MLOAD \/ inst.inst_opcode = ILOAD) ==>
         mem_word_taint tnt.t_mem (w2n wt) SUBSET mem_word_taint tn.t_mem (w2n w)) /\
       (inst.inst_opcode = SLOAD ==>
         key_taint tnt.t_stor wt SUBSET key_taint tn.t_stor w) /\
       (inst.inst_opcode = TLOAD ==>
         key_taint tnt.t_trans wt SUBSET key_taint tn.t_trans w)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [ILOAD;SLOAD;TLOAD]`
  >- (drule_all cut_scalar_read_clean >> strip_tac >>
      `eval_operand a s = eval_operand a t` by
        (irule ptr_mixed_scalar_eval >> metis_tac[]) >>
      qexists `wt` >> fs[MEM] >> simp[]
      >- (`w2n wt + 32 <= lo` by (irule cut_iload_bound >> metis_tac[]) >>
          simp[mem_word_taint_def, SUBSET_DEF] >> rpt strip_tac >>
          qpat_assum `!i. i < lo ==> _` irule >> simp[]) >>
      fs[key_taint_def,SUBSET_DEF] >> metis_tac[]) >>
  `?w. eval_operand a s = SOME w` by
    (drule_all ptr_mixed_vars_eval_presence >>
     disch_then (qspec_then `a` mp_tac) >> Cases_on `eval_operand a s` >> simp[]) >>
  qexists `w` >> fs[MEM] >> simp[] >> strip_tac >>
  simp[mem_word_taint_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem focus_cut_ghost_runtime_next:
  ptr_snapshot_step C pre a b (tokens,registry,births,PT,TG,saved,entries)
    (tokens',registry',births',PT',TG',saved',entries') /\
  ptr_chrono_step Ct at bt /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  at.po_inst = concretize_inst_with_positions lp a.po_inst /\ at.po_inst.inst_opcode <> NOP /\
  fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn) /\
  inst_wf a.po_inst /\ FDOM a.po_prov SUBSET fn_pv P a.po_fn /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\ ~in_revert_forward a.po_fn a.po_state /\
  ptr_ledger_erases dyn births TG a.po_prov /\
  ptr_paired_sample positions a at (tokens,registry,births,PT,TG,saved,entries) /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE) /\
  (!v site. FLOOKUP TG v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
     FLOOKUP at.po_prov v = SOME site) /\
  LENGTH PT = LENGTH a.po_params /\ LENGTH a.po_params = LENGTH at.po_params /\
  (!k site. k < LENGTH a.po_params ==>
    (EL k at.po_params = SOME site ==>
       EL k a.po_params = SOME site /\ EL k PT = NONE /\
       EL k a.po_state.vs_params = EL k at.po_state.vs_params) /\
    (EL k PT = NONE /\ EL k a.po_params = SOME site ==>
       EL k at.po_params = SOME site)) /\
  (!i. i < lo ==> i IN at.po_taint.t_mem ==> i IN a.po_taint.t_mem) /\
  at.po_taint.t_stor SUBSET a.po_taint.t_stor /\ at.po_taint.t_trans SUBSET a.po_taint.t_trans /\
  (!op w wt k. a.po_inst.inst_opcode = MLOAD /\ a.po_inst.inst_operands = [op] /\
     eval_operand op a.po_state = SOME w /\ eval_operand op at.po_state = SOME wt /\ k < 32 ==>
     w2n wt + k IN at.po_taint.t_mem ==> w2n w + k IN a.po_taint.t_mem) ==>
  (ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
   (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TG' v = NONE) /\
   (!v site. FLOOKUP TG' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
      FLOOKUP bt.po_prov v = SOME site)) /\
  PT' = PT /\ saved' = saved /\
  b.po_params = a.po_params /\ bt.po_params = at.po_params /\
  b.po_stack = a.po_stack /\ bt.po_stack = at.po_stack /\
  b.po_state.vs_params = a.po_state.vs_params /\
  bt.po_state.vs_params = at.po_state.vs_params
Proof
  simp[ptr_snapshot_step_def, ptr_paired_sample_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `a.po_state.vs_labels = at.po_state.vs_labels /\
   a.po_state.vs_fmp = at.po_state.vs_fmp` by
    (drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  `!op. op_taint at.po_taint op SUBSET op_taint a.po_taint op` by
    (gen_tac >> Cases_on `op` >>
     fs[op_taint_def, ptr_dalloca_ghost_vars_def, entry_taint_def] >> metis_tac[]) >>
  `!op. MEM op a.po_inst.inst_operands ==>
     op_taint at.po_taint op SUBSET op_taint a.po_taint op` by simp[] >>
  `!op wt. a.po_inst.inst_operands = [op] /\ eval_operand op at.po_state = SOME wt ==>
     ?w. eval_operand op a.po_state = SOME w /\
       ((a.po_inst.inst_opcode = MLOAD \/ a.po_inst.inst_opcode = ILOAD) ==>
         mem_word_taint at.po_taint.t_mem (w2n wt) SUBSET
         mem_word_taint a.po_taint.t_mem (w2n w)) /\
       (a.po_inst.inst_opcode = SLOAD ==>
         key_taint at.po_taint.t_stor wt SUBSET key_taint a.po_taint.t_stor w) /\
       (a.po_inst.inst_opcode = TLOAD ==>
         key_taint at.po_taint.t_trans wt SUBSET key_taint a.po_taint.t_trans w)` by
    (rpt gen_tac >> strip_tac >> irule cut_unary_mask_demands >> simp[] >>
     goal_assum (drule_at (Pat `ptr_mixed_vars _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_ledger_erases _ _ _ _`)) >>
     goal_assum (drule_at (Pat `access_ok _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[]) >>
  drule_all ptr_dalloca_runtime_demands >> strip_tac >>
  `((a.po_inst.inst_opcode = ADD \/ a.po_inst.inst_opcode = SUB) ==>
      ?x y. a.po_inst.inst_operands = [x;y]) /\
   (a.po_inst.inst_opcode = ASSIGN ==> ?op. a.po_inst.inst_operands = [op])` by
    (conj_tac >> strip_tac >> qpat_assum `inst_wf a.po_inst` mp_tac >>
     fs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
  `((a.po_inst.inst_opcode = ALLOCA /\ at.po_inst.inst_opcode = ASSIGN /\
      (?pos. at.po_inst.inst_operands = [Lit pos]) /\
      at.po_inst.inst_outputs = a.po_inst.inst_outputs) \/
    (a.po_inst.inst_opcode <> ALLOCA /\ at.po_inst = a.po_inst))` by
    (Cases_on `a.po_inst.inst_opcode = ALLOCA`
     >- (`?out. a.po_inst.inst_outputs = [out]` by
           fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
         qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` mp_tac >>
         simp[concretize_inst_with_positions_def] >> CASE_TAC >> strip_tac >>
         gvs[mk_assign_inst_def, mk_nop_inst_def]) >>
     gvs[concretize_positions_unchanged]) >>
  irule ptr_dalloca_runtime_chrono_next >>
  simp[] >> metis_tac[]
QED

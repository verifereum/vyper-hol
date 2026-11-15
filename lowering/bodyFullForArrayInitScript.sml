Theory bodyFullForArrayInit
Ancestors
  bodyFullForArray stmtForDynArrayMemoryEntry whitelistForIterDynFrag
  fragGasOriginPtrLoop fragGasSeqPtr fragExecMem instMemFrontier
  venomExecSemantics venomState venomInst ptrDiscipline
  decoderAllocationBoundsPtr words list rich_list finite_map emitHelperProps
  fragExec venomExecProofs memSafeRun exprLoweringProps entrySinkExtraction
  stmtSimDeclPath unitTransformDefs contextCodegenRel codegenRel

Theorem for_array_dynamic_entry_path_full:
  ainst.inst_opcode = ALLOCA /\ ainst.inst_outputs = [p] /\
  MEM ainst (fn_insts func) /\ fn_inst_ids_distinct func /\
  ainst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  lookup_block s0.vs_current_bb func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      pre ++ [mk_inst mi MLOAD [saved_base] [lv]; ainst;
              mk_inst j JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks =
    SOME <|bb_label := entry; bb_instructions :=
      [mk_inst e1 ASSIGN [Lit 0w] [idx];
       mk_inst e2 GT [Var lv; Lit (n2w c)] [g];
       mk_inst e3 ISZERO [Var g] [vld];
       mk_inst e4 ASSERT [Var vld] [];
       mk_inst e5 JMP [Label cond] []]|> /\
  s0.vs_inst_idx = LENGTH pre /\ ~s0.vs_halted /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ P es /\
  lookup_scopes id es.scopes = NONE /\
  eval_operand saved_base s0 = SOME array_base /\
  mload (w2n array_base) s0 = n2w (LENGTH vs) /\
  LENGTH vs <= c /\ c < dimword (:256) /\ ret_pc_ok cenv st s0 /\
  ALL_DISTINCT [lv;p;idx;g;vld] /\
  not_local_ptr cenv es.scopes lv /\ not_local_ptr cenv es.scopes p /\
  not_local_ptr cenv es.scopes idx /\ not_local_ptr cenv es.scopes g /\
  not_local_ptr cenv es.scopes vld /\
  (!x. saved_base = Var x ==> ~MEM x [lv;p;idx;g;vld]) /\
  (!x. not_fresh_at st x ==> ~MEM x [lv;p;idx;g;vld]) /\
  alloca_history func s0 /\ w2n array_base + 32 <= s0.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
  exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
    (n2w sz : bytes32) = OK sA /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G tn
    [mk_inst mi MLOAD [saved_base] [lv];ainst] s0 G1 tn1) /\
  (!H. inst_seq_ptr (DF H) lo ctx func PG G1 tn1
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv;Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] (jump_to entry sA) G2 tn2) ==>
  ?dst cc s1.
    exec_alloca ainst (update_var lv (n2w (LENGTH vs)) s0)
      (n2w sz : bytes32) = OK s1 /\ s1 = sA /\
    cc = jump_to cond (update_var vld 1w (update_var g 0w
      (update_var idx 0w (jump_to entry s1)))) /\
    array_loop_inv ctx func cenv cx st0 P vs id idx saved_base array_base p dst sz
      ainst cond st 0 es cc /\
    lookup_var lv cc = SOME (n2w (LENGTH vs)) /\
    array_caller_frame st s0 cc /\
    gas_marked_path F ctx func s0 0 (OK cc) /\
    gas_path_mem ctx func s0 0 (OK cc) /\
    alloca_history func cc /\ cc.vs_memory = s0.vs_memory /\
    s0.vs_alloca_next <= cc.vs_alloca_next /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s0,G,tn) [] (OK cc,G2,tn2))
Proof
  strip_tac >>
  drule_all (SIMP_RULE pure_ss [PULL_EXISTS] dynarray_loop_initialize_mem) >>
  strip_tac >>
  `s1 = sA` by gvs[] >>
  qpat_x_assum `s1 = sA` SUBST_ALL_TAC >>
  qexists_tac `dst` >> simp[] >>
  qabbrev_tac `sl = update_var lv (n2w (LENGTH vs)) s0` >>
  qabbrev_tac `en = jump_to entry sA` >>
  qabbrev_tac `u = update_var vld 1w (update_var g 0w (update_var idx 0w en))` >>
  `step_inst_base (mk_inst mi MLOAD [saved_base] [lv]) s0 = OK sl` by
    (simp[Abbr `sl`] >> qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
     irule step_MLOAD >> simp[]) >>
  `step_inst_base ainst sl = OK sA` by
    simp[step_inst_base_opcode_eqs, eval_operand_def,Abbr `sl`] >>
  `run_inst_seq [mk_inst mi MLOAD [saved_base] [lv];ainst] s0 = OK sA` by
    simp[run_inst_seq_def] >>
  `run_inst_seq_mem_ok [mk_inst mi MLOAD [saved_base] [lv];ainst] s0` by
    (simp[run_inst_seq_mem_ok_def,below_frontier_MLOAD,inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `allocas_from lo sA` by
    (irule (INST_TYPE [alpha |-> ``:256``] exec_alloca_preserves_allocas_from) >>
     qexistsl_tac [`n2w sz : bytes32`,`ainst`,`sl`] >>
     simp[Abbr `sl`] >> gvs[allocas_from_def,update_var_def]) >>
  `sA.vs_current_bb = s0.vs_current_bb /\ ~sA.vs_halted` by
    (drule run_inst_seq_preserves_entry_control >>
     simp[mk_inst_def,is_terminator_def]) >>
  `lookup_var lv en = SOME (n2w (LENGTH vs))` by
    (drule_all exec_alloca_frames >> strip_tac >>
     gvs[ALL_DISTINCT,Abbr `en`,jump_to_def,lookup_var_def,
         Abbr `sl`,update_var_def,FLOOKUP_UPDATE]) >>
  `run_inst_seq
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv;Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] en = OK u` by
    (simp[Abbr `u`] >> irule dynarray_entry_block_run >>
     gvs[ALL_DISTINCT] >> qexists_tac `LENGTH vs` >> simp[]) >>
  `run_inst_seq_mem_ok
    [mk_inst e1 ASSIGN [Lit 0w] [idx];
     mk_inst e2 GT [Var lv;Lit (n2w c)] [g];
     mk_inst e3 ISZERO [Var g] [vld];
     mk_inst e4 ASSERT [Var vld] []] en` by
    (gvs[ALL_DISTINCT] >>
     simp[run_inst_seq_mem_ok_def,inst_dload_in_section_def,
          step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,
          exec_pure2_def,exec_pure1_def,lookup_var_update_var,
          bool_to_word_def,inst_mem_below_frontier_def,
          source_memory_read_ranges_def,source_memory_write_ranges_def,
          Abbr `u`]) >>
  qpat_x_assum `cc = jump_to cond u` SUBST_ALL_TAC >> simp[] >>
  conj_tac >- gvs[Abbr `u`,ALL_DISTINCT,lookup_var_update_var] >> qx_gen_tac `hh` >>
  qpat_assum `!h. inst_seq_ptr _ _ _ _ _ G tn _ s0 _ _`
    (qspec_then `hh` assume_tac) >>
  `gas_origin_ptr_path (DF hh,lo,explicit,ctx,func,PG) (s0,G,tn) []
     (OK (sA with vs_inst_idx := LENGTH pre + 2),G1,tn1)` by
    (qpat_assum `run_inst_seq _ s0 = OK sA`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac run_inst_seq_gas_origin_ptr_path) >>
     simp[mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[DROP_LENGTH_APPEND,mk_inst_def]) >>
  `gas_origin_ptr_path (DF hh,lo,explicit,ctx,func,PG)
     (sA with vs_inst_idx := LENGTH pre + 2,G1,tn1) []
     (OK en,G1,tn1)` by
    (`gas_origin_ptr_path (DF hh,lo,explicit,ctx,func,PG)
       (sA with vs_inst_idx := LENGTH pre + 2,G1,tn1) []
       (OK (jump_to entry (sA with vs_inst_idx := LENGTH pre + 2)),G1,tn1)`
       suffices_by simp[Abbr `en`,jump_to_def] >>
     irule jmp_origin_ptr_path >> simp[get_instruction_def] >>
     qexists_tac `j` >> simp[EL_APPEND_EQN]) >>
  qpat_assum `!h. inst_seq_ptr _ _ _ _ _ G1 tn1 _ en _ _`
    (qspec_then `hh` assume_tac) >>
  `gas_origin_ptr_path (DF hh,lo,explicit,ctx,func,PG) (en,G1,tn1) []
     (OK (u with vs_inst_idx := 4),G2,tn2)` by
    (qpat_assum `run_inst_seq _ en = OK u`
       (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac run_inst_seq_gas_origin_ptr_path) >>
     simp[Abbr `en`,jump_to_def,mk_inst_def,is_terminator_def] >>
     disch_then irule >> gvs[jump_to_def,mk_inst_def]) >>
  `gas_origin_ptr_path (DF hh,lo,explicit,ctx,func,PG)
     (u with vs_inst_idx := 4,G2,tn2) []
     (OK (jump_to cond (u with vs_inst_idx := 4)),G2,tn2)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,Abbr `en`,jump_to_def,update_var_def,
          allocas_from_def,get_instruction_def] >>
     conj_tac >- (qexists_tac `e5` >> simp[]) >> gvs[allocas_from_def]) >>
  gvs[jump_to_def] >> metis_tac[gas_origin_ptr_path_trans]
QED

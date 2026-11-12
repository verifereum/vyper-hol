(* Word and byte writes in the FMP stage simulation. *)
Theory fmpStageOpSimMemWrites
Ancestors
  fmpStageOpSimMemSupport fmpStageOpSimMemReads fmpStageOpBase fmpStageRel
  o1LowerDloadRangeTransport o1LowerDloadMemoryConsumer o1LowerDloadShared
  o1LowerDloadRelocationKernel o1PassContract ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst memLocDefs pointerConfinedDefs words byte finite_map pred_set list

Theorem fmp_mem_store_value_prov[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MSTORE;MSTORE8] /\ inst.inst_operands = [p;vop] ==>
  op_prov G vop = NONE
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  Cases_on `vop` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  Cases_on `p = Var v` >> gvs[]
QED

Theorem fmp_mem_store_operands:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [MSTORE;MSTORE8] /\
  inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
  ?y w. eval_operand p t = SOME y /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\
    (inst.inst_opcode = MSTORE8 ==> v = w) /\
    ((w2n x=w2n y /\ w2n x+(if inst.inst_opcode=MSTORE then 32 else 1)<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+(if inst.inst_opcode=MSTORE then 32 else 1)<=z /\
       w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn p = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `!v. ~retpc_use_ok inst v` by gvs[retpc_use_ok_def] >>
  `!v. p = Var v ==> ~retpc_var fn v` by
    (metis_tac[fmp_mem_operand_non_retpc, MEM]) >>
  `!v. vop = Var v ==> ~retpc_var fn v` by
    (metis_tac[fmp_mem_operand_non_retpc, MEM]) >>
  `op_prov G vop = NONE` by metis_tac[fmp_mem_store_value_prov] >>
  `?w. eval_operand vop t = SOME w /\
       fmp_value_rel sm NONE (op_taint tn vop) v w` by
    (`MEM vop inst.inst_operands /\ inst.inst_opcode <> PHI` by gvs[] >>
     metis_tac[fmp_stage_operand]) >>
  `word_agree_except (op_taint tn vop) v w` by
    fs[fmp_value_rel_def, ld_value_agree_scalar] >>
  `inst.inst_opcode = MSTORE8 ==> v=w` by
    (strip_tac >> `op_taint tn vop = {}` by
      (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
     metis_tac[fmp_mem_value_clean]) >>
  `MEM p inst.inst_operands /\ inst.inst_opcode <> PHI` by gvs[] >>
  `mem_write_ops inst = SOME <|iao_ofst := p;
      iao_size := SOME (Lit (if inst.inst_opcode=MSTORE then 32w else 1w));
      iao_max_size := SOME (Lit (if inst.inst_opcode=MSTORE then 32w else 1w))|>` by
    (fs[] >> simp[mem_write_ops_def]) >>
  `MEM (w2n x,if inst.inst_opcode=MSTORE then 32 else 1)
       (source_memory_write_ranges inst s)` by
    (fs[] >> simp[source_memory_write_ranges_def, fixed_source_write_range_def]) >>
  `(<|iao_ofst := p;
      iao_size := SOME (Lit (if inst.inst_opcode=MSTORE then 32w else 1w));
      iao_max_size := SOME (Lit (if inst.inst_opcode=MSTORE then 32w else 1w))|> : inst_access_ops).iao_ofst = p` by simp[] >>
  drule_all fmp_mem_write_operand_range >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem fmp_mem_mstore_agree:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  word_agree_except m v w /\
  ((a=c /\ a+32<=eom) \/
   (?id b d z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,d,z) /\
     j+32<=z /\ a=b+j /\ c=d+j)) /\
  mask = ((tn.t_mem DIFF {i | a<=i /\ i<a+32}) UNION {a+k | k IN m}) ==>
  ld_memory_agree (fmp_ld_sites sm) eom mask
    (mstore a v s).vs_memory (mstore c w t).vs_memory
Proof
  strip_tac >> qpat_x_assum `mask = _` SUBST_ALL_TAC >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by
    metis_tac[fmp_mem_geometry] >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  `ld_memory_agree (fmp_ld_sites sm) eom
    ((tn.t_mem DIFF {i | a<=i /\ i<a+32}) UNION {a+k | k<32 /\ k IN m})
    (write_memory_with_expansion a (word_to_bytes v T) s).vs_memory
    (write_memory_with_expansion c (word_to_bytes w T) t).vs_memory` by
    (irule ld_memory_agree_write_geometry >>
     goal_assum (drule_at Any) >>
     simp[LENGTH_word_to_bytes, dimword_def] >>
     fs[word_agree_except_def] >> metis_tac[]) >>
  gvs[mstore_def, write_memory_with_expansion_def,
     LENGTH_word_to_bytes, dimword_def] >>
  irule ld_memory_agree_mono >> goal_assum (drule_at Any) >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem fmp_mem_mstore8_agree:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ((a=c /\ a+1<=eom) \/
   (?id b d z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,d,z) /\
     j+1<=z /\ a=b+j /\ c=d+j)) /\
  mask = (tn.t_mem DIFF {i | a<=i /\ i<a+1}) ==>
  ld_memory_agree (fmp_ld_sites sm) eom mask
    (mstore8 a v s).vs_memory (mstore8 c v t).vs_memory
Proof
  strip_tac >> qpat_x_assum `mask = _` SUBST_ALL_TAC >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by
    metis_tac[fmp_mem_geometry] >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  `ld_memory_agree (fmp_ld_sites sm) eom
    (tn.t_mem DIFF {i | a<=i /\ i<a+LENGTH [(w2w v : word8)]})
    (write_memory_with_expansion a [(w2w v : word8)] s).vs_memory
    (write_memory_with_expansion c [(w2w v : word8)] t).vs_memory` by
    (irule ld_memory_agree_clean_write >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[mstore8_def, write_memory_with_expansion_def]
QED

Theorem fmp_mem_store_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ MEM inst.inst_opcode [MSTORE;MSTORE8] /\
  step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    ld_memory_agree (fmp_ld_sites sm) eom (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [p;vop]` >>
  rename1 `eval_operand p s = SOME x` >>
  rename1 `eval_operand vop s = SOME v` >>
  `MEM inst.inst_opcode [MSTORE;MSTORE8]` by simp[] >>
  drule_all fmp_mem_store_operands >> strip_tac >>
  (Cases_on `inst.inst_opcode = MSTORE`
  >- (gvs[] >>
      `mem_taint tn inst s (mstore (w2n x) v s) =
        ((tn.t_mem DIFF {i | w2n x<=i /\ i<w2n x+32}) UNION
         {w2n x+k | k IN op_taint tn vop})` by
        (irule ld_mem_taint_mstore >> simp[] >> metis_tac[w2n_lt]) >>
      gvs[] >> irule fmp_mem_mstore_agree >> simp[] >> metis_tac[]) >>
  gvs[] >> rename1 `eval_operand vop t = SOME w` >>
  `mem_taint tn inst s (mstore8 (w2n x) w s) =
      tn.t_mem DIFF {i | w2n x<=i /\ i<w2n x+1}` by
    (simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
         fixed_source_write_range_def, written_taint_def, new_site_bytes_def,
         mstore8_def, range_bytes_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]) >>
  gvs[] >> irule fmp_mem_mstore8_agree >> simp[] >> metis_tac[])
QED

Theorem fmp_mem_store_outputs[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MSTORE;MSTORE8] ==> inst.inst_outputs = []
Proof
  strip_tac >>
  `o1_fn_shape C fn /\ MEM inst (fn_insts fn)` by
    metis_tac[fmp_stage_frame_facts] >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  fs[] >> gvs[inst_wf_def]
QED

Theorem fmp_mem_store_ghost[local]:
  MEM inst.inst_opcode [MSTORE;MSTORE8] /\ inst.inst_outputs = [] ==>
  step_taint inst s u tn = tn with t_mem := mem_taint tn inst s u
Proof
  strip_tac >> fs[] >>
  simp[step_taint_def, set_var_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def, taint_component_equality, DRESTRICT_UNIV]
QED
Theorem fmp_mem_writes_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MSTORE; MSTORE8] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = r /\ terminates r ==>
  ?k' r'. step_inst k' C' inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\
        (!v. ~MEM v inst.inst_outputs ==>
             FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
             FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
        (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
           ?y. FLOOKUP t1.vs_vars v = SOME y /\
               (~retpc_var fn v ==>
                fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
                  (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
        ld_memory_agree (fmp_ld_sites sm) eom
          (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
        ld_shared_agree D s.vs_call_ctx.cc_address
          (step_taint inst s s1 tn) s1 t1 /\
        s1.vs_returndata = t1.vs_returndata /\
        ~s1.vs_halted /\ ~t1.vs_halted /\
        s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
        s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
        s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
        s1.vs_block_ctx = s.vs_block_ctx /\
        s1.vs_data_section = s.vs_data_section /\
        s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
        s1.vs_prev_hashes = s.vs_prev_hashes /\
        s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
        t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
        t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
        t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
        t1.vs_block_ctx = t.vs_block_ctx /\
        t1.vs_data_section = t.vs_data_section /\
        t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
        t1.vs_prev_hashes = t.vs_prev_hashes /\
        t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp
    | Halt se => dead_result_rel D r r'
    | Abort ab se => dead_result_rel D r r'
    | _ => F
Proof
  strip_tac >>
  `inst.inst_outputs = []` by metis_tac[fmp_mem_store_outputs] >>
  `?s1. r = OK s1` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
     gvs[AllCaseEqs(), passSimulationDefsTheory.terminates_def] >>
     strip_tac >> gvs[]) >>
  qpat_x_assum `r = OK _` SUBST_ALL_TAC >> simp[] >>
  drule_all fmp_mem_store_step >> strip_tac >>
  qexistsl_tac [`k`,`t1`] >> simp[] >>
  drule_all fmp_mem_store_ghost >> strip_tac >> simp[] >>
  qpat_x_assum `step_inst _ C _ _ = _` mp_tac >>
  qpat_x_assum `step_inst _ C' _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[mstore_def, mstore8_def, write_memory_with_expansion_def] >>
  fs[fmp_stage_rel_def, ld_shared_agree_def]
QED

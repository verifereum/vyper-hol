(* Structural boundary for combined memory, immutable and log effects. *)
Theory o1LowerDloadJointInternalEffects
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointStorageWrite o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRangeRead o1LowerDloadJointAssign o1LowerDloadShared
  o1LowerDloadJointRangeCopy
  o1LowerDloadJointRelation o1LowerDloadEnvironment o1LowerDloadOccurrence
  o1LowerDloadJointScalar o1LowerDloadRelocationKernel
  ptrDiscipline venomState venomExecSemantics venomInst
  memLocDefs words pointerConfinedDefs
  finite_map list pred_set unitShapeDefs o1PassContract venomWf codegenRel contextCodegenRel

Theorem ld_joint_internal_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|> /\
  t1 = t with <|vs_memory := mt; vs_immutables := imt; vs_logs := lt|> /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address tn1 s1 t1 ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, wf_function_def, fn_labels_def]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >> simp[active_inst_def]) >>
  drule_all ld_joint_control_unchanged_next >> strip_tac >>
  qexistsl_tac [`u`,`fn'`] >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  gvs[venom_state_fupdcanon] >>
  simp[ld_joint_boundary_def, venom_state_fupdcanon] >> conj_tac
  >- (qexists_tac `u` >>
      gvs[ld_joint_frame_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def, ld_env_agree_def, op_taint_def] >>
      conj_tac
      >- (qpat_x_assum `ld_joint_control _ _ _ (_ with vs_inst_idx := _) _` mp_tac >>
          simp[NoAsms, ld_joint_control_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
      rpt strip_tac >> metis_tac[]) >>
  gvs[ld_shared_agree_def]
QED

(* Check that both concrete effect shapes enter the combined boundary;
   payload relations remain semantic obligations, not framing assumptions. *)
Theorem ld_internal_effect_update_shapes[local]:
  (?ms ims ls. istore off v s =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>) /\
  (?ms ims ls. (s with vs_logs := s.vs_logs ++ [ev]) =
     s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|>)
Proof
  conj_tac
  >- (qexistsl_tac [`(mstore off v s).vs_memory`,
                   `s.vs_immutables |+ (off,v)`,`s.vs_logs`] >>
      simp[istore_def, mstore_def, venom_state_component_equality]) >>
  qexistsl_tac [`s.vs_memory`,`s.vs_immutables`,`s.vs_logs ++ [ev]`] >>
  simp[venom_state_component_equality]
QED

Theorem ld_shared_istore:
  ld_shared_agree D A tn s t /\ word_agree_except m v w ==>
  ld_shared_agree D A (tn with t_imm := key_update tn.t_imm off m)
    (istore off v s) (istore off w t)
Proof
  simp[ld_shared_agree_def, istore_def, mstore_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `key = off` >>
  gvs[key_update_def, word_agree_except_def, FAPPLY_FUPDATE_THM]
QED

Theorem ld_shared_logs_append:
  ld_shared_agree D A tn s t ==>
  ld_shared_agree D A tn
    (s with vs_logs := s.vs_logs ++ [ev])
    (t with vs_logs := t.vs_logs ++ [ev])
Proof
  simp[ld_shared_agree_def]
QED

Theorem ld_joint_istore_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
  ?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\ op_prov G p = NONE
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[o1LowerDloadGhostTheory.frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `!vv. MEM (Var vv) inst.inst_operands ==> vv NOTIN fn_pv P fn` by
    (qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [fn_ptr_ok_def]) >>
     qpat_x_assum `!ii. MEM ii (fn_insts fn) ==> _` drule >>
     simp[] >> metis_tac[]) >>
  `!op. MEM op inst.inst_operands ==> op_prov H op = NONE` by
    (rpt strip_tac >>
     `op_prov G op = NONE` by
       (Cases_on `op` >> simp[op_prov_def] >>
        rename1 `FLOOKUP G vv` >> Cases_on `FLOOKUP G vv` >> simp[] >>
        fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
       fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
     drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     simp[occurrence_param_ok_def]) >>
  `op_taint tn p = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
  `!vv. ~retpc_use_ok inst vv` by simp[retpc_use_ok_def] >>
  `eval_operand p s = eval_operand p t` by
    (irule ld_joint_operand_clean >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  `?w. eval_operand vop t = SOME w /\
    ld_value_agree sites (op_prov H vop) (op_taint tn vop) v w` by
    (irule ld_joint_operand_value >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc, MEM]) >>
  qexists_tac `w` >> gvs[ld_value_agree_def] >>
  Cases_on `p` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G vv` >> Cases_on `FLOOKUP G vv` >> simp[] >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_joint_istore_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = ISTORE /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [p;vop]` >>
  rename1 `eval_operand p s = SOME x` >>
  rename1 `eval_operand vop s = SOME v` >>
  `?w. eval_operand p t = SOME x /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\ op_prov G p = NONE` by
    (irule ld_joint_istore_operands >> metis_tac[]) >>
  qexists_tac `istore (w2n x) w t` >> simp[] >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  `w2n x+32 <= lo` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, source_memory_write_ranges_def, mem_write_ops_def,
         fixed_source_write_range_def] >>
     Cases_on `p` >> gvs[op_prov_def] >> metis_tac[arithmeticTheory.NOT_LESS]) >>
  conj_tac
  >- (`mem_taint tn inst s (istore (w2n x) v s) =
        ((tn.t_mem DIFF {i | w2n x <= i /\ i < w2n x+32}) UNION
         {w2n x+k | k IN op_taint tn vop})` by
        (simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
              fixed_source_write_range_def, written_taint_def,
              new_site_bytes_def, istore_def, mstore_def, range_bytes_def] >>
         simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
      asm_rewrite_tac[] >>
      drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_mstore_geometry >>
      disch_then irule >> simp[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address
     (tn with t_imm := key_update tn.t_imm (w2n x) (op_taint tn vop))
     (istore (w2n x) v s) (istore (w2n x) w t)` by
    (irule ld_shared_istore >> simp[]) >>
  gvs[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
      ld_shared_agree_def]
QED


Theorem ld_joint_log_scalar[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  MEM op (sz::tops) ==>
  eval_operand op s = eval_operand op t
Proof
  rpt gen_tac >> disch_tac >> gns[] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[o1LowerDloadGhostTheory.frame_reachable_prov_support] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
        metis_tac[MEM_EL]) >> metis_tac[]) >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def,
          mem_read_ops_def] >>
     qexists_tac `vv` >> simp[MEM_REVERSE, REVERSE_APPEND] >>
     Cases_on `p = Var vv` >>
     gvs[FILTER_APPEND_DISTRIB, FILTER_REVERSE, REVERSE_EQ_SING, FILTER_EQ_NIL] >>
     Cases_on `tops` >> gvs[] >>
     IF_CASES_TAC >> gvs[] >>
     strip_tac >>
     qpat_x_assum `_ = [Var vv]` (mp_tac o AP_TERM ``LENGTH : operand list -> num``) >>
     simp[] >> IF_CASES_TAC >> simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[]) >>
  `op_prov H op = NONE` by
    (`occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
       fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
     drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     Cases_on `op_prov H op` >> simp[occurrence_param_ok_def]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gs[taint_ok_def, MEM_REVERSE] >> metis_tac[]) >>
  irule ld_joint_operand_clean >>
  `MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v)` by
    gs[retpc_use_ok_def, MEM_REVERSE] >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]
QED

Theorem ld_joint_log_read[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: REVERSE (p::sz::tops) /\
  LENGTH tops = w2n tc /\ eval_operand p s = SOME x /\
  eval_operand sz s = SOME l /\ eval_operands tops s = SOME topics ==>
  ?y. eval_operand p t = SOME y /\ eval_operand sz t = SOME l /\
    eval_operands tops t = SOME topics /\
    read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t
Proof
  strip_tac >>
  `!op. MEM op (sz::tops) ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> irule ld_joint_log_scalar >> metis_tac[]) >>
  `eval_operand sz t = SOME l` by metis_tac[MEM] >>
  `eval_operands tops s = eval_operands tops t` by
    (qpat_x_assum `!op. MEM op (sz::tops) ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `tops` >>
     simp[eval_operands_def] >> rpt strip_tac >>
     `eval_operand h s = eval_operand h t` by metis_tac[] >>
     `eval_operands tops s = eval_operands tops t` by
       (first_x_assum irule >> gvs[] >> metis_tac[]) >> simp[]) >>
  `eval_operands tops t = SOME topics` by metis_tac[] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {}` by
    (qpat_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, MEM_REVERSE] >> metis_tac[]) >>
  `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def, REVERSE_APPEND] >>
  `?y. eval_operand p t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n x=b+j /\ w2n y=c+j))` by
    (drule ld_joint_read_operand_range >>
     disch_then (qspecl_then [`x`,`<|iao_ofst := p; iao_size := SOME sz; iao_max_size := SOME sz|>`,`p`,`w2n l`] mp_tac) >>
     simp[mem_read_ops_def, REVERSE_APPEND] >>
     disch_then irule >> simp[retpc_use_ok_def, MEM_REVERSE] >>
     Cases_on `tops` >> simp[]) >>
  `!k. k<w2n l ==> w2n x+k NOTIN tn.t_mem` by
    (rpt strip_tac >>
     `w2n x <= w2n x+k /\ w2n x+k < w2n x+w2n l` by decide_tac >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     gvs[taint_ok_def, about_to_revert_def] >>
     disj2_tac >> qexistsl_tac [`w2n x`,`w2n l`,`w2n x+k`] >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qexists_tac `y` >> simp[] >> irule ld_memory_agree_clean_slice >>
  qexistsl_tac [`lo`,`tn.t_mem`,`sites`] >> simp[] >>
  gvs[ld_joint_boundary_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_eval_operands_defined:
  !ops s. IS_SOME (eval_operands ops s) <=>
    EVERY (\op. IS_SOME (eval_operand op s)) ops
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  first_x_assum (qspec_then `s` assume_tac) >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operands ops s` >> gvs[]
QED

Theorem ld_joint_log_step[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = LOG /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  Cases_on `REVERSE rest` >> gvs[] >>
  rename1 `REVERSE rest = p::rr` >>
  Cases_on `rr` >> gvs[] >> rename1 `REVERSE rest = p::szop::tops` >>
  `rest = REVERSE (p::szop::tops)` by metis_tac[REVERSE_REVERSE] >>
  `LENGTH tops = w2n tc` by
    (qpat_x_assum `LENGTH rest = _` mp_tac >> simp[]) >>
  `EVERY (\op. IS_SOME (eval_operand op s)) tops` by
    (qpat_assum `eval_operands tops s = SOME topics` mp_tac >>
     simp[GSYM ld_eval_operands_defined]) >>
  `IS_SOME (eval_operands inst.inst_operands s)` by
    simp[ld_eval_operands_defined, eval_operand_def] >>
  `~s.vs_call_ctx.cc_static` by
    (Cases_on `eval_operands inst.inst_operands s` >> fs[] >> gvs[]) >>
  gvs[] >>
  `?y. eval_operand p t = SOME y /\ eval_operand szop t = SOME sz /\
    eval_operands tops t = SOME topics /\
    read_memory (w2n off) (w2n sz) s = read_memory (w2n y) (w2n sz) t` by
    (irule ld_joint_log_read >> simp[] >> metis_tac[]) >>
  `s.vs_call_ctx = t.vs_call_ctx /\
   ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_local_fields_def] >>
  `~t.vs_call_ctx.cc_static` by metis_tac[] >>
  qexists_tac `t with vs_logs := t.vs_logs ++
    [<|logger := t.vs_call_ctx.cc_address; topics := topics;
       data := read_memory (w2n y) (w2n sz) t|>]` >>
  simp[GSYM read_memory_def] >>
  `new_site_bytes s s = {}` by
    (simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  (conj_tac
  >- (gvs[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
         new_site_bytes_def, written_taint_def, range_bytes_def, FLOOKUP_DEF] >>
      Cases_on `REVERSE tops ++ [szop;p]` >> gvs[] >>
      rename1 `REVERSE tops ++ [szop;p] = hh::tt` >>
      Cases_on `tt` >> gvs[] >> rename1 `_ = hh::hh2::tt2` >>
      Cases_on `tt2` >> gvs[]) >>
  gvs[ld_shared_agree_def, step_taint_def, store_taint_def,
      imm_taint_def, adopt_reset_def])
QED

Theorem ld_joint_internal_effect_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [ISTORE; LOG] /\ step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  strip_tac >>
  `?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1) s1.vs_memory t1.vs_memory /\
    ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1` by
    (Cases_on `inst.inst_opcode = ISTORE`
     >- (irule ld_joint_istore_step >> metis_tac[]) >>
     irule ld_joint_log_step >> gvs[MEM] >> metis_tac[]) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `fn_inst_wf fn` by (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[MEM, inst_wf_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[MEM, is_terminator_def] >>
  `step_prov PG G inst s1 = G /\ occurrence_step a HP H inst s1 = H` by
    simp[step_prov_def, occurrence_step_def, set_prov_def, DRESTRICT_UNIV] >>
  `occ_frame_reachable vs C stk PG G (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[MEM]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[MEM]) >>
  qexists_tac `t1` >> simp[] >>
  `?ms ims ls mt imt lt.
     s1 = s with <|vs_memory := ms; vs_immutables := ims; vs_logs := ls|> /\
     t1 = t with <|vs_memory := mt; vs_immutables := imt; vs_logs := lt|>` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     qpat_x_assum `step_inst fuel C' inst t = _` mp_tac >>
     qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     gvs[MEM] >> simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[exec_write2_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[istore_def, mstore_def] >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  irule ld_joint_internal_update_next >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  conj_tac >- gvs[step_taint_def] >> conj_tac
  >- gvs[ld_joint_boundary_def, ld_joint_frame_def, ld_env_agree_def,
         step_taint_def, set_var_taint_def, DRESTRICT_UNIV, op_taint_def] >>
  metis_tac[]
QED

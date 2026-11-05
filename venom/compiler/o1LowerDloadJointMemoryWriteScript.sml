(* Masked writes under occurrence geometry, including empty protected sites. *)
Theory o1LowerDloadJointMemoryWrite
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointRelation o1LowerDloadMemoryConsumer
  o1LowerDloadRelocationKernel ptrDiscipline venomState words finite_map pred_set codegenRel
  o1LowerDloadJointMemoryRead o1LowerDloadJointScalar o1LowerDloadOccurrence
  o1LowerDloadAddressArithmetic venomExecSemantics list unitShapeDefs memLocDefs
  o1PassContract pointerConfinedDefs venomInst contextCodegenRel
  o1LowerDloadEnvironment o1LowerDloadOpaque venomWf

Theorem ld_memory_agree_mstore_geometry:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\ word_agree_except m v w /\
  ((a = c /\ a+32 <= lo) \/
   (?id b d z j. FLOOKUP sites id = SOME (b,d,z) /\ j+32 <= z /\
     a = b+j /\ c = d+j)) ==>
  ld_memory_agree sites lo
    ((mask DIFF {i | a <= i /\ i < a+32}) UNION {a+k | k IN m})
    (mstore a v s).vs_memory (mstore c w t).vs_memory
Proof
  strip_tac
  >- (gvs[] >> rewrite_tac[ld_memory_agree_def] >> conj_tac
      >- (rpt strip_tac >> simp[ld_mstore_bytes] >>
          Cases_on `a <= i /\ i < a+32`
          >- (`i-a NOTIN m` by (gvs[] >> metis_tac[arithmeticTheory.SUB_ADD]) >>
              gvs[word_agree_except_def]) >>
          simp[] >> irule ld_memory_agree_fixed_byte >>
          qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
      rpt strip_tac >>
      `lo <= b /\ lo <= c` by metis_tac[ld_joint_geometry_def] >>
      `~(a <= b+j /\ b+j < a+32) /\
       ~(a <= c+j /\ c+j < a+32)` by decide_tac >>
      asm_rewrite_tac[ld_mstore_bytes] >>
      irule ld_memory_agree_site_byte >>
      qexistsl_tac [`id`,`lo`,`mask`,`sites`,`z`] >> gvs[]) >>
  gvs[] >>
  `lo <= b /\ lo <= d` by metis_tac[ld_joint_geometry_def] >>
  rewrite_tac[ld_memory_agree_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(b+j <= i /\ i < b+j+32) /\
       ~(d+j <= i /\ i < d+j+32)` by decide_tac >>
      asm_rewrite_tac[ld_mstore_bytes] >>
      irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`,`mask`,`sites`] >> gvs[]) >>
  rpt strip_tac >>
  rename1 `read_byte (sb+k) (mstore (b+j) v s).vs_memory =
    read_byte (tb+k) (mstore (d+j) w t).vs_memory` >>
  rename1 `FLOOKUP sites jd = SOME (sb,tb,sz)` >>
  Cases_on `jd = id`
  >- (gnvs[] >>
      Cases_on `j <= k /\ k < j+32`
      >- (`k = j+(k-j)` by decide_tac >>
          `k-j NOTIN m` by (gvs[] >> metis_tac[]) >>
          qpat_x_assum `word_agree_except _ _ _` mp_tac >>
          simp[word_agree_except_def] >>
          disch_then (qspec_then `k-j` mp_tac) >> simp[ld_mstore_bytes]) >>
      gvs[ld_mstore_bytes] >>
      `k < sz` by decide_tac >>
      fs[ld_memory_agree_def] >> metis_tac[]) >>
  `0 < z /\ 0 < sz` by decide_tac >>
  `(sb+sz <= b \/ b+z <= sb) /\ (tb+sz <= d \/ d+z <= tb)` by
    (qpat_x_assum `ld_joint_geometry _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ld_joint_geometry_def]) >>
     metis_tac[]) >>
  `~(b+j <= sb+k /\ sb+k < b+j+32) /\
   ~(d+j <= tb+k /\ tb+k < d+j+32)` by decide_tac >>
  asm_rewrite_tac[ld_mstore_bytes] >> irule ld_memory_agree_site_byte >>
  qexistsl_tac [`jd`,`lo`,`mask`,`sites`,`sz`] >> gvs[]
QED

Theorem ld_joint_mstore_operands[local]:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME x /\ eval_operand vop s = SOME v ==>
  ?y w. eval_operand p t = SOME y /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\
    ((w2n x = w2n y /\ w2n x+32 <= lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
       w2n x = b+j /\ w2n y = c+j))
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[o1LowerDloadGhostTheory.frame_reachable_prov_support] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def,
           o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
     metis_tac[]) >>
  `op_prov G vop = NONE` by
    (Cases_on `vop` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def,
          mem_read_ops_def] >>
     qexists_tac `vv` >> Cases_on `p = Var vv` >> simp[]) >>
  `!op v. MEM op [p;vop] /\ op = Var v ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var] >>
  `!op v. MEM op [p;vop] /\ op = Var v ==> ~retpc_var fn v` by
    (`!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
     metis_tac[ld_active_operand_non_retpc]) >>
  `?y. eval_operand p t = SOME y /\
    ld_value_agree sites (op_prov H p) (op_taint tn p) x y` by
    (irule ld_joint_operand_value >> metis_tac[MEM]) >>
  `?w. eval_operand vop t = SOME w /\
    ld_value_agree sites (op_prov H vop) (op_taint tn vop) v w` by
    (irule ld_joint_operand_value >> metis_tac[MEM]) >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\
   ld_joint_erasure sites B /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  `op_prov H vop = NONE` by
    (drule occurrence_op_erasure >> disch_then (qspec_then `vop` mp_tac) >>
     Cases_on `op_prov H vop` >> simp[occurrence_param_ok_def]) >>
  `word_agree_except (op_taint tn vop) v w` by
    gvs[ld_value_agree_def] >>
  qexistsl_tac [`y`,`w`] >> simp[] >>
  `lo < w2n x+32 \/ op_prov G p <> NONE ==>
    ?vv b z. p = Var vv /\ FLOOKUP G vv = SOME (b,z) /\
      b <= w2n x /\ w2n x+32 <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, source_memory_write_ranges_def, mem_write_ops_def,
         fixed_source_write_range_def] >>
     metis_tac[]) >>
  drule occurrence_op_erasure >> disch_then (qspec_then `p` assume_tac) >>
  Cases_on `op_prov H p`
  >- (gvs[occurrence_param_ok_def] >>
      `x = y` by metis_tac[ld_value_agree_clean] >> gvs[] >>
      Cases_on `lo < w2n x+32` >> gvs[op_prov_def]) >>
  gvs[occurrence_param_ok_def, ld_value_agree_pointer] >>
  gvs[op_prov_def] >>
  `FLOOKUP B x' = SOME (b,z)` by
    (drule ld_joint_erasure_lookup >> metis_tac[]) >> gvs[] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    metis_tac[ld_joint_geometry_def] >>
  `w2n (x + n2w c - n2w b) = c + (w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`x'`,`b`,`c`,`z`,`w2n x-b`] >> simp[]
QED

Theorem ld_joint_mstore_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MSTORE /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_rename_tac `mstore (w2n x) v s` >>
  rename1 `inst.inst_operands = [p;vop]` >>
  `?y w. eval_operand p t = SOME y /\ eval_operand vop t = SOME w /\
    word_agree_except (op_taint tn vop) v w /\
    ((w2n x = w2n y /\ w2n x+32 <= lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
       w2n x = b+j /\ w2n y = c+j))` by
    (irule ld_joint_mstore_operands >> metis_tac[]) >>
  (qexists_tac `mstore (w2n y) w t` >> conj_tac
  >- (qexists_tac `y` >> simp[] >> qexists_tac `w` >> simp[]) >>
  `mem_taint tn inst s (mstore (w2n x) v s) =
    ((tn.t_mem DIFF {i | w2n x <= i /\ i < w2n x+32}) UNION
     {w2n x+k | k IN op_taint tn vop})` by
    (irule ld_mem_taint_mstore >> simp[] >> metis_tac[w2n_lt]) >>
  asm_rewrite_tac[] >>
  `ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U) /\
   ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory` by
    fs[ld_joint_boundary_def] >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_mstore_geometry >>
  disch_then irule >> simp[] >> metis_tac[])
QED

Theorem ld_joint_memory_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with vs_memory := ms /\ t1 = t with vs_memory := mt /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H /\
  occurrence_annotation_ok n a U B HP H stk PG G
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  tn1.t_var = tn.t_var /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H sites X ts
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_joint_source >> drule occ_frame_reachable_annotation >> simp[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[o1_fn_shape_def, venomWfTheory.wf_function_def,
       fn_labels_def]) >>
  qhdtm_assum `ld_joint_boundary`
    (strip_assume_tac o REWRITE_RULE [ld_joint_boundary_def]) >>
  qhdtm_assum `ld_joint_frame`
    (strip_assume_tac o REWRITE_RULE [ld_joint_frame_def]) >>
  `active_inst fn inst2 (s with vs_inst_idx := SUC s.vs_inst_idx)` by
    (qpat_x_assum `active_inst fn inst2 _` mp_tac >> simp[active_inst_def]) >>
  drule_all o1LowerDloadJointAssignTheory.ld_joint_control_unchanged_next >> strip_tac >>
  qexistsl_tac [`u`,`fn'`] >> simp[] >>
  qpat_x_assum `s1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `t1 = _` SUBST_ALL_TAC >>
  gvs[venom_state_fupdcanon] >>
  simp[ld_joint_boundary_def] >> conj_tac
  >- (qexists_tac `u` >>
      gvs[ld_joint_frame_def, ld_params_agree_def, ld_joint_local_fields_def,
          ld_joint_allocas_def, ld_env_agree_def, op_taint_def] >>
      conj_tac
      >- (qpat_x_assum `ld_joint_control _ _ _ (_ with vs_inst_idx := _) _` mp_tac >>
          simp[NoAsms, ld_joint_control_def] >> strip_tac >> gvs[] >> metis_tac[]) >>
      rpt strip_tac >> metis_tac[]) >>
  gvs[o1LowerDloadSharedTheory.ld_shared_agree_def]
QED

Theorem ld_joint_mstore_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = MSTORE /\ ~in_revert_forward fn s /\
  step_inst fuel C inst s = OK s1 /\
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
  strip_tac >> drule_all ld_joint_mstore_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `fn_inst_wf fn` by (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    gvs[is_terminator_def] >>
  `step_prov PG G inst s1 = G /\ occurrence_step a HP H inst s1 = H` by
    simp[step_prov_def, occurrence_step_def, set_prov_def,
         DRESTRICT_UNIV] >>
  `occ_frame_reachable vs C stk PG G (step_taint inst s s1 tn) fn inst2
     (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H` by
    (drule_all occ_frame_reachable_next >> simp[occurrence_sites_step_def] >> gvs[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G
     (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule occurrence_annotation_next >>
     disch_then (qspecl_then [`s1`,`inst`,`SUC s.vs_inst_idx`,`fuel`,`C`] mp_tac) >>
     simp[occurrence_sites_step_def] >> gvs[]) >>
  qexists_tac `t1` >> simp[] >>
  `?ms mt. s1 = s with vs_memory := ms /\ t1 = t with vs_memory := mt` by
    (qpat_x_assum `step_inst fuel C inst s = _` mp_tac >>
     qpat_x_assum `step_inst fuel C' inst t = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[mstore_def] >> metis_tac[]) >>
  irule ld_joint_memory_update_next >>
  gvs[step_taint_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `tn` >> simp[] >>
  gvs[set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
      DRESTRICT_UNIV]
QED

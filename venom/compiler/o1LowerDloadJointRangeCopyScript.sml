(* Relocated address ranges for ordinary copy instructions. *)
Theory o1LowerDloadJointRangeCopy
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadRangeTransport o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel
  o1LowerDloadAddressArithmetic ptrDiscipline venomState words finite_map
  pred_set list o1PassContract contextCodegenRel venomInst
  pointerConfinedDefs memLocDefs o1LowerDloadOpaque unitShapeDefs codegenRel venomExecSemantics venomWf

Theorem ld_joint_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  (len <> 0 /\ (lo < w2n x+len \/ op_prov G op <> NONE) ==>
   ?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b<=w2n x /\ w2n x+len<=b+z) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  `?y. eval_operand op t = SOME y /\
    ld_value_agree sites (op_prov H op) (op_taint tn op) x y` by
    (irule ld_joint_operand_value >>
     metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]) >>
  qexists_tac `y` >> simp[] >> Cases_on `len=0` >> simp[] >>
  `occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G /\
   ld_joint_erasure sites B /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
  drule occurrence_op_erasure >> disch_then (qspec_then `op` assume_tac) >>
  Cases_on `op_prov H op`
  >- (gvs[occurrence_param_ok_def] >>
      `x=y` by metis_tac[ld_value_agree_clean] >> gvs[] >>
      Cases_on `lo < w2n x+len` >> gvs[op_prov_def]) >>
  gvs[occurrence_param_ok_def, ld_value_agree_pointer] >>
  gvs[op_prov_def] >>
  `FLOOKUP B x' = SOME (b,z)` by
    (drule ld_joint_erasure_lookup >> metis_tac[]) >> gvs[] >>
  `b+z < dimword (:256) /\ c+z < dimword (:256)` by
    metis_tac[ld_joint_geometry_def] >>
  `w2n (x+n2w c-n2w b) = c+(w2n x-b)` by
    (irule lower_dload_translate_endpoint >> simp[] >>
     qexists_tac `z` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`x'`,`b`,`c`,`z`,`w2n x-b`] >> simp[]
QED

Theorem ld_joint_write_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_write_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  drule ld_joint_operand_range >> disch_then irule >> simp[] >> rpt strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  gvs[access_ok_def] >> metis_tac[]
QED

Theorem ld_joint_read_operand_range:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = op /\
  MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v) /\
  op_taint tn op = {} /\ eval_operand op s = SOME x /\
  MEM (w2n x,len) (source_memory_read_ranges inst s) ==>
  ?y. eval_operand op t = SOME y /\
    (len=0 \/ (w2n x=w2n y /\ w2n x+len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  drule ld_joint_operand_range >> disch_then irule >> simp[] >> rpt strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `access_ok lo G fn inst s` by metis_tac[ptr_discipline_def] >>
  gvs[access_ok_def] >> metis_tac[]
QED

Theorem ld_joint_copy_scalar_operand:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/
   inst.inst_opcode = CODECOPY \/ inst.inst_opcode = RETURNDATACOPY) /\
  inst.inst_operands = [dst;src;sz] /\
  (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src)) ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
    metis_tac[o1LowerDloadGhostTheory.frame_reachable_prov_support] >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >>
     `MEM inst (fn_insts fn)` by
       (fs[active_inst_def, fn_insts_def,
           o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
     metis_tac[]) >>
  `op_prov G op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >> rename1 `FLOOKUP G vv` >>
     Cases_on `FLOOKUP G vv` >> simp[] >>
     `vv IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
     qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def,
         mem_read_ops_def] >> qexists_tac `vv` >>
     Cases_on `dst = Var vv` >> Cases_on `src = Var vv` >>
     Cases_on `sz = Var vv` >> simp[] >> rpt strip_tac >> gvs[]) >>
  `op_prov H op = NONE` by
    (`occurrence_env_ok B (a::MAP (\u. u.of_owner) U) H G` by
       fs[ld_joint_boundary_def, occurrence_annotation_ok_def] >>
     drule occurrence_op_erasure >> disch_then (qspec_then `op` mp_tac) >>
     Cases_on `op_prov H op` >> simp[occurrence_param_ok_def]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  irule ld_joint_operand_clean >>
  `MEM op inst.inst_operands /\ (!v. ~retpc_use_ok inst v)` by
    gvs[retpc_use_ok_def] >>
  metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc]
QED

Theorem ld_joint_mcopy_operands:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?d' r'. eval_operand dst t = SOME d' /\ eval_operand src t = SOME r' /\
    eval_operand sz t = SOME l /\
    (w2n l=0 \/ (w2n d=w2n d' /\ w2n d+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n d=b+j /\ w2n d'=c+j)) /\
    (w2n l=0 \/ (w2n r=w2n r' /\ w2n r+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n r=b+j /\ w2n r'=c+j))
Proof
  strip_tac >>
  `eval_operand sz s = eval_operand sz t` by
    (irule ld_joint_copy_scalar_operand >> metis_tac[]) >>
  `eval_operand sz t = SOME l` by metis_tac[] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn dst = {} /\ op_taint tn src = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. ~retpc_use_ok inst v` by simp[retpc_use_ok_def] >>
  `?d'. eval_operand dst t = SOME d' /\
    (w2n l=0 \/ (w2n d=w2n d' /\ w2n d+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n d=b+j /\ w2n d'=c+j))` by
    (drule ld_joint_write_operand_range >> disch_then irule >> simp[] >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
          fixed_source_write_range_def, sized_source_write_range_def, eval_operand_def] >> metis_tac[]) >>
  `?r'. eval_operand src t = SOME r' /\
    (w2n l=0 \/ (w2n r=w2n r' /\ w2n r+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n r=b+j /\ w2n r'=c+j))` by
    (drule ld_joint_read_operand_range >> disch_then irule >> simp[] >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          eval_operand_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_mem_taint_mcopy:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  mem_taint tn inst s (mcopy (w2n d) (w2n r) (w2n l) s) =
    ((tn.t_mem DIFF {i | w2n d<=i /\ i<w2n d+w2n l}) UNION
     {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem})
Proof
  strip_tac >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def,
       new_site_bytes_def, mcopy_def, write_memory_with_expansion_def,
       range_bytes_def] >>
  simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_joint_mcopy_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [dop;rop;lop]`,
          `eval_operand dop s = SOME d`, `eval_operand rop s = SOME r`,
          `eval_operand lop s = SOME l`] >>
  drule_all ld_joint_mcopy_operands >>
  disch_then (qx_choose_then `d'` (qx_choose_then `r'` assume_tac)) >>
  gnvs[] >>
  `mem_taint tn inst s (mcopy (w2n d) (w2n r) (w2n l) s) =
    ((tn.t_mem DIFF {i | w2n d<=i /\ i<w2n d+w2n l}) UNION
     {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem})` by
    (irule ld_mem_taint_mcopy >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def, ld_joint_frame_def, ld_joint_allocas_def] >>
  Cases_on `w2n l=0`
  >- (gvs[mcopy_def] >> irule ld_memory_agree_empty_write >> simp[]) >>
  pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >> BETA_TAC >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_snapshot_copy >>
  disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem ld_joint_mcopy_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\ ~in_revert_forward fn s /\
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
  strip_tac >> drule_all ld_joint_mcopy_step >> strip_tac >>
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
    simp[step_prov_def, occurrence_step_def, set_prov_def, DRESTRICT_UNIV] >>
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
     simp[step_inst_non_invoke] >>
     asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     gvs[mcopy_def, write_memory_with_expansion_def] >> metis_tac[]) >>
  irule ld_joint_memory_update_next >> gvs[step_taint_def] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `tn` >> simp[] >>
  gvs[set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, DRESTRICT_UNIV]
QED

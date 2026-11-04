(* Relocated address ranges for ordinary copy instructions. *)
Theory o1LowerDloadJointRangeCopy
Ancestors
  o1LowerDloadRangeTransport o1LowerDloadJointMemoryWrite
  o1LowerDloadJointRelation o1LowerDloadOccurrence o1LowerDloadJointScalar
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel
  o1LowerDloadAddressArithmetic ptrDiscipline venomState words finite_map
  pred_set list o1PassContract contextCodegenRel venomInst
  pointerConfinedDefs memLocDefs o1LowerDloadOpaque unitShapeDefs codegenRel

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
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by metis_tac[ptr_discipline_def] >>
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

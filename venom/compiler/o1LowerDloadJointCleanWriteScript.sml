(* Normal clean-payload memory-write family. *)
Theory o1LowerDloadJointCleanWrite
Ancestors
  o1LowerDloadPtrDiscipline o1LowerDloadJointRead1 o1LowerDloadShared
  o1LowerDloadJointRangeCopy o1LowerDloadJointRelation o1LowerDloadJointScalar
  o1LowerDloadJointMemoryWrite o1LowerDloadRangeTransport
  o1LowerDloadOccurrence o1LowerDloadEnvironment o1LowerDloadRelocationKernel
  o1LowerDloadOpaque ptrDiscipline pointerConfinedDefs memLocDefs
  unitShapeDefs o1PassContract contextCodegenRel codegenRel venomInst venomWf
  venomState venomExecSemantics words finite_map pred_set list

Theorem ld_joint_clean_write_scalar:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  (((inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = CODECOPY \/
     inst.inst_opcode = RETURNDATACOPY) /\
     inst.inst_operands = [dst;src;sz] /\ MEM op [src;sz]) \/
   (inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [dst;op]) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
     MEM op [addr;src;sz])) ==>
  eval_operand op s = eval_operand op t
Proof
  rpt gen_tac >> disch_tac >> gns[] >>
  Cases_on `(inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = CODECOPY \/
     inst.inst_opcode = RETURNDATACOPY) /\
     inst.inst_operands = [dst;src;sz] /\ MEM op [src;sz]`
  >- (gvs[] >> drule ld_joint_copy_scalar_operand >> disch_then irule >>
      simp[] >> metis_tac[]) >>
  gs[] >>
  (`frame_reachable vs C stk PG G tn fn inst s` by
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
         Cases_on `dst = Var vv` >> Cases_on `addr = Var vv` >>
         Cases_on `src = Var vv` >> Cases_on `sz = Var vv` >>
         simp[] >> rpt strip_tac >> gvs[]) >>
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
      metis_tac[ld_active_operand_ir_var, ld_active_operand_non_retpc])
QED

Theorem ld_joint_clean_write_payload_fields:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata /\
  s.vs_code = t.vs_code /\ s.vs_returndata = t.vs_returndata /\
  (!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code)
Proof
  strip_tac >>
  `ld_joint_local_fields s t /\
   ld_shared_agree D s.vs_call_ctx.cc_address tn s t /\
   s.vs_returndata = t.vs_returndata` by
    fs[ld_joint_boundary_def, ld_joint_frame_def] >>
  drule ld_shared_account_observations >>
  fs[ld_joint_local_fields_def]
QED

Theorem ld_joint_clean_write_destination:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  (((inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = CODECOPY \/
     inst.inst_opcode = RETURNDATACOPY) /\
     inst.inst_operands = [dst;src;sz] /\ eval_operand src s = SOME r /\
     eval_operand sz s = SOME l /\ len=w2n l) \/
   (inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [dst;value] /\
     eval_operand value s = SOME v /\ len=1) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
     eval_operand addr s = SOME av /\ eval_operand src s = SOME r /\
     eval_operand sz s = SOME l /\ len=w2n l)) /\
  eval_operand dst s = SOME d ==>
  ?d'. eval_operand dst t = SOME d' /\
    (len=0 \/ (w2n d=w2n d' /\ w2n d+len<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n d=b+j /\ w2n d'=c+j))
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection, ptr_discipline_def] >>
  `op_taint tn dst = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> gvs[taint_ok_def] >> metis_tac[]) >>
  drule ld_joint_write_operand_range >> disch_then irule >> simp[] >>
  gvs[mem_write_ops_def, source_memory_write_ranges_def,
      fixed_source_write_range_def, sized_source_write_range_def,
      retpc_use_ok_def, eval_operand_def] >> metis_tac[]
QED

Theorem ld_joint_clean_write_execution:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MSTORE8;CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C inst s = OK s1 ==>
  ?p q xs. s1 = write_memory_with_expansion p xs s /\
    step_inst fuel C' inst t = OK (write_memory_with_expansion q xs t) /\
    source_memory_write_ranges inst s = [(p,LENGTH xs)] /\
    (LENGTH xs=0 \/ (p=q /\ p+LENGTH xs<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+LENGTH xs<=z /\
                    p=b+j /\ q=c+j))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata /\
   s.vs_code = t.vs_code /\ s.vs_returndata = t.vs_returndata /\
   (!addr. (lookup_account addr s.vs_accounts).code =
           (lookup_account addr t.vs_accounts).code)` by
    metis_tac[ld_joint_clean_write_payload_fields] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  fs[] >>
  (simp[step_inst_non_invoke] >>
   asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
   simp[exec_write2_def, AllCaseEqs()] >> strip_tac >> gvs[]) 
  >~ [`inst.inst_opcode = MSTORE8`]
  >- (rename [`inst.inst_operands = [dop;vop]`,
              `eval_operand dop s = SOME d`, `eval_operand vop s = SOME v`] >>
      `eval_operand vop s = eval_operand vop t` by
        (drule ld_joint_clean_write_scalar >> disch_then irule >> simp[] >> metis_tac[]) >>
      `?d'. eval_operand dop t = SOME d' /\
        ((w2n d=w2n d' /\ w2n d+1<=lo) \/
         (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+1<=z /\
                        w2n d=b+j /\ w2n d'=c+j))` by
        (drule ld_joint_clean_write_destination >> simp[] >> metis_tac[]) >>
      `eval_operand vop t = SOME v` by metis_tac[] >>
      qexistsl_tac [`w2n d`,`w2n d'`,`[w2w v : word8]`] >>
      gvs[mstore8_def, write_memory_with_expansion_def,
           source_memory_write_ranges_def, fixed_source_write_range_def] >> metis_tac[w2n_11])
  >~ [`inst.inst_opcode = EXTCODECOPY`]
  >- suspend "extcopy"
  >> rename [`inst.inst_operands = [dop;rop;lop]`,
             `eval_operand dop s = SOME d`, `eval_operand rop s = SOME r`,
             `eval_operand lop s = SOME l`] >>
  `eval_operand rop t = SOME r /\ eval_operand lop t = SOME l` by
    (`eval_operand rop s = eval_operand rop t /\
      eval_operand lop s = eval_operand lop t` by
       (conj_tac >> drule ld_joint_clean_write_scalar >> disch_then irule >>
        simp[] >> metis_tac[]) >> metis_tac[]) >>
  `?d'. eval_operand dop t = SOME d' /\
    (w2n l=0 \/ (w2n d=w2n d' /\ w2n d+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n d=b+j /\ w2n d'=c+j))` by
    (drule ld_joint_clean_write_destination >> disch_then irule >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) bytes s` >>
  `LENGTH bytes = w2n l` by
    (simp[Abbr `bytes`, LENGTH_TAKE] >> gvs[] >> decide_tac) >>
  qexistsl_tac [`w2n d`,`w2n d'`,`bytes`] >>
  simp[Abbr `bytes`, source_memory_write_ranges_def, sized_source_write_range_def] >>
  gvs[LENGTH_TAKE] >> metis_tac[w2n_11]
QED

Resume ld_joint_clean_write_execution[extcopy]:
  rename [`inst.inst_operands = [aop;dop;rop;lop]`,
          `eval_operand aop s = SOME av`, `eval_operand dop s = SOME d`,
          `eval_operand rop s = SOME r`, `eval_operand lop s = SOME l`] >>
  `!op. MEM op [aop;rop;lop] ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule ld_joint_clean_write_scalar >> disch_then irule >> simp[] >> fs[]) >>
  `eval_operand aop t = SOME av /\ eval_operand rop t = SOME r /\
   eval_operand lop t = SOME l` by metis_tac[MEM] >>
  `?d'. eval_operand dop t = SOME d' /\
    (w2n l=0 \/ (w2n d=w2n d' /\ w2n d+w2n l<=lo) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+w2n l<=z /\
                    w2n d=b+j /\ w2n d'=c+j))` by
    (drule ld_joint_clean_write_destination >> disch_then irule >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) bytes s` >>
  `LENGTH bytes = w2n l` by simp[Abbr `bytes`, LENGTH_TAKE] >>
  qexistsl_tac [`w2n d`,`w2n d'`,`bytes`] >>
  simp[Abbr `bytes`, source_memory_write_ranges_def, sized_source_write_range_def] >>
  gvs[LENGTH_TAKE] >> metis_tac[w2n_11]
QED

Finalise ld_joint_clean_write_execution

Theorem ld_mem_taint_clean_write:
  MEM inst.inst_opcode [MSTORE8;CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY] /\
  source_memory_write_ranges inst s = [(p,LENGTH xs)] ==>
  mem_taint tn inst s (write_memory_with_expansion p xs s) =
    tn.t_mem DIFF {i | p<=i /\ i<p+LENGTH xs}
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by
    (fs[] >> Cases_on `inst.inst_operands` >> simp[written_taint_def] >>
     rename1 `inst.inst_operands = _::rest` >> Cases_on `rest` >> simp[written_taint_def] >>
     rename1 `inst.inst_operands = _::_::rest2` >> Cases_on `rest2` >> simp[written_taint_def] >>
     rename1 `inst.inst_operands = _::_::_::rest3` >> Cases_on `rest3` >> simp[written_taint_def]) >>
  fs[] >>
  simp[mem_taint_def, step_writes_def, new_site_bytes_def,
       write_memory_with_expansion_def, range_bytes_def] >>
  simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_joint_clean_write_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MSTORE8;CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY] /\
  step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory /\
    (?ms mt. s1 = s with vs_memory := ms /\ t1 = t with vs_memory := mt)
Proof
  strip_tac >> drule_all ld_joint_clean_write_execution >>
  disch_then (qx_choose_then `p` (qx_choose_then `q` (qx_choose_then `xs` assume_tac))) >>
  gnvs[] >>
  `ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
   ld_joint_geometry sites X lo (a::MAP (\u. u.of_owner) U)` by
    fs[ld_joint_boundary_def] >>
  `mem_taint tn inst s (write_memory_with_expansion p xs s) =
    tn.t_mem DIFF {i | p<=i /\ i<p+LENGTH xs}` by
    (irule ld_mem_taint_clean_write >> simp[]) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (Cases_on `LENGTH xs=0`
      >- (gvs[] >> irule ld_memory_agree_empty_write >> simp[]) >>
      drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_clean_write >>
      disch_then irule >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`(write_memory_with_expansion p xs s).vs_memory`,
                `(write_memory_with_expansion q xs t).vs_memory`] >>
  simp[write_memory_with_expansion_def]
QED

Theorem ld_joint_clean_write_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [MSTORE8;CALLDATACOPY;CODECOPY;RETURNDATACOPY;EXTCODECOPY] /\
  ~in_revert_forward fn s /\ step_inst fuel C inst s = OK s1 /\
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
  strip_tac >> drule_all ld_joint_clean_write_step >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    metis_tac[ld_joint_source] >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    gvs[ld_joint_boundary_def] >>
  `MEM fn C.ctx_functions` by
    (drule occ_frame_reachable_annotation >> simp[]) >>
  `fn_inst_wf fn` by (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by (fs[] >> gvs[inst_wf_def]) >>
  `~MEM inst.inst_opcode [DLOAD;DLOADBYTES] /\
   ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (fs[] >> gvs[is_terminator_def]) >>
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
  qexists_tac `t1` >> simp[IgnAsm `s1 = _`, IgnAsm `t1 = _`] >>
  irule ld_joint_memory_update_next >> gvs[step_taint_def] >>
  (conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
   qexists_tac `tn` >> simp[] >>
   gvs[set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, DRESTRICT_UNIV])
QED

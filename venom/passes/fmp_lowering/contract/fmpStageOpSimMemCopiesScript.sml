(* Memory copy instructions in the FMP stage simulation. *)
Theory fmpStageOpSimMemCopies
Ancestors
  fmpStageOpSimMemSupport fmpStageOpSimMemReads fmpStageOpBase fmpStageRel
  o1LowerDloadRangeTransport o1LowerDloadMemoryConsumer o1LowerDloadShared
  o1LowerDloadRelocationKernel o1PassContract ptrDiscipline ptrStaticDiscipline
  contextCodegenRel codegenRel unitShapeDefs venomExecSemantics venomWf
  venomState venomInst vfmState memLocDefs pointerConfinedDefs words byte finite_map pred_set list

Theorem fmp_mem_copy_scalar_prov[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ((MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
    inst.inst_operands = [dst;src;sz] /\
    (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src))) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
    MEM op [addr;src;sz])) ==>
  op_prov G op = NONE
Proof
  strip_tac >>
  `MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
   ?P. EVERY (fn_static_ptr_ok P) C.ctx_functions` by
    metis_tac[fmp_stage_frame_facts] >>
  `FDOM G SUBSET fn_pv P fn` by metis_tac[fmp_stage_prov_support] >>
  `ptr_use_static_ok P (fn_pv P fn) inst` by
    fs[EVERY_MEM, fn_static_ptr_ok_def] >>
  Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN fn_pv P fn` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  qpat_x_assum `!v'. _` (qspec_then `v` mp_tac) >>
  Cases_on `dst = Var v` >> Cases_on `src = Var v` >>
  gvs[boolTheory.bool_case_eq] >> simp[FORALL_inst_access_ops]
QED

Theorem fmp_mem_copy_scalar[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ((MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
    inst.inst_operands = [dst;src;sz] /\
    (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src))) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
    MEM op [addr;src;sz])) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  strip_tac >>
  `op_prov G op = NONE` by metis_tac[fmp_mem_copy_scalar_prov] >>
  `taint_ok fn tn inst s` by metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `MEM op inst.inst_operands /\ inst.inst_opcode <> PHI /\
   (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    metis_tac[fmp_mem_operand_non_retpc] >>
  metis_tac[fmp_mem_operand_clean]
QED

Theorem fmp_mem_copy_range[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  ((MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
    inst.inst_operands = [dst;src;sz]) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
    eval_operand addr s <> NONE)) /\
  (op = dst \/ (inst.inst_opcode = MCOPY /\ op = src)) /\
  eval_operand dst s <> NONE /\
  eval_operand op s = SOME x /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?y. eval_operand op t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  `taint_ok fn tn inst s /\ access_ok eom G fn inst s` by
    metis_tac[fmp_stage_frame_facts] >>
  `op_taint tn op = {}` by (fs[taint_ok_def] >> gvs[] >> metis_tac[]) >>
  `MEM op inst.inst_operands /\ inst.inst_opcode <> PHI /\
   (!v. ~retpc_use_ok inst v)` by gvs[retpc_use_ok_def] >>
  `!v. op = Var v ==> ~retpc_var fn v` by
    metis_tac[fmp_mem_operand_non_retpc] >>
  `w2n l <> 0 /\ (eom < w2n x+w2n l \/ op_prov G op <> NONE) ==>
   ?v b z. op = Var v /\ FLOOKUP G v = SOME (b,z) /\
     b <= w2n x /\ w2n x+w2n l <= b+z` by
    (fs[access_ok_def, mem_write_ops_def, mem_read_ops_def,
        source_memory_write_ranges_def, source_memory_read_ranges_def,
        sized_source_write_range_def, memory_range_of_operands_def] >>
     Cases_on `eval_operand dst s` >> gvs[] >>
     Cases_on `eval_operand addr s` >> gvs[] >> metis_tac[]) >>
  drule_all fmp_mem_operand_range >> simp[]
QED

Theorem fmp_mem_copy_destination[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
  inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME x /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?y. eval_operand dst t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  mp_tac (Q.INST [`op` |-> `dst`, `addr` |-> `dst`]
    (SPEC_ALL fmp_mem_copy_range)) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem fmp_mem_mcopy_source[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME x /\
  eval_operand sz s = SOME l ==>
  ?y. eval_operand src t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >>
  mp_tac (Q.INST [`op` |-> `src`, `addr` |-> `dst`, `r` |-> `x`]
    (SPEC_ALL fmp_mem_copy_range)) >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem fmp_mem_mcopy_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = MCOPY /\
  step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    ld_memory_agree (fmp_ld_sites sm) eom (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [dst;src;sz]`,
          `eval_operand dst s = SOME d`, `eval_operand src s = SOME r`,
          `eval_operand sz s = SOME l`] >>
  `eval_operand sz t = SOME l` by
    (irule fmp_mem_copy_scalar >> simp[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES]` by simp[] >>
  drule_all fmp_mem_copy_destination >>
  disch_then (qx_choose_then `dt` assume_tac) >>
  drule_all fmp_mem_mcopy_source >>
  disch_then (qx_choose_then `rt` assume_tac) >> gnvs[] >>
  `mem_taint tn inst s (mcopy (w2n d) (w2n r) (w2n l) s) =
    ((tn.t_mem DIFF {i | w2n d<=i /\ i<w2n d+w2n l}) UNION
     {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem})` by
    (simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def, new_site_bytes_def,
       mcopy_def, write_memory_with_expansion_def, range_bytes_def,
       EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by metis_tac[fmp_mem_geometry] >>
  Cases_on `w2n l=0`
  >- (gvs[mcopy_def] >> irule ld_memory_agree_empty_write >> simp[]) >>
  pure_rewrite_tac[mcopy_def, GSYM read_memory_def, LET_THM] >> BETA_TAC >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_snapshot_copy >>
  disch_then irule >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_copy_fields[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata /\
  (!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code)
Proof
  strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  drule ld_shared_accounts_fields >> strip_tac >>
  `!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code` by
    (gen_tac >> first_x_assum (qspec_then `addr` mp_tac) >>
     simp[lookup_account_def] >> simp[vfmStateTheory.account_state_component_equality]) >>
  fs[fmp_stage_rel_def, fmp_frame_rel_def]
QED

Theorem fmp_mem_extcopy_destination[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [addr;dst;src;sz] /\ eval_operand addr s = SOME a /\
  eval_operand dst s = SOME x /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?y. eval_operand dst t = SOME y /\
    (w2n l=0 \/ (w2n x=w2n y /\ w2n x+w2n l<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l<=z /\ w2n x=b+j /\ w2n y=c+j))
Proof
  strip_tac >> mp_tac (Q.INST [`op` |-> `dst`] (SPEC_ALL fmp_mem_copy_range)) >> simp[]
QED

Theorem fmp_mem_clean_copy_execution[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
  step_inst k C inst s = OK s1 ==>
  ?p q xs. s1 = write_memory_with_expansion p xs s /\
    step_inst k C' inst t = OK (write_memory_with_expansion q xs t) /\
    source_memory_write_ranges inst s = [(p,LENGTH xs)] /\
    (LENGTH xs=0 \/ (p=q /\ p+LENGTH xs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+LENGTH xs<=z /\ p=b+j /\ q=c+j))
Proof
  strip_tac >> drule fmp_mem_copy_fields >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [dst;src;sz]`,
          `eval_operand dst s = SOME d`, `eval_operand src s = SOME r`,
          `eval_operand sz s = SOME l`] >>
  `eval_operand src t = SOME r /\ eval_operand sz t = SOME l` by
    (conj_tac
     >- (mp_tac (Q.INST [`op` |-> `src`, `addr` |-> `dst`, `x` |-> `r`]
           (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
     mp_tac (Q.INST [`op` |-> `sz`, `addr` |-> `dst`, `x` |-> `l`]
       (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  `MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES]` by simp[] >>
  drule_all fmp_mem_copy_destination >>
  disch_then (qx_choose_then `dt` assume_tac) >> gnvs[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) bytes s` >>
  `LENGTH bytes = w2n l` by (simp[Abbr `bytes`, LENGTH_TAKE] >> gvs[] >> decide_tac) >>
  qexistsl_tac [`w2n d`,`w2n dt`,`bytes`] >>
  simp[Abbr `bytes`, source_memory_write_ranges_def, sized_source_write_range_def] >>
  gvs[LENGTH_TAKE] >> metis_tac[w2n_11]
QED

Theorem fmp_mem_extcopy_execution[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ inst.inst_opcode = EXTCODECOPY /\
  step_inst k C inst s = OK s1 ==>
  ?p q xs. s1 = write_memory_with_expansion p xs s /\
    step_inst k C' inst t = OK (write_memory_with_expansion q xs t) /\
    source_memory_write_ranges inst s = [(p,LENGTH xs)] /\
    (LENGTH xs=0 \/ (p=q /\ p+LENGTH xs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+LENGTH xs<=z /\ p=b+j /\ q=c+j))
Proof
  strip_tac >> drule fmp_mem_copy_fields >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [addr;dst;src;sz]`,
          `eval_operand addr s = SOME a`, `eval_operand dst s = SOME d`,
          `eval_operand src s = SOME r`, `eval_operand sz s = SOME l`] >>
  `eval_operand addr t = SOME a` by
    (mp_tac (Q.INST [`op` |-> `addr`, `x` |-> `a`]
      (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  `eval_operand src t = SOME r` by
    (mp_tac (Q.INST [`op` |-> `src`, `x` |-> `r`]
      (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  `eval_operand sz t = SOME l` by
    (mp_tac (Q.INST [`op` |-> `sz`, `x` |-> `l`]
      (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  drule_all fmp_mem_extcopy_destination >>
  disch_then (qx_choose_then `dt` assume_tac) >> gnvs[] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) bytes s` >>
  `LENGTH bytes = w2n l` by simp[Abbr `bytes`] >>
  qexistsl_tac [`w2n d`,`w2n dt`,`bytes`] >>
  simp[Abbr `bytes`, source_memory_write_ranges_def, sized_source_write_range_def] >>
  metis_tac[w2n_11]
QED

Theorem fmp_mem_all_clean_execution[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  step_inst k C inst s = OK s1 ==>
  ?p q xs. s1 = write_memory_with_expansion p xs s /\
    step_inst k C' inst t = OK (write_memory_with_expansion q xs t) /\
    source_memory_write_ranges inst s = [(p,LENGTH xs)] /\
    (LENGTH xs=0 \/ (p=q /\ p+LENGTH xs<=eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+LENGTH xs<=z /\ p=b+j /\ q=c+j))
Proof
  strip_tac >> Cases_on `inst.inst_opcode = EXTCODECOPY`
  >- (drule_all fmp_mem_extcopy_execution >> simp[]) >>
  `MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES]` by fs[] >>
  drule_all fmp_mem_clean_copy_execution >> simp[]
QED

Theorem fmp_mem_clean_copy_step:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  step_inst k C inst s = OK s1 ==>
  ?t1. step_inst k C' inst t = OK t1 /\
    ld_memory_agree (fmp_ld_sites sm) eom (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  strip_tac >> drule_all fmp_mem_all_clean_execution >>
  disch_then (qx_choose_then `p` (qx_choose_then `q` (qx_choose_then `xs` assume_tac))) >>
  gnvs[] >>
  `mem_taint tn inst s (write_memory_with_expansion p xs s) =
   tn.t_mem DIFF {i | p<=i /\ i<p+LENGTH xs}` by
    (simp[mem_taint_def, step_writes_def, written_taint_def, new_site_bytes_def,
          write_memory_with_expansion_def, range_bytes_def, EXTENSION, FLOOKUP_DEF] >>
     fs[] >> simp[SF CONJ_ss] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     rename1 `h::tl` >> Cases_on `tl` >> simp[] >>
     rename1 `h::h1::tl` >> Cases_on `tl` >> simp[] >>
     rename1 `h::h1::h2::tl` >> Cases_on `tl` >> simp[]) >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
    fs[fmp_stage_rel_def] >>
  `ld_joint_geometry (fmp_ld_sites sm) FEMPTY eom
    (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by metis_tac[fmp_mem_geometry] >>
  simp[] >>
  Cases_on `LENGTH xs=0`
  >- (gvs[] >> irule ld_memory_agree_empty_write >> simp[]) >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_clean_write >>
  disch_then irule >> simp[] >> metis_tac[LENGTH_NIL]
QED

Theorem fmp_mem_copy_outputs[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] ==>
  inst.inst_outputs = []
Proof
  strip_tac >>
  `MEM inst (fn_insts fn) /\ o1_fn_shape C fn` by metis_tac[fmp_stage_frame_facts] >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[]) >>
  gvs[inst_wf_def]
QED

Theorem fmp_mem_copy_frame[local]:
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  step_inst k C inst s = OK s1 ==>
  (s1 with vs_memory := s.vs_memory) = s
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem fmp_mem_copy_exception[local]:
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  step_inst k C inst s = r /\ terminates r /\ ~(?s1. r = OK s1) ==>
  inst.inst_opcode = RETURNDATACOPY /\
  ?dst src sz d x l. inst.inst_operands = [dst;src;sz] /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME x /\
    eval_operand sz s = SOME l /\ LENGTH s.vs_returndata < w2n x + w2n l /\
    r = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >> Cases_on `r` >> gvs[passSimulationDefsTheory.terminates_def] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >> fs[] >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_mem_copy_abort[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  step_inst k C inst s = r /\ terminates r /\ ~(?s1. r = OK s1) ==>
  ?r'. step_inst k C' inst t = r' /\ dead_result_rel D r r'
Proof
  strip_tac >> drule_all fmp_mem_copy_exception >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [dst;src;sz]`, `eval_operand src s = SOME x`,
          `eval_operand sz s = SOME l`] >>
  `eval_operand src t = SOME x` by
    (mp_tac (Q.INST [`op` |-> `src`, `addr` |-> `dst`]
      (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  `eval_operand sz t = SOME l` by
    (mp_tac (Q.INST [`op` |-> `sz`, `addr` |-> `dst`, `x` |-> `l`]
      (SPEC_ALL fmp_mem_copy_scalar)) >> simp[]) >>
  `MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES]` by simp[] >>
  drule_all fmp_mem_copy_destination >> strip_tac >>
  drule fmp_mem_copy_fields >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  fs[fmp_stage_rel_def, ld_shared_agree_def, dead_result_rel_def,
     halt_state_def, set_returndata_def]
QED

Theorem fmp_mem_copies_sim:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~in_revert_forward fn s /\
  MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
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
  strip_tac >> Cases_on `?s1. r = OK s1`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      `?t1. step_inst k C' inst t = OK t1 /\
        ld_memory_agree (fmp_ld_sites sm) eom (mem_taint tn inst s s1)
          s1.vs_memory t1.vs_memory` by
        (Cases_on `inst.inst_opcode = MCOPY`
         >- metis_tac[fmp_mem_mcopy_step] >>
         `MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY]` by fs[] >>
         metis_tac[fmp_mem_clean_copy_step]) >>
      `inst.inst_outputs = []` by metis_tac[fmp_mem_copy_outputs, MEM] >>
      `s1 with vs_memory := s.vs_memory = s` by metis_tac[fmp_mem_copy_frame, MEM] >>
      `t1 with vs_memory := t.vs_memory = t` by metis_tac[fmp_mem_copy_frame, MEM] >>
      qexistsl_tac [`k`,`t1`] >> simp[] >>
      fs[venom_state_component_equality, step_taint_def, store_taint_def,
         adopt_reset_def, imm_taint_def, fmp_stage_rel_def, ld_shared_agree_def]) >>
  drule_all fmp_mem_copy_abort >> strip_tac >>
  qexistsl_tac [`k`,`r'`] >> simp[] >>
  drule_all fmp_mem_copy_exception >> strip_tac >> gvs[]
QED

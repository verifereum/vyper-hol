(* Concrete ordinary memory effects at a related FMP cut point. *)
Theory gasFocusFmpCutMemoryEffect
Ancestors fmpStageOpSimMemReads[qualified] arithmetic[qualified,ignore_grammar]
  fmpStageRel o1LowerDloadRangeTransport lowerDloadSafetyBytes contextCodegenRel
  o1LowerDloadMemoryConsumer o1LowerDloadRelocationKernel codegenRel
  o1LowerDloadShared fmpStagePointRanges ptrStaticDiscipline frameRelocationCleanOperands
  memLocDefs pointerConfinedDefs venomWf passSimulationDefs
  ptrDiscipline venomExecSemantics venomState venomInst finite_map pred_set list words byte

Theorem focus_fmp_cut_word_read[local]:
  MEM inst.inst_opcode [MLOAD; ILOAD] /\
  inst.inst_operands = [p] /\ inst.inst_outputs = [v] /\
  eval_operand p s = SOME x /\ eval_operand p t = SOME y /\
  ld_memory_agree sites eom M s.vs_memory t.vs_memory /\
  ((w2n x = w2n y /\ w2n x + 32 <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + 32 <= z /\ w2n x = b+j /\ w2n y = c+j)) ==>
  step_inst_base inst s = OK (update_var v (mload (w2n x) s) s) /\
  step_inst_base inst t = OK (update_var v (mload (w2n y) t) t) /\
  word_agree_except (mem_word_taint M (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, exec_read1_def] >>
  irule ld_mload_masked >> simp[mem_word_taint_def] >> rpt strip_tac >>
  irule ld_memory_agree_slice_element >> simp[] >>
  qexistsl_tac [`eom`,`M`,`sites`] >> simp[] >> metis_tac[]
QED

Theorem focus_fmp_cut_sha3_read[local]:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [p;sz] /\
  inst.inst_outputs = [v] /\
  eval_operand p s = SOME x /\ eval_operand p t = SOME y /\
  eval_operand sz s = SOME l /\ eval_operand sz t = SOME l /\
  taint_ok fn tn inst s /\ ~in_revert_forward fn s /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  (w2n l = 0 \/ (w2n x = w2n y /\ w2n x + w2n l <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + w2n l <= z /\ w2n x = b+j /\ w2n y = c+j)) ==>
  ?w. step_inst_base inst s = OK (update_var v w s) /\
      step_inst_base inst t = OK (update_var v w t)
Proof
  strip_tac >>
  `read_memory (w2n x) (w2n l) s = read_memory (w2n y) (w2n l) t` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     `MEM (w2n x,w2n l) (source_memory_read_ranges inst s)` by
       simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
     `MEM inst.inst_opcode [SHA3;LOG;CREATE;CREATE2]` by simp[] >>
     `w2n x+x' NOTIN tn.t_mem` by metis_tac[taint_ok_observation_read] >>
     metis_tac[ld_memory_agree_slice_element]) >>
  gvs[step_inst_base_opcode_eqs, GSYM read_memory_def]
  >> (metis_tac[])
QED

Theorem focus_fmp_cut_mstore_agree[local]:
  ld_joint_geometry sites X eom owners /\
  ld_memory_agree sites eom M s.vs_memory t.vs_memory /\
  word_agree_except mask v w /\
  ((p=q /\ p+32<=eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j+32<=z /\ p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites eom
    ((M DIFF {i | p<=i /\ i<p+32}) UNION {p+k | k IN mask})
    (mstore p v s).vs_memory (mstore q w t).vs_memory
Proof
  strip_tac >>
  `ld_memory_agree sites eom
    ((M DIFF {i | p<=i /\ i<p+32}) UNION {p+k | k<32 /\ k IN mask})
    (write_memory_with_expansion p (word_to_bytes v T) s).vs_memory
    (write_memory_with_expansion q (word_to_bytes w T) t).vs_memory` by
      (irule ld_memory_agree_write_geometry >>
       goal_assum (drule_at Any) >> simp[dimword_def] >>
       fs[word_agree_except_def] >> metis_tac[]) >>
  gvs[mstore_def, write_memory_with_expansion_def, dimword_def] >>
  irule ld_memory_agree_mono >> goal_assum (drule_at Any) >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem focus_fmp_cut_store[local]:
  MEM inst.inst_opcode [MSTORE;MSTORE8] /\ inst.inst_operands = [p;valop] /\
  eval_operand p s = SOME x /\ eval_operand p t = SOME y /\
  eval_operand valop s = SOME v /\ eval_operand valop t = SOME w /\
  (if inst.inst_opcode = MSTORE then word_agree_except (op_taint tn valop) v w
   else v = w) /\
  len = (if inst.inst_opcode = MSTORE then 32 else 1) /\
  ld_joint_geometry sites (X : num # num |-> 256 # num) eom owners /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  ((w2n x = w2n y /\ w2n x + len <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + len <= z /\ w2n x = b+j /\ w2n y = c+j)) /\
  step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_memory_agree sites eom (step_taint inst s s1 tn).t_mem
      s1.vs_memory t1.vs_memory /\
    (s1 with vs_memory := s.vs_memory) = s /\
    (t1 with vs_memory := t.vs_memory) = t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst.inst_opcode = MSTORE`
  >- ((gnvs[step_inst_base_opcode_eqs, exec_write2_def] >>
      `mem_taint tn inst s (mstore (w2n x) v s) =
        (tn.t_mem DIFF {i | w2n x<=i /\ i<w2n x+32}) UNION
        {w2n x+k | k IN op_taint tn valop}` by
          (irule ld_mem_taint_mstore >> simp[w2n_lt] >> metis_tac[]) >>
      `ld_memory_agree sites eom (mem_taint tn inst s (mstore (w2n x) v s))
        (mstore (w2n x) v s).vs_memory (mstore (w2n y) w t).vs_memory` by
          (asm_rewrite_tac[] >> metis_tac[focus_fmp_cut_mstore_agree]) >>
      simp[step_taint_def, mstore_def] >> (gvs[venomStateTheory.mstore_def]))) >>
  qexists_tac `mstore8 (w2n y) w t` >>
  gnvs[step_inst_base_opcode_eqs, exec_write2_def] >>
  rename1 `eval_operand valop s = SOME value` >>
  `mem_taint tn inst s (mstore8 (w2n x) value s) =
    tn.t_mem DIFF {i | w2n x<=i /\ i<w2n x+1}` by
      simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, written_taint_def, new_site_bytes_def,
        mstore8_def, range_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `ld_memory_agree sites eom (tn.t_mem DIFF {i | w2n x<=i /\ i<w2n x+1})
    (write_memory_with_expansion (w2n x) [(w2w value : word8)] s).vs_memory
    (write_memory_with_expansion (w2n y) [(w2w value : word8)] t).vs_memory` by
      (irule (SRULE [] (Q.INST [`xs` |-> `[(w2w value : word8)]`]
         (SPEC_ALL ld_memory_agree_clean_write))) >> simp[w2n_11] >>
       qexistsl_tac [`X`,`owners`] >> simp[]) >>
  gvs[step_taint_def, mstore8_def, write_memory_with_expansion_def]
QED

Theorem focus_fmp_cut_mcopy[local]:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand dst t = SOME dt /\
  eval_operand src s = SOME r /\ eval_operand src t = SOME rt /\
  eval_operand sz s = SOME l /\ eval_operand sz t = SOME l /\
  ld_joint_geometry sites (X : num # num |-> 256 # num) eom owners /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  (w2n l = 0 \/ (w2n d = w2n dt /\ w2n d + w2n l <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + w2n l <= z /\ w2n d = b+j /\ w2n dt = c+j)) /\
  (w2n l = 0 \/ (w2n r = w2n rt /\ w2n r + w2n l <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + w2n l <= z /\ w2n r = b+j /\ w2n rt = c+j)) /\
  step_inst_base inst s = OK s1 ==>
  ?t1. step_inst_base inst t = OK t1 /\
    ld_memory_agree sites eom (step_taint inst s s1 tn).t_mem
      s1.vs_memory t1.vs_memory /\
    (s1 with vs_memory := s.vs_memory) = s /\
    (t1 with vs_memory := t.vs_memory) = t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexists_tac `mcopy (w2n dt) (w2n rt) (w2n l) t` >>
  gnvs[step_inst_base_opcode_eqs] >>
  `mem_taint tn inst s (mcopy (w2n d) (w2n r) (w2n l) s) =
    ((tn.t_mem DIFF {i | w2n d<=i /\ i<w2n d+w2n l}) UNION
     {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem})` by
    (simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def, new_site_bytes_def,
       mcopy_def, write_memory_with_expansion_def, range_bytes_def,
       EXTENSION, FLOOKUP_DEF, SF CONJ_ss]) >>
  simp[step_taint_def, mcopy_def, GSYM read_memory_def] >>
  reverse conj_tac >- simp[write_memory_with_expansion_def] >>
  Cases_on `w2n l = 0`
  >- (simp[EXTENSION, read_memory_def] >> irule ld_memory_agree_empty_write >> simp[]) >>
  `{k+w2n d | k<w2n l /\ k+w2n r IN tn.t_mem} =
    {w2n d+k | k<w2n l /\ w2n r+k IN tn.t_mem}` by
      (simp[arithmeticTheory.ADD_COMM]) >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_snapshot_copy >>
  disch_then irule >> simp[] >> qexists_tac `0` >> gnvs[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

(* A payload copy either writes the same bytes at both destinations or, for
   RETURNDATACOPY alone, fails the same source-side bounds check. *)
Theorem focus_fmp_cut_payload_execution[local]:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  inst.inst_operands =
    (if inst.inst_opcode = EXTCODECOPY then [addr;dst;src;sz] else [dst;src;sz]) /\
  eval_operand dst s = SOME d /\ eval_operand dst t = SOME dt /\
  eval_operand src s = SOME r /\ eval_operand src t = SOME r /\
  eval_operand sz s = SOME l /\ eval_operand sz t = SOME l /\
  (inst.inst_opcode = EXTCODECOPY ==>
     eval_operand addr s = SOME a /\ eval_operand addr t = SOME a /\
     (lookup_account (w2w a) s.vs_accounts).code =
     (lookup_account (w2w a) t.vs_accounts).code) /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata ==>
  (inst.inst_opcode = RETURNDATACOPY /\ LENGTH s.vs_returndata < w2n r + w2n l /\
   step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
   step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))) \/
  (?xs. LENGTH xs = w2n l /\
    source_memory_write_ranges inst s = [(w2n d,LENGTH xs)] /\
    step_inst_base inst s = OK (write_memory_with_expansion (w2n d) xs s) /\
    step_inst_base inst t = OK (write_memory_with_expansion (w2n dt) xs t))
Proof
  strip_tac >>
  Cases_on `LENGTH s.vs_returndata < w2n r + w2n l` >>
  gvs[step_inst_base_opcode_eqs, source_memory_write_ranges_def,
      sized_source_write_range_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n d) payload s` >>
  qexists_tac `payload` >> simp[Abbr `payload`, LENGTH_TAKE] >> decide_tac
QED

Theorem focus_fmp_cut_payload_write[local]:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  source_memory_write_ranges inst s = [(p,LENGTH xs)] /\
  ld_joint_geometry sites (X : num # num |-> 256 # num) eom owners /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  (LENGTH xs = 0 \/ (p = q /\ p + LENGTH xs <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j + LENGTH xs <= z /\ p = b+j /\ q = c+j)) ==>
  ld_memory_agree sites eom
    (step_taint inst s (write_memory_with_expansion p xs s) tn).t_mem
    (write_memory_with_expansion p xs s).vs_memory
    (write_memory_with_expansion q xs t).vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `written_taint tn inst s = {}` by
    (`inst.inst_opcode <> MSTORE /\ inst.inst_opcode <> ISTORE /\
      inst.inst_opcode <> MCOPY` by fs[] >>
     namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[written_taint_def] >>
     namedCases_on `rest` ["", "b rest2"] >> simp[written_taint_def] >>
     namedCases_on `rest2` ["", "c rest3"] >> simp[written_taint_def] >>
     Cases_on `rest3` >> simp[written_taint_def]) >>
  `mem_taint tn inst s (write_memory_with_expansion p xs s) =
    tn.t_mem DIFF {i | p<=i /\ i<p+LENGTH xs}` by
      (simp[mem_taint_def, step_writes_def, new_site_bytes_def,
            write_memory_with_expansion_def, range_bytes_def, EXTENSION,
            FLOOKUP_DEF, SF CONJ_ss] >> gvs[]) >>
  simp[step_taint_def] >> Cases_on `xs = []`
  >- (simp[EXTENSION] >> irule ld_memory_agree_empty_write >> simp[]) >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_clean_write >>
  disch_then irule >> gvs[] >> disj2_tac >>
  goal_assum (drule_at Any) >> (metis_tac[])
QED

(* For a successful read the sole updated variable is scalar; its byte
   mask is the source output mask, not the address operand's mask. *)
Theorem focus_fmp_cut_read_output[local]:
  MEM inst.inst_opcode [MLOAD;ILOAD;SHA3] /\ inst.inst_outputs = [out] /\
  word_agree_except (out_taint tn inst s) x y /\
  s1 = update_var out x s /\ t1 = update_var out y t ==>
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v a. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME a ==>
    ?b. FLOOKUP t1.vs_vars v = SOME b /\
        (~retpc_var fn v ==>
         fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
           (op_taint (step_taint inst s s1 tn) (Var v)) a b)) /\
  (step_taint inst s s1 tn).t_mem = tn.t_mem
Proof
  strip_tac >> drule_all fmpStageOpSimMemReadsTheory.fmp_mem_read_ghost >> strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def,
      fmp_value_rel_def, ld_value_agree_scalar]
QED

(* A completed payload copy modifies only memory. An out-of-bounds RETURNDATACOPY
   instead follows the explicit exception on both sides. *)
Theorem focus_fmp_cut_payload_result[local]:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY] /\
  inst.inst_operands =
    (if inst.inst_opcode = EXTCODECOPY then [addr;dst;src;sz] else [dst;src;sz]) /\
  eval_operand dst s = SOME d /\ eval_operand dst t = SOME dt /\
  eval_operand src s = SOME r /\ eval_operand src t = SOME r /\
  eval_operand sz s = SOME l /\ eval_operand sz t = SOME l /\
  (inst.inst_opcode = EXTCODECOPY ==>
     eval_operand addr s = SOME a /\ eval_operand addr t = SOME a /\
     (lookup_account (w2w a) s.vs_accounts).code =
     (lookup_account (w2w a) t.vs_accounts).code) /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata /\
  ld_joint_geometry sites (X : num # num |-> 256 # num) eom owners /\
  ld_memory_agree sites eom tn.t_mem s.vs_memory t.vs_memory /\
  (w2n l = 0 \/ (w2n d = w2n dt /\ w2n d + w2n l <= eom) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\
     j+w2n l <= z /\ w2n d = b+j /\ w2n dt = c+j)) ==>
  (inst.inst_opcode = RETURNDATACOPY /\
   step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s)) /\
   step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))) \/
  (?s1 t1. step_inst_base inst s = OK s1 /\ step_inst_base inst t = OK t1 /\
    ld_memory_agree sites eom (step_taint inst s s1 tn).t_mem
      s1.vs_memory t1.vs_memory /\
    (s1 with vs_memory := s.vs_memory) = s /\
    (t1 with vs_memory := t.vs_memory) = t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_fmp_cut_payload_execution >> strip_tac
  >- simp[] >>
  disj2_tac >>
  `ld_memory_agree sites eom
    (step_taint inst s (write_memory_with_expansion (w2n d) xs s) tn).t_mem
    (write_memory_with_expansion (w2n d) xs s).vs_memory
    (write_memory_with_expansion (w2n dt) xs t).vs_memory` by
      (irule focus_fmp_cut_payload_write >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`write_memory_with_expansion (w2n d) xs s`,
                `write_memory_with_expansion (w2n dt) xs t`] >>
  simp[] >> simp[write_memory_with_expansion_def]
QED

Theorem focus_fmp_cut_write_ghost[local]:
  MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY;CALLDATACOPY;CODECOPY;
                       RETURNDATACOPY;EXTCODECOPY;DLOADBYTES] /\
  inst.inst_outputs = [] ==>
  step_taint inst s s1 tn = tn with t_mem := mem_taint tn inst s s1
Proof
  strip_tac >> fs[] >>
  simp[step_taint_def, set_var_taint_def, adopt_reset_def, store_taint_def,
       imm_taint_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem focus_fmp_cut_copy_fields[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_returndata = t.vs_returndata /\
  (!a. (lookup_account a s.vs_accounts).code = (lookup_account a t.vs_accounts).code)
Proof
  strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn s t` by fs[fmp_stage_rel_def] >>
  drule ld_shared_accounts_fields >> strip_tac >>
  `!a. (lookup_account a s.vs_accounts).code = (lookup_account a t.vs_accounts).code` by
    (gen_tac >> first_x_assum (qspec_then `a` mp_tac) >>
     simp[vfmStateTheory.lookup_account_def, vfmStateTheory.account_state_component_equality]) >>
  fs[fmp_stage_rel_def, fmp_frame_rel_def]
QED

(* Only the offset position can carry provenance on these opcodes. The
   singleton filter excludes aliasing that position to a scalar position. *)
Theorem focus_fmp_cut_scalar_positions[local]:
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  ((inst.inst_opcode = SHA3 /\ inst.inst_operands = [dst;sz] /\ op = sz) \/
   (MEM inst.inst_opcode [MSTORE;MSTORE8] /\ inst.inst_operands = [dst;sz] /\ op = sz) \/
   (MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
      inst.inst_operands = [dst;src;sz] /\
      (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src))) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
      MEM op [addr;src;sz])) ==>
  op_prov G op = NONE
Proof
  strip_tac >> Cases_on `op` >> simp[op_prov_def] >>
  rename1 `FLOOKUP G v` >> Cases_on `FLOOKUP G v` >> simp[] >>
  `v IN pv` by (fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  gvs[ptr_use_static_ok_def, is_pointer_preserving_op_def,
      mem_read_ops_def, mem_write_ops_def] >>
  qpat_x_assum `!u. _` (qspec_then `v` mp_tac) >>
  simp[] >> rw[] >> gvs[inst_access_ops_component_equality, AllCaseEqs()]
QED

Theorem focus_fmp_cut_read_range[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  eval_operand dst s = SOME x /\
  ((MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [dst] /\ len = 32) \/
   (inst.inst_opcode = SHA3 /\ inst.inst_operands = [dst;sz] /\
     eval_operand sz s = SOME l /\ len = w2n l)) ==>
  ?y. eval_operand dst t = SOME y /\
      (len = 0 \/ (w2n x = w2n y /\ w2n x+len <= eom) \/
       (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
         j+len <= z /\ w2n x = b+j /\ w2n y = c+j))
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI /\ MEM dst inst.inst_operands` by fs[] >>
  `~MEM inst.inst_opcode [ASSIGN;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by fs[] >>
  `op_taint tn dst = {}` by (drule_all taint_ok_operand_exclusion >> simp[]) >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = dst` by
    (fs[] >> simp[mem_read_ops_def]) >>
  `MEM (w2n x,len) (source_memory_read_ranges inst s)` by
    (fs[] >> simp[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  `!v. dst = Var v ==> ~retpc_var fn v` by metis_tac[] >>
  drule_all fmp_mem_read_operand_range_point >> simp[]
QED

Theorem focus_fmp_cut_scalar_value[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  inst.inst_opcode <> PHI /\ MEM op inst.inst_operands /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  op_prov G op = NONE /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\ word_agree_except (op_taint tn op) x y /\
    (op_taint tn op = {} ==> x = y)
Proof
  strip_tac >>
  `(!v. op = Var v ==> ~retpc_var fn v)` by metis_tac[] >>
  drule_all fmpStageOpBaseTheory.fmp_stage_operand_point >>
  simp[fmp_value_rel_def, ld_value_agree_scalar] >> metis_tac[ld_value_agree_clean, ld_value_agree_scalar]
QED

Theorem focus_fmp_cut_read_result[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv /\
  MEM inst.inst_opcode [MLOAD;ILOAD;SHA3] /\
  terminates (step_inst_base inst s) ==>
  ?out a b. inst.inst_outputs = [out] /\
    step_inst_base inst s = OK (update_var out a s) /\
    step_inst_base inst t = OK (update_var out b t) /\
    word_agree_except (out_taint tn inst s) a b
Proof
  strip_tac >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by fs[fmp_stage_rel_def] >>
  Cases_on `inst.inst_opcode = SHA3`
  >- (`?p sz out x l. inst.inst_operands = [p;sz] /\ inst.inst_outputs = [out] /\
         eval_operand p s = SOME x /\ eval_operand sz s = SOME l` by
        (qpat_x_assum `terminates _` mp_tac >>
         namedCases_on `inst.inst_operands` ["", "p ps"] >> simp[step_inst_base_opcode_eqs, terminates_def] >>
         namedCases_on `ps` ["", "sz rest"] >> simp[terminates_def] >>
         Cases_on `rest` >> simp[terminates_def] >>
         Cases_on `eval_operand p s` >> simp[terminates_def] >>
         Cases_on `eval_operand sz s` >> simp[terminates_def] >>
         namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[terminates_def] >>
         Cases_on `outs` >> simp[terminates_def]) >>
      `op_prov G sz = NONE` by
        (irule focus_fmp_cut_scalar_positions >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      `MEM sz inst.inst_operands /\ inst.inst_opcode <> PHI /\
        MEM inst.inst_opcode [SHA3;LOG;CREATE;CREATE2]` by simp[] >>
      `op_taint tn sz = {}` by (drule_all taint_ok_observation_operand >> simp[]) >>
      `eval_operand sz t = SOME l` by (drule_all focus_fmp_cut_scalar_value >> simp[]) >>
      (`?y. eval_operand p t = SOME y /\
         (w2n l = 0 \/ (w2n x = w2n y /\ w2n x+w2n l <= eom) \/
          (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
            j+w2n l <= z /\ w2n x = b+j /\ w2n y = c+j))` suffices_by
          (disch_then (qx_choose_then `y` (CONJUNCTS_THEN assume_tac)) >>
           drule_all focus_fmp_cut_sha3_read >> strip_tac >>
           qexistsl_tac [`out`,`w`,`w`] >> simp[word_agree_except_def])) >>
      irule focus_fmp_cut_read_range >> simp[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [MLOAD;ILOAD]` by fs[] >>
  `?p out x. inst.inst_operands = [p] /\ inst.inst_outputs = [out] /\
     eval_operand p s = SOME x` by
    (qpat_x_assum `terminates _` mp_tac >> fs[] >>
     namedCases_on `inst.inst_operands` ["", "p ps"] >>
     simp[step_inst_base_opcode_eqs, exec_read1_def, terminates_def] >>
     Cases_on `ps` >> simp[terminates_def] >>
     Cases_on `eval_operand p s` >> simp[terminates_def] >>
     namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[terminates_def] >>
     Cases_on `outs` >> simp[terminates_def]) >>
  (`?y. eval_operand p t = SOME y /\
     (w2n x = w2n y /\ w2n x+32 <= eom \/
      (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
        j+32 <= z /\ w2n x = b+j /\ w2n y = c+j))` suffices_by
     (disch_then (qx_choose_then `y` (CONJUNCTS_THEN assume_tac)) >>
      drule_all focus_fmp_cut_word_read >> strip_tac >>
      qexistsl_tac [`out`,`mload (w2n x) s`,`mload (w2n y) t`] >> gvs[out_taint_def])) >>
  drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`) focus_fmp_cut_read_range >>
  disch_then (qspecl_then [`x`,`p`,`32`,`0w`,`inst`,`p`] mp_tac) >>
  simp[]
QED

(* All writes use the write-range selector, independently of MCOPY's read
   selector.  The sized write computation also covers a zero-size copy. *)
Theorem focus_fmp_cut_write_range[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  ((MEM inst.inst_opcode [MSTORE;MSTORE8] /\ inst.inst_operands = [dst;src] /\
     len = (if inst.inst_opcode = MSTORE then 32 else 1)) \/
   (MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
     inst.inst_operands = [dst;src;sz] /\ eval_operand sz s = SOME l /\ len = w2n l) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
     eval_operand addr s = SOME a /\ eval_operand sz s = SOME l /\ len = w2n l)) ==>
  ?dt. eval_operand dst t = SOME dt /\
    (len = 0 \/ (w2n d = w2n dt /\ w2n d+len <= eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+len <= z /\ w2n d = b+j /\ w2n dt = c+j))
Proof
  strip_tac >>
  `MEM dst inst.inst_operands /\ inst.inst_opcode <> PHI` by fs[] >>
  `op_taint tn dst = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
     simp[taint_ok_def] >> fs[] >> metis_tac[]) >>
  `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = dst` by
    (fs[] >> simp[mem_write_ops_def]) >>
  `MEM (w2n d,len) (source_memory_write_ranges inst s)` by
    (fs[] >> simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def]) >>
  `!v. dst = Var v ==> ~retpc_var fn v` by metis_tac[] >>
  drule_all fmp_mem_write_operand_range_point >> simp[]
QED

Theorem focus_fmp_cut_mcopy_source[local]:
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME l ==>
  ?rt. eval_operand src t = SOME rt /\
    (w2n l = 0 \/ (w2n r = w2n rt /\ w2n r+w2n l <= eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l <= z /\ w2n r = b+j /\ w2n rt = c+j))
Proof
  strip_tac >>
  `MEM src inst.inst_operands /\ inst.inst_opcode <> PHI /\
    ~MEM inst.inst_opcode [ASSIGN;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by simp[] >>
  `op_taint tn src = {}` by (drule_all taint_ok_operand_exclusion >> simp[]) >>
  `?ops. mem_read_ops inst = SOME ops /\ ops.iao_ofst = src` by simp[mem_read_ops_def] >>
  `MEM (w2n r,w2n l) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `!v. src = Var v ==> ~retpc_var fn v` by metis_tac[] >>
  drule_all fmp_mem_read_operand_range_point >> simp[]
QED

val cut_payload_ops = ``[CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES;EXTCODECOPY]``;

Theorem focus_fmp_cut_copy_operands[local]:
  (inst.inst_opcode = MCOPY \/ MEM inst.inst_opcode ^cut_payload_ops) /\
  terminates (step_inst_base inst s) ==>
  ?addr dst src sz d v l. inst.inst_operands =
      (if inst.inst_opcode = EXTCODECOPY then [addr;dst;src;sz] else [dst;src;sz]) /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME v /\
    eval_operand sz s = SOME l /\
    (inst.inst_opcode = EXTCODECOPY ==> IS_SOME (eval_operand addr s))
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >> qpat_x_assum `terminates _` mp_tac >>
  namedCases_on `inst.inst_operands` ["", "a ps"]
  >- (fs[] >> simp[step_inst_base_opcode_eqs, terminates_def]) >>
  namedCases_on `ps` ["", "b qs"]
  >- (fs[] >> simp[step_inst_base_opcode_eqs, terminates_def]) >>
  namedCases_on `qs` ["", "c rs"]
  >- (fs[] >> simp[step_inst_base_opcode_eqs, terminates_def]) >>
  namedCases_on `rs` ["", "d rest"]
  >- (fs[] >> simp[step_inst_base_opcode_eqs, terminates_def] >>
      Cases_on `eval_operand a s` >> simp[terminates_def] >>
      Cases_on `eval_operand b s` >> simp[terminates_def] >>
      Cases_on `eval_operand c s` >> simp[terminates_def]) >>
  Cases_on `rest`
  >- (fs[] >> simp[step_inst_base_opcode_eqs, terminates_def] >>
      Cases_on `eval_operand a s` >> simp[terminates_def] >>
      Cases_on `eval_operand b s` >> simp[terminates_def] >>
      Cases_on `eval_operand c s` >> simp[terminates_def] >>
      Cases_on `eval_operand d s` >> simp[terminates_def]) >>
  fs[] >> simp[step_inst_base_opcode_eqs, terminates_def]
QED

val cut_memory_point = ``
  wf_function fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  ~in_revert_forward fn s /\ access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  (!v. MEM (Var v) inst.inst_operands ==> ~retpc_var fn v) /\
  ptr_use_static_ok P pv inst /\ FDOM G SUBSET pv``;

val cut_write_result = ``?t1. step_inst_base inst t = OK t1 /\
  ld_memory_agree (fmp_ld_sites sm) eom (step_taint inst s s1 tn).t_mem
    s1.vs_memory t1.vs_memory /\
  (s1 with vs_memory := s.vs_memory) = s /\
  (t1 with vs_memory := t.vs_memory) = t``;

Theorem focus_fmp_cut_store_result[local]:
  ^cut_memory_point /\ eom <= fmp0 /\ fmp0 <= raw0 /\
  MEM inst.inst_opcode [MSTORE;MSTORE8] /\
  step_inst_base inst s = r /\ terminates r ==>
  ?s1. r = OK s1 /\ ^cut_write_result
Proof
  strip_tac >>
  `?dst src d v s1. inst.inst_operands = [dst;src] /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME v /\
    step_inst_base inst s = OK s1 /\ r = OK s1` by
    (qpat_x_assum `terminates r` mp_tac >> gvs[] >>
     namedCases_on `inst.inst_operands` ["", "dst ps"] >>
     simp[step_inst_base_opcode_eqs, exec_write2_def, terminates_def] >>
     namedCases_on `ps` ["", "src rest"] >> simp[terminates_def] >>
     Cases_on `rest` >> simp[terminates_def] >>
     Cases_on `eval_operand dst s` >> simp[terminates_def] >>
     Cases_on `eval_operand src s` >> simp[terminates_def]) >>
  qexists_tac `s1` >> simp[] >>
  `op_prov G src = NONE` by
    (irule focus_fmp_cut_scalar_positions >>
     goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
     gvs[SF SFY_ss]) >>
  `MEM src inst.inst_operands /\ inst.inst_opcode <> PHI` by fs[] >>
  drule_all focus_fmp_cut_scalar_value >> strip_tac >>
  `(if inst.inst_opcode = MSTORE then word_agree_except (op_taint tn src) v y
    else v = y)` by
    (Cases_on `inst.inst_opcode = MSTORE` >> simp[] >>
     `~MEM inst.inst_opcode [ASSIGN;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by fs[] >>
     drule_all taint_ok_operand_exclusion >> simp[]) >>
  qabbrev_tac `(len:num) = if inst.inst_opcode = MSTORE then 32 else 1` >>
  `len <> 0` by (simp[Abbr `len`] >> Cases_on `inst.inst_opcode = MSTORE` >> simp[]) >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by fs[fmp_stage_rel_def] >>
  `len = (if inst.inst_opcode = MSTORE then 32 else 1)` by simp[Abbr `len`] >>
  (`?dt. eval_operand dst t = SOME dt /\
    (len = 0 \/ (w2n d = w2n dt /\ w2n d+len <= eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+len <= z /\ w2n d = b+j /\ w2n dt = c+j))` suffices_by
     (asm_rewrite_tac[] >>
      disch_then (qx_choose_then `dt` (CONJUNCTS_THEN assume_tac)) >>
      irule focus_fmp_cut_store >>
      asm_rewrite_tac[] >> conj_tac
      >- (qexistsl_tac [`len`,`dst`,`v`,`src`,`y`,`d`,`dt`] >> asm_rewrite_tac[]) >>
      qexistsl_tac [`FEMPTY`,`MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm)))`] >>
      irule fmp_mem_geometry_point >> simp[] >> metis_tac[])) >>
  irule focus_fmp_cut_write_range >>
  goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ s = SOME _`)) >>
  asm_rewrite_tac[]
QED

(* Copy lengths and non-memory source arguments are clean scalar words. *)
Theorem focus_fmp_cut_copy_scalar[local]:
  ^cut_memory_point /\
  ((MEM inst.inst_opcode [MCOPY;CALLDATACOPY;CODECOPY;RETURNDATACOPY;DLOADBYTES] /\
    inst.inst_operands = [dst;src;sz] /\ (op = sz \/ (inst.inst_opcode <> MCOPY /\ op = src))) \/
   (inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [addr;dst;src;sz] /\
    MEM op [addr;src;sz])) /\ eval_operand op s = SOME x ==>
  eval_operand op t = SOME x
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `op_prov G op = NONE` by
    (irule focus_fmp_cut_scalar_positions >>
     goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
     fs[] >> metis_tac[]) >>
  `MEM op inst.inst_operands /\ inst.inst_opcode <> PHI /\
   ~MEM inst.inst_opcode [ASSIGN;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by fs[] >>
  `op_taint tn op = {}` by (drule_all taint_ok_operand_exclusion >> simp[]) >>
  drule_all focus_fmp_cut_scalar_value >> simp[]
QED

Theorem focus_fmp_cut_mcopy_result[local]:
  ^cut_memory_point /\ eom <= fmp0 /\ fmp0 <= raw0 /\
  inst.inst_opcode = MCOPY /\ step_inst_base inst s = rs /\ terminates rs ==>
  ?s1. rs = OK s1 /\ ^cut_write_result
Proof
  strip_tac >>
  `?dst src sz d r l. inst.inst_operands = [dst;src;sz] /\
    eval_operand dst s = SOME d /\ eval_operand src s = SOME r /\
    eval_operand sz s = SOME l` by
    (`terminates (step_inst_base inst s)` by simp[] >>
     drule_at (Pat `terminates _`) focus_fmp_cut_copy_operands >> simp[]) >>
  `rs = OK (mcopy (w2n d) (w2n r) (w2n l) s)` by
    (qpat_x_assum `step_inst_base inst s = rs` mp_tac >> simp[step_inst_base_opcode_eqs]) >>
  qexists_tac `mcopy (w2n d) (w2n r) (w2n l) s` >> simp[] >>
  `eval_operand sz t = SOME l` by
    (irule focus_fmp_cut_copy_scalar >>
     goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
     simp[SF SFY_ss]) >>
  `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by fs[fmp_stage_rel_def] >>
  (`?rt. eval_operand src t = SOME rt /\
    (w2n l = 0 \/ (w2n r = w2n rt /\ w2n r+w2n l <= eom) \/
     (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
       j+w2n l <= z /\ w2n r = b+j /\ w2n rt = c+j))` suffices_by
     (disch_then (qx_choose_then `rt` (CONJUNCTS_THEN assume_tac)) >>
      (`?dt. eval_operand dst t = SOME dt /\
        (w2n l = 0 \/ (w2n d = w2n dt /\ w2n d+w2n l <= eom) \/
         (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
           j+w2n l <= z /\ w2n d = b+j /\ w2n dt = c+j))` suffices_by
         (disch_then (qx_choose_then `dt` (CONJUNCTS_THEN assume_tac)) >>
          irule focus_fmp_cut_mcopy >>
          asm_rewrite_tac[] >> conj_tac
          >- (qexistsl_tac [`d`,`dst`,`dt`,`l`,`r`,`rt`,`src`,`sz`] >> asm_rewrite_tac[]) >>
          qexistsl_tac [`FEMPTY`,`MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm)))`] >>
          irule fmp_mem_geometry_point >> simp[] >> metis_tac[])) >>
      irule focus_fmp_cut_write_range >>
      goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
      qexistsl_tac [`ARB`,`ARB`,`l`,`r`,`src`,`sz`] >> simp[])) >>
  drule_all focus_fmp_cut_mcopy_source >> simp[]
QED

Theorem focus_fmp_cut_payload_point[local]:
  ^cut_memory_point /\ eom <= fmp0 /\ fmp0 <= raw0 /\
  MEM inst.inst_opcode ^cut_payload_ops /\ step_inst_base inst s = rs /\ terminates rs ==>
  (?r'. step_inst_base inst t = r' /\
    (?s1. rs = Abort ExHalt_abort s1) /\ dead_result_rel D rs r') \/
  (?s1. rs = OK s1 /\ ^cut_write_result)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `terminates (step_inst_base inst s)` by simp[] >>
  drule_at (Pat `terminates _`) focus_fmp_cut_copy_operands >>
  simp[SF SFY_ss] >> strip_tac >>
  rename1 `eval_operand src s = SOME v` >>
  drule focus_fmp_cut_copy_fields >> strip_tac >>
  `!op x. MEM op [src;sz] /\ eval_operand op s = SOME x ==>
    eval_operand op t = SOME x` by
      (rpt strip_tac >> irule focus_fmp_cut_copy_scalar >>
       goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
       goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
       Cases_on `inst.inst_opcode = EXTCODECOPY` >>
       fs[SF SFY_ss] >> metis_tac[]) >>
  `eval_operand src t = SOME v /\ eval_operand sz t = SOME l` by metis_tac[MEM] >>
  `?a. inst.inst_opcode = EXTCODECOPY ==>
    eval_operand addr s = SOME a /\ eval_operand addr t = SOME a /\
    (lookup_account (w2w a) s.vs_accounts).code =
    (lookup_account (w2w a) t.vs_accounts).code` by
      (Cases_on `inst.inst_opcode = EXTCODECOPY` >> simp[] >>
       `?a. eval_operand addr s = SOME a` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
       qexists_tac `a` >> simp[] >>
       irule focus_fmp_cut_copy_scalar >>
       goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
       goal_assum (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
       simp[SF SFY_ss]) >>
  (`?dt. eval_operand dst t = SOME dt /\
      (w2n l = 0 \/ (w2n d = w2n dt /\ w2n d+w2n l <= eom) \/
       (?id b c z j. FLOOKUP (fmp_ld_sites sm) id = SOME (b,c,z) /\
         j+w2n l <= z /\ w2n d = b+j /\ w2n dt = c+j))` suffices_by
     (disch_then (qx_choose_then `dt` (CONJUNCTS_THEN assume_tac)) >>
      `ld_joint_geometry (fmp_ld_sites sm) (FEMPTY : num # num |-> 256 # num) eom
        (MAP FST (SET_TO_LIST (FDOM (fmp_ld_sites sm))))` by
          (irule fmp_mem_geometry_point >> simp[] >> metis_tac[]) >>
      `ld_memory_agree (fmp_ld_sites sm) eom tn.t_mem s.vs_memory t.vs_memory` by
        fs[fmp_stage_rel_def] >>
      drule_all focus_fmp_cut_payload_result >> strip_tac
      >- (`rs = Abort ExHalt_abort (halt_state (set_returndata [] s))` by metis_tac[] >>
          disj1_tac >> simp[dead_result_rel_def]) >>
      disj2_tac >> qexists_tac `s1` >> simp[] >> metis_tac[])) >>
  irule focus_fmp_cut_write_range >>
  goal_assum (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `active_inst _ _ _`)) >>
  Cases_on `inst.inst_opcode = EXTCODECOPY` >> fs[SF SFY_ss] >> metis_tac[]
QED

val cut_read_ops = ``[MLOAD;ILOAD;SHA3]``;
val cut_write_ops = ``[MSTORE;MSTORE8;MCOPY;CALLDATACOPY;CODECOPY;
                       RETURNDATACOPY;EXTCODECOPY;DLOADBYTES]``;

val cut_data = ``
  (!v. ~MEM v inst.inst_outputs ==>
       FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
       FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
     ?y. FLOOKUP t1.vs_vars v = SOME y /\
         (~retpc_var fn v ==> fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
           (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address (step_taint inst s s1 tn) s1 t1``;

Theorem focus_fmp_cut_read_data[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^cut_read_ops /\ inst.inst_outputs = [out] /\
  word_agree_except (out_taint tn inst s) x y /\
  s1 = update_var out x s /\ t1 = update_var out y t ==>
  ^cut_data
Proof
  strip_tac >> drule_all focus_fmp_cut_read_output >> strip_tac >>
  drule_all fmpStageOpSimMemReadsTheory.fmp_mem_read_ghost >> strip_tac >>
  fs[fmp_stage_rel_def] >>
  gvs[update_var_def, ld_shared_agree_def]
QED

Theorem focus_fmp_cut_write_data[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  MEM inst.inst_opcode ^cut_write_ops /\ inst_wf inst /\
  ld_memory_agree (fmp_ld_sites sm) eom (step_taint inst s s1 tn).t_mem
    s1.vs_memory t1.vs_memory /\
  (s1 with vs_memory := s.vs_memory) = s /\
  (t1 with vs_memory := t.vs_memory) = t ==>
  ^cut_data
Proof
  strip_tac >>
  `inst.inst_outputs = []` by
    (qpat_assum `MEM _ ^cut_write_ops`
       (REPEAT_TCL DISJ_CASES_THEN assume_tac o REWRITE_RULE [MEM]) >>
     fs[inst_wf_def]) >>
  drule_all focus_fmp_cut_write_ghost >> strip_tac >>
  `s1.vs_vars = s.vs_vars /\ t1.vs_vars = t.vs_vars` by
    (conj_tac
     >- (qpat_assum `(s1 with vs_memory := s.vs_memory) = s`
           (mp_tac o Q.AP_TERM `\u. u.vs_vars`) >> simp[]) >>
     qpat_assum `(t1 with vs_memory := t.vs_memory) = t`
       (mp_tac o Q.AP_TERM `\u. u.vs_vars`) >> simp[]) >>
  `ld_shared_agree D s.vs_call_ctx.cc_address tn
     (s1 with vs_memory := s.vs_memory) (t1 with vs_memory := t.vs_memory)` by
    (asm_rewrite_tac[] >> fs[fmp_stage_rel_def]) >>
  fs[ld_shared_agree_def]
QED

(* Local execution at the current instruction, before advancing either
   cursor. Only RETURNDATACOPY can abort in this class. *)
Theorem focus_fmp_cut_memory_effect:
  ^cut_memory_point /\ inst_wf inst /\ eom <= fmp0 /\ fmp0 <= raw0 /\
  MEM inst.inst_opcode (^cut_read_ops ++ ^cut_write_ops) /\
  step_inst_base inst s = r /\ terminates r ==>
  ?r'. step_inst_base inst t = r' /\
    case r of
      OK s1 => ?t1. r' = OK t1 /\ ^cut_data
    | Abort ab s1 => dead_result_rel D r r'
    | _ => F
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `MEM inst.inst_opcode ^cut_read_ops`
  >- (`terminates (step_inst_base inst s)` by simp[] >>
      drule_all focus_fmp_cut_read_result >> strip_tac >>
      `r = OK (update_var out a s)` by metis_tac[] >>
      qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
      qexists_tac `OK (update_var out b t)` >> conj_tac >- simp[] >>
      pure_rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
      qexists_tac `update_var out b t` >> conj_tac >- simp[] >>
      irule focus_fmp_cut_read_data >> simp[SF SFY_ss] >>
      qexistsl_tac [`a`,`b`] >> simp[]) >>
  `MEM inst.inst_opcode ^cut_write_ops` by fs[MEM_APPEND] >>
  `(?r'. step_inst_base inst t = r' /\
     (?s1. r = Abort ExHalt_abort s1) /\ dead_result_rel D r r') \/
   (?s1. r = OK s1 /\ ^cut_write_result)` by
    (Cases_on `MEM inst.inst_opcode [MSTORE;MSTORE8]`
     >- (disj2_tac >> drule_all focus_fmp_cut_store_result >> simp[]) >>
     Cases_on `inst.inst_opcode = MCOPY`
     >- (disj2_tac >> drule_all focus_fmp_cut_mcopy_result >> simp[]) >>
     `MEM inst.inst_opcode ^cut_payload_ops` by fs[] >>
     drule_all focus_fmp_cut_payload_point >> simp[])
  >- (qexists_tac `r'` >> gvs[]) >>
  qpat_x_assum `r = OK _` SUBST_ALL_TAC >>
  qexists_tac `OK t1` >> conj_tac >- simp[] >>
  pure_rewrite_tac[TypeBase.case_def_of ``:exec_result``] >> BETA_TAC >>
  qexists_tac `t1` >> conj_tac >- simp[] >>
  irule focus_fmp_cut_write_data >> simp[SF SFY_ss]
QED

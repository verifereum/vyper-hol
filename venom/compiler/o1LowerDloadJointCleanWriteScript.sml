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
  (* P4a in progress *) cheat
QED

Theorem ld_joint_clean_write_payload_fields:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts ==>
  s.vs_call_ctx.cc_calldata = t.vs_call_ctx.cc_calldata /\
  s.vs_code = t.vs_code /\ s.vs_returndata = t.vs_returndata /\
  (!addr. (lookup_account addr s.vs_accounts).code =
          (lookup_account addr t.vs_accounts).code)
Proof
  (* P4a in progress *) cheat
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
    (len=0 \/ (w2n d=w2n d' /\ (w2n d+len<=lo \/
       dyn_floor C vs<=w2n d /\ w2n d+len<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+len<=z /\
                    w2n d=b+j /\ w2n d'=c+j))
Proof
  (* P4a in progress *) cheat
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
    (LENGTH xs=0 \/ (p=q /\ (p+LENGTH xs<=lo \/
       dyn_floor C vs<=p /\ p+LENGTH xs<=dimword (:256))) \/
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
  (* P4a in progress *) cheat
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
    ld_dyn_agree (dyn_floor C vs) (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory /\
    (?ms mt. s1 = s with vs_memory := ms /\ t1 = t with vs_memory := mt)
Proof
  (* P4a in progress *) cheat
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
  (* P4a in progress *) cheat
QED

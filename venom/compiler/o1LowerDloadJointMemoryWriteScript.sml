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
    ((w2n x=w2n y /\ (w2n x+32<=lo \/
       dyn_floor C vs<=w2n x /\ w2n x+32<=dimword (:256))) \/
     (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
       w2n x = b+j /\ w2n y = c+j))
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_mstore_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MSTORE /\ step_inst fuel C inst s = OK s1 ==>
  ?t1. step_inst fuel C' inst t = OK t1 /\
    ld_memory_agree sites lo (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory /\
    ld_dyn_agree (dyn_floor C vs) (mem_taint tn inst s s1)
      s1.vs_memory t1.vs_memory
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_memory_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = s with vs_memory := ms /\ t1 = t with vs_memory := mt /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H stk PG G
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  tn1.t_var = tn.t_var /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  ld_memory_agree sites lo tn1.t_mem s1.vs_memory t1.vs_memory /\
  ld_dyn_agree (dyn_floor C vs) tn1.t_mem s1.vs_memory t1.vs_memory ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H sites X ts
Proof
  (* P4a in progress *) cheat
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
  (* P4a in progress *) cheat
QED

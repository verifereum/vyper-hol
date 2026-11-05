(* Operational consumers of the source-indexed relocation kernel. *)
Theory o1LowerDloadMemoryConsumer
Ancestors
  o1LowerDloadRelocationKernel regularCallEmitSim venomExecSemantics ptrDiscipline
  venomMemProps venomState list rich_list codegenRel finite_map words byte pred_set

Theorem ld_mload_mapped_bytes:
  (!k. k < 32 ==>
       read_byte (a+k) s.vs_memory = read_byte (b+k) t.vs_memory) ==>
  mload a s = mload b t
Proof
  strip_tac >> simp[mload_def] >> AP_TERM_TAC >> irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ] >> rpt strip_tac >>
  simp[EL_TAKE, EL_APPEND_EQN, EL_DROP, EL_REPLICATE] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[read_byte_def] >>
  Cases_on `a+x < LENGTH s.vs_memory` >>
  Cases_on `b+x < LENGTH t.vs_memory` >> simp[]
QED

Theorem ld_mload_site:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
  (!k. k < 32 ==> b+j+k NOTIN mask) ==>
  mload (b+j) s = mload (c+j) t
Proof
  strip_tac >> irule ld_mload_mapped_bytes >> rpt strip_tac >>
  simp[GSYM arithmeticTheory.ADD_ASSOC] >>
  irule ld_memory_agree_site_byte >>
  qexistsl_tac [`id`, `lo`, `mask`, `sites`, `z`] >>
  rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem ld_mstore_bytes:
  read_byte i (mstore a v s).vs_memory =
  if a <= i /\ i < a+32 then EL (i-a) (word_to_bytes v T)
  else read_byte i s.vs_memory
Proof
  `mstore a v s = write_memory_with_expansion a (word_to_bytes v T) s` by
    simp[mstore_def, write_memory_with_expansion_def, LENGTH_word_to_bytes, wordsTheory.dimword_def] >>
  simp[read_byte_write_memory_with_expansion, LENGTH_word_to_bytes, wordsTheory.dimword_def]
QED

Theorem ld_step_mstore:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME (n2w a) /\ eval_operand vop s = SOME v /\
  a < dimword (:256) ==>
  step_inst fuel ctx inst s = OK (mstore a v s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
                   exec_write2_def]
QED

Theorem ld_step_mload:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [p] /\
  inst.inst_outputs = [out] /\ eval_operand p s = SOME (n2w a) /\
  a < dimword (:256) ==>
  step_inst fuel ctx inst s = OK (update_var out (mload a s) s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def,
                   exec_read1_def]
QED

(* Distinct protected sites are separated in both address spaces.  Zero-size
   sites are harmless: their byte projection has no instances. *)
Theorem ld_memory_agree_mstore_masked:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites owner = SOME (b,c,z) /\ j+32 <= z /\ lo <= b /\ lo <= c /\
  (!id b' c' z'. FLOOKUP sites id = SOME (b',c',z') ==>
     (b' = b /\ c' = c) \/
     ((b'+z' <= b \/ b+z <= b') /\ (c'+z' <= c \/ c+z <= c'))) /\
  word_agree_except m v w ==>
  ld_memory_agree sites lo
    ((mask DIFF {i | b+j <= i /\ i < b+j+32}) UNION {b+j+k | k IN m})
    (mstore (b+j) v s).vs_memory (mstore (c+j) w t).vs_memory
Proof
  strip_tac >> rewrite_tac[ld_memory_agree_def] >> conj_tac
  >- (rpt strip_tac >>
      `~(b+j <= i /\ i < b+j+32) /\
       ~(c+j <= i /\ i < c+j+32)` by decide_tac >>
      simp[ld_mstore_bytes] >> irule ld_memory_agree_fixed_byte >>
      qexistsl_tac [`lo`, `mask`, `sites`] >> gvs[]) >>
  rpt strip_tac >>
  rename1 `FLOOKUP sites id = SOME (sb,tb,sz)` >>
  qpat_x_assum `!id b' c' z'. _` drule >> strip_tac
  >- (gnvs[] >> simp[ld_mstore_bytes] >>
      Cases_on `j <= j' /\ j' < j+32`
      >- (gnvs[] >>
          `j' = j + (j'-j)` by decide_tac >>
          `j'-j NOTIN m` by metis_tac[] >>
          qpat_x_assum `word_agree_except _ _ _` mp_tac >>
          simp[word_agree_except_def] >>
          disch_then (qspec_then `j'-j` mp_tac) >> simp[]) >>
      gvs[] >>
      irule ld_memory_agree_site_byte >>
      qexistsl_tac [`id`, `lo`, `mask`, `sites`, `sz`] >> gvs[]) >>
  `~(b+j <= sb+j' /\ sb+j' < b+j+32) /\
   ~(c+j <= tb+j' /\ tb+j' < c+j+32)` by decide_tac >>
  asm_rewrite_tac[ld_mstore_bytes] >> irule ld_memory_agree_site_byte >>
  qexistsl_tac [`id`, `lo`, `mask`, `sites`, `sz`] >> gvs[]
QED

Theorem ld_memory_agree_mstore:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites owner = SOME (b,c,z) /\ j+32 <= z /\ lo <= b /\ lo <= c /\
  (!id b' c' z'. FLOOKUP sites id = SOME (b',c',z') ==>
     (b' = b /\ c' = c) \/
     ((b'+z' <= b \/ b+z <= b') /\ (c'+z' <= c \/ c+z <= c'))) ==>
  ld_memory_agree sites lo (mask DIFF {i | b+j <= i /\ i < b+j+32})
    (mstore (b+j) v s).vs_memory (mstore (c+j) v t).vs_memory
Proof
  strip_tac >>
  qspecl_then [`{}`, `v`] mp_tac
    (Q.GENL [`m`, `w`] ld_memory_agree_mstore_masked) >>
  simp[word_agree_except_def] >> disch_then irule >> metis_tac[]
QED

Theorem ld_step_mload_transfer:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites id = SOME (b,c,z) /\ j+32 <= z /\
  (!k. k < 32 ==> b+j+k NOTIN mask) /\
  b+j < dimword (:256) /\ c+j < dimword (:256) /\
  si.inst_opcode = MLOAD /\ si.inst_operands = [sp] /\ si.inst_outputs = [out] /\
  ti.inst_opcode = MLOAD /\ ti.inst_operands = [tp] /\ ti.inst_outputs = [out] /\
  eval_operand sp s = SOME (n2w (b+j)) /\
  eval_operand tp t = SOME (n2w (c+j)) ==>
  step_inst fuel sc si s = OK (update_var out (mload (b+j) s) s) /\
  step_inst fuel tc ti t = OK (update_var out (mload (b+j) s) t)
Proof
  strip_tac >>
  `mload (b+j) s = mload (c+j) t` by
    (drule_all ld_mload_site >> simp[]) >>
  conj_tac >- (irule ld_step_mload >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac[] >> irule ld_step_mload >> simp[] >> metis_tac[]
QED

(* The same clean word can be stored and read back in both executions.
   Operand availability after each write is explicit; target operational
   success is a conclusion, never a premise. *)
Theorem ld_step_clean_store_load:
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  FLOOKUP sites owner = SOME (b,c,z) /\ j+32 <= z /\ lo <= b /\ lo <= c /\
  (!id b' c' z'. FLOOKUP sites id = SOME (b',c',z') ==>
     (b' = b /\ c' = c) \/
     ((b'+z' <= b \/ b+z <= b') /\ (c'+z' <= c \/ c+z <= c'))) /\
  b+j < dimword (:256) /\ c+j < dimword (:256) /\
  sw.inst_opcode = MSTORE /\ sw.inst_operands = [sp;sv] /\
  tw.inst_opcode = MSTORE /\ tw.inst_operands = [tp;tv] /\
  eval_operand sp s = SOME (n2w (b+j)) /\ eval_operand sv s = SOME v /\
  eval_operand tp t = SOME (n2w (c+j)) /\ eval_operand tv t = SOME v /\
  sr.inst_opcode = MLOAD /\ sr.inst_operands = [sq] /\ sr.inst_outputs = [out] /\
  tr.inst_opcode = MLOAD /\ tr.inst_operands = [tq] /\ tr.inst_outputs = [out] /\
  eval_operand sq (mstore (b+j) v s) = SOME (n2w (b+j)) /\
  eval_operand tq (mstore (c+j) v t) = SOME (n2w (c+j)) ==>
  step_inst fuel sc sw s = OK (mstore (b+j) v s) /\
  step_inst fuel tc tw t = OK (mstore (c+j) v t) /\
  ld_memory_agree sites lo (mask DIFF {i | b+j <= i /\ i < b+j+32})
    (mstore (b+j) v s).vs_memory (mstore (c+j) v t).vs_memory /\
  step_inst fuel sc sr (mstore (b+j) v s) =
    OK (update_var out v (mstore (b+j) v s)) /\
  step_inst fuel tc tr (mstore (c+j) v t) =
    OK (update_var out v (mstore (c+j) v t))
Proof
  strip_tac >> conj_tac
  >- (irule ld_step_mstore >> simp[] >> metis_tac[]) >> conj_tac
  >- (irule ld_step_mstore >> simp[] >> metis_tac[]) >> conj_tac
  >- (drule_all ld_memory_agree_mstore >> simp[]) >>
  conj_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def,
       mload_mstore_same]
QED

Theorem ld_mem_taint_mstore:
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME (n2w a) /\ eval_operand vop s = SOME v /\
  a < dimword (:256) ==>
  mem_taint tn inst s (mstore a v s) =
    ((tn.t_mem DIFF {i | a <= i /\ i < a+32}) UNION
     {a+k | k IN op_taint tn vop})
Proof
  strip_tac >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def,
       new_site_bytes_def, mstore_def, range_bytes_def] >>
  simp[EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ld_memory_agree_mstore_taint:
  ld_memory_agree sites lo tn.t_mem s.vs_memory t.vs_memory /\
  FLOOKUP sites owner = SOME (b,c,z) /\ j+32 <= z /\ lo <= b /\ lo <= c /\
  (!id b' c' z'. FLOOKUP sites id = SOME (b',c',z') ==>
     (b' = b /\ c' = c) \/
     ((b'+z' <= b \/ b+z <= b') /\ (c'+z' <= c \/ c+z <= c'))) /\
  word_agree_except (op_taint tn vop) v w /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [p;vop] /\
  eval_operand p s = SOME (n2w (b+j)) /\ eval_operand vop s = SOME v /\
  b+j < dimword (:256) ==>
  ld_memory_agree sites lo (mem_taint tn inst s (mstore (b+j) v s))
    (mstore (b+j) v s).vs_memory (mstore (c+j) w t).vs_memory
Proof
  strip_tac >> drule_all ld_mem_taint_mstore >>
  disch_then (qspec_then `tn` SUBST1_TAC) >> irule ld_memory_agree_mstore_masked >>
  metis_tac[]
QED

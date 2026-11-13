Theory concretizePtrWriteClassification
Ancestors concretizePtrWriteFootprint ptrDiscipline codegenRel venomState
  venomInst memLocDefs arithmetic pred_set list words pair

Theorem ptr_step_write_range:
  x IN range_bytes (step_writes inst s post) <=>
  ?off len. MEM (off,len) (source_memory_write_ranges inst s) /\
    off <= x /\ x < off +
      (if MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL]
       then MIN len (LENGTH post.vs_returndata) else len)
Proof
  simp[step_writes_def, range_bytes_def, MEM_MAP, FORALL_PROD,
    EXISTS_PROD] >>
  Cases_on `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
    inst.inst_opcode = DELEGATECALL` >>
  gvs[MEM_MAP, EXISTS_PROD] >> metis_tac[ADD_COMM]
QED

(* This indexed cursor retains word addition: padding can wrap.  Empty
   entries are ranges too, but cannot supply a byte witness. *)
Definition ptr_dret_cursor_def:
  ptr_dret_cursor (cursor:bytes32) pairs 0 = cursor /\
  ptr_dret_cursor cursor [] (SUC n) = cursor /\
  ptr_dret_cursor cursor ((src,sz)::rest) (SUC n) =
    ptr_dret_cursor (cursor + n2w (ceil32 (w2n sz))) rest n
End

Theorem ptr_dret_range_member:
  MEM (off,len) (dret_source_write_ranges cursor pairs) <=>
  ?n. n < LENGTH pairs /\ off = w2n (ptr_dret_cursor cursor pairs n) /\
    len = w2n (SND (EL n pairs))
Proof
  qid_spec_tac `cursor` >> Induct_on `pairs`
  >- simp[dret_source_write_ranges_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[dret_source_write_ranges_def] >>
  eq_tac
  >- (strip_tac
      >- (qexists_tac `0` >> simp[ptr_dret_cursor_def]) >>
      rename1 `n < LENGTH pairs` >> qexists_tac `SUC n` >>
      simp[ptr_dret_cursor_def]) >>
  strip_tac >> Cases_on `n` >> gvs[ptr_dret_cursor_def] >>
  metis_tac[]
QED

(* A range classification exposes all successful evaluations, including
   values which do not themselves select the destination. *)
Definition ptr_classified_write_range_def:
  ptr_classified_write_range inst s off len <=>
  (?dst value x v.
    MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE] /\
    inst.inst_operands = [dst;value] /\
    eval_operand dst s = SOME x /\ eval_operand value s = SOME v /\
    off = w2n x /\ len = (if inst.inst_opcode = MSTORE8 then 1 else 32)) \/
  (?dst src size x y z.
    MEM inst.inst_opcode [MCOPY;CALLDATACOPY;RETURNDATACOPY;DLOADBYTES;CODECOPY] /\
    inst.inst_operands = [dst;src;size] /\
    eval_operand dst s = SOME x /\ eval_operand src s = SOME y /\
    eval_operand size s = SOME z /\ off = w2n x /\ len = w2n z) \/
  (?addr dst src size a x y z.
    inst.inst_opcode = EXTCODECOPY /\
    inst.inst_operands = [addr;dst;src;size] /\
    eval_operand addr s = SOME a /\ eval_operand dst s = SOME x /\
    eval_operand src s = SOME y /\ eval_operand size s = SOME z /\
    off = w2n x /\ len = w2n z) \/
  (?gas addr value ao az ro rz g a v u n x z.
    inst.inst_opcode = CALL /\
    inst.inst_operands = [gas;addr;value;ao;az;ro;rz] /\
    eval_operand gas s = SOME g /\ eval_operand addr s = SOME a /\
    eval_operand value s = SOME v /\ eval_operand ao s = SOME u /\
    eval_operand az s = SOME n /\ eval_operand ro s = SOME x /\
    eval_operand rz s = SOME z /\ off = w2n x /\ len = w2n z) \/
  (?gas addr ao az ro rz g a u n x z.
    MEM inst.inst_opcode [STATICCALL;DELEGATECALL] /\
    inst.inst_operands = [gas;addr;ao;az;ro;rz] /\
    eval_operand gas s = SOME g /\ eval_operand addr s = SOME a /\
    eval_operand ao s = SOME u /\ eval_operand az s = SOME n /\
    eval_operand ro s = SOME x /\ eval_operand rz s = SOME z /\
    off = w2n x /\ len = w2n z) \/
  (?ordinary dynamic vals pairs.
    inst.inst_opcode = DRET /\
    parse_dret_shape inst = SOME (ordinary,dynamic) /\
    eval_operands inst.inst_operands s = SOME vals /\
    pair_dret_words (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) = SOME pairs /\
    MEM (off,len) (dret_source_write_ranges s.vs_call_entry_fmp pairs))
End

Theorem ptr_source_write_classification:
  MEM (off,len) (source_memory_write_ranges inst s) <=>
    ptr_classified_write_range inst s off len
Proof
  Cases_on `inst.inst_opcode` >>
  simp[source_memory_write_ranges_def, ptr_classified_write_range_def,
    fixed_source_write_range_def, sized_source_write_range_def] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[])
QED

Theorem ptr_step_write_opcode:
  x IN range_bytes (step_writes inst s post) ==>
  MEM inst.inst_opcode
    [MSTORE;MSTORE8;ISTORE;MCOPY;CALLDATACOPY;RETURNDATACOPY;
     DLOADBYTES;CODECOPY;EXTCODECOPY;CALL;STATICCALL;DELEGATECALL;DRET]
Proof
  simp[ptr_step_write_range] >> rpt strip_tac >>
  drule (iffLR ptr_source_write_classification) >>
  simp[ptr_classified_write_range_def] >> metis_tac[]
QED

Theorem ptr_step_write_max_containment:
  mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst t = SOME y /\
  eval_operand sizeop t = SOME z ==>
  !q. q IN range_bytes (step_writes inst t post) ==>
    w2n y <= q /\ q < w2n y + w2n z
Proof
  strip_tac >> simp[ptr_step_write_range] >> rpt strip_tac >>
  drule (iffLR ptr_source_write_classification) >>
  simp[ptr_classified_write_range_def] >> strip_tac >>
  gvs[mem_write_ops_def, eval_operand_def, dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  gvs[MIN_DEF] >> decide_tac
QED

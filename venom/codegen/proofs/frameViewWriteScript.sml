Theory frameViewWrite
Ancestors
  frameViewFacts frameViewMemory frameRel venomState venomMemProps
  venomExecSemantics contextCodegenRel codegenRel list

Theorem expanded_write_frame_view:
  write_memory_with_expansion off bytes (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (write_memory_with_expansion off bytes s) with
    vs_memory := (write_memory_with_expansion off bytes
                    (s with vs_memory := m)).vs_memory
Proof
  simp[write_memory_with_expansion_def, frame_view_def]
QED

Theorem mstore_frame_view:
  mstore off v (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (mstore off v s) with
    vs_memory := (mstore off v (s with vs_memory := m)).vs_memory
Proof
  simp[mstore_eq_write_mem, expanded_write_frame_view]
QED

Theorem mstore8_frame_view:
  mstore8 off v (frame_view fn ra s with vs_memory := m) =
  frame_view fn ra (mstore8 off v s) with
    vs_memory := (mstore8 off v (s with vs_memory := m)).vs_memory
Proof
  simp[mstore8_def, frame_view_def]
QED

val opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun opcode_equation opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    opcode_equations);

Theorem mstore_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE /\ step_inst_base inst s = OK s' ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``MSTORE``, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[opcode_equation ``MSTORE``, exec_write2_def, mstore_frame_view] >>
  qexists_tac `(mstore (w2n addr) val (s with vs_memory := m)).vs_memory` >>
  simp[mstore_eq_write_mem, write_memory_byte_agreement,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       byte_in_memory_range_def] >>
  rpt strip_tac >>
  simp[read_byte_write_memory_with_expansion,
       byteTheory.LENGTH_word_to_bytes]
QED

Theorem mstore8_eq_expanded_write:
  mstore8 off v s = write_memory_with_expansion off [w2w v] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

Theorem mstore8_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE8 /\ step_inst_base inst s = OK s' ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``MSTORE8``, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  simp[opcode_equation ``MSTORE8``, exec_write2_def, mstore8_frame_view] >>
  qexists_tac `(mstore8 (w2n addr) val (s with vs_memory := m)).vs_memory` >>
  simp[mstore8_eq_expanded_write, write_memory_byte_agreement,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       byte_in_memory_range_def] >>
  rpt strip_tac >> simp[read_byte_write_memory_with_expansion]
QED

Theorem istore_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ISTORE /\ step_inst_base inst s = OK s' ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``ISTORE``, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`eval_operand offset_op s = SOME off`,
          `eval_operand val_op s = SOME v`] >>
  qexists_tac `(mstore (w2n off) v (s with vs_memory := m)).vs_memory` >>
  conj_tac
  >- simp[opcode_equation ``ISTORE``, istore_def, mstore_frame_view,
          frame_view_def, mstore_eq_write_mem, write_memory_with_expansion_def] >>
  simp[istore_def, mstore_eq_write_mem, write_memory_byte_agreement,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       byte_in_memory_range_def] >>
  rpt strip_tac >> simp[read_byte_write_memory_with_expansion,
                        byteTheory.LENGTH_word_to_bytes]
QED

Theorem mcopy_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ step_inst_base inst s = OK s' /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``MCOPY``, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [op_dst; op_src; op_size]`,
          `eval_operand op_dst s = SOME dst`,
          `eval_operand op_src s = SOME src`,
          `eval_operand op_size s = SOME sz`] >>
  `TAKE (w2n sz) (DROP (w2n src) m ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n src) s.vs_memory ++ REPLICATE (w2n sz) 0w)` by
    (irule padded_memory_read_cong >> rpt strip_tac >> first_x_assum irule >>
     simp[source_memory_read_byte_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, byte_in_memory_range_def]) >>
  qexists_tac `(mcopy (w2n dst) (w2n src) (w2n sz)
                      (s with vs_memory := m)).vs_memory` >>
  conj_tac
  >- simp[opcode_equation ``MCOPY``, mcopy_def, frame_view_def,
          write_memory_with_expansion_def] >>
  simp[mcopy_def, write_memory_byte_agreement,
       source_memory_write_ranges_def, sized_source_write_range_def,
       byte_in_memory_range_def] >>
  rpt strip_tac >>
  simp[read_byte_write_memory_with_expansion, LENGTH_TAKE]
QED

Theorem codecopy_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = CODECOPY /\ step_inst_base inst s = OK s' ==>
  ?m'. step_inst_base inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``CODECOPY``, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [op_dst; op_src; op_size]`,
          `eval_operand op_dst s = SOME dst`,
          `eval_operand op_src s = SOME src`,
          `eval_operand op_size s = SOME sz`] >>
  qexists_tac `(write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) s.vs_code ++ REPLICATE (w2n sz) 0w))
    (s with vs_memory := m)).vs_memory` >>
  conj_tac
  >- simp[opcode_equation ``CODECOPY``, frame_view_def,
          write_memory_with_expansion_def] >>
  simp[write_memory_byte_agreement, source_memory_write_ranges_def,
       sized_source_write_range_def, byte_in_memory_range_def] >>
  rpt strip_tac >> simp[read_byte_write_memory_with_expansion, LENGTH_TAKE]
QED

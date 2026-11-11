(*
 * Memory-reading steps through the frame view.
 *
 * TOP-LEVEL:
 *   memory_read_step_frame_view — MLOAD, ILOAD, SHA3 and LOG commute with
 *                                 the frame view when the substituted
 *                                 memory agrees on the bytes they read
 *)

Theory frameViewRead
Ancestors
  frameViewScalar frameViewMemory frameViewFacts frameRel venomExecSemantics
  venomState venomInst unitShapeDefs stackPlanGen contextCodegenRel codegenRel list

val opcode_equations = CONJUNCTS step_inst_base_opcode_eqs;
fun opcode_equation opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    opcode_equations);

Theorem load_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [MLOAD; ILOAD] /\ step_inst_base inst s = OK s' /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!x. MEM x inst.inst_outputs ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_assum `inst.inst_opcode = _`
    (fn th => fs[opcode_equation (rhs (concl th))]) >>
  qpat_x_assum `exec_read1 _ inst s = OK s'` mp_tac >>
  simp[exec_read1_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `eval_operand op s = SOME addr` >>
  `TAKE 32 (DROP (w2n addr) m ++ REPLICATE 32 0w) =
   TAKE 32 (DROP (w2n addr) s.vs_memory ++ REPLICATE 32 0w)` by
    (irule padded_memory_read_cong >> rpt strip_tac >> first_x_assum irule >>
     simp[source_memory_read_byte_def, source_memory_read_ranges_def,
          byte_in_memory_range_def]) >>
  simp[exec_read1_def, mload_def, frame_view_update_var, update_var_def,
       frame_view_def]
QED

Theorem sha3_base_frame_view:
  ssa_form fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = SHA3 /\ step_inst_base inst s = OK s' /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!x. MEM x inst.inst_outputs ==> ~retpc_var fn x` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >> simp[] >>
     qexists_tac `inst` >> gvs[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``SHA3``, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename [`inst.inst_operands = [op_off; op_len]`,
          `eval_operand op_off s = SOME off`,
          `eval_operand op_len s = SOME len`] >>
  `TAKE (w2n len) (DROP (w2n off) m ++ REPLICATE (w2n len) 0w) =
   TAKE (w2n len) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n len) 0w)` by
    (irule padded_memory_read_cong >> rpt strip_tac >> first_x_assum irule >>
     simp[source_memory_read_byte_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, byte_in_memory_range_def]) >>
  simp[opcode_equation ``SHA3``, frame_view_update_var, update_var_def,
       frame_view_def]
QED

Theorem log_base_frame_view:
  opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = LOG /\ step_inst_base inst s = OK s' /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  step_inst_base inst (frame_view fn ra s with vs_memory := m) =
  OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra s with vs_memory := m) = eval_operand op s`
    by (rpt strip_tac >> irule eval_operand_frame_view >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> gvs[]) >>
  `!ops. EVERY (\op. MEM op inst.inst_operands) ops ==>
    eval_operands ops (frame_view fn ra s with vs_memory := m) = eval_operands ops s`
    by (rpt strip_tac >> irule eval_operands_frame_view >>
        gvs[EVERY_MEM] >> gen_tac >> disch_tac >>
        irule ordinary_operand_not_retpc >> simp[] >> qexists_tac `inst` >> simp[]) >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[opcode_equation ``LOG``, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = Lit tc::rest` >>
  rename1 `eval_operand (HD (REVERSE rest)) s = SOME off` >>
  rename1 `eval_operand (EL 1 (REVERSE rest)) s = SOME sz` >>
  `MEM (HD (REVERSE rest)) rest` by
    (`0 < LENGTH (REVERSE rest)` by simp[] >>
     `MEM (EL 0 (REVERSE rest)) (REVERSE rest)` by (irule EL_MEM >> simp[]) >>
     gvs[MEM_REVERSE]) >>
  `MEM (EL 1 (REVERSE rest)) rest` by
    (once_rewrite_tac[GSYM MEM_REVERSE] >> irule EL_MEM >> simp[]) >>
  `EVERY (\op. op = Lit tc \/ MEM op rest) (DROP 2 (REVERSE rest))` by
    (simp[EVERY_MEM] >> gen_tac >> disch_tac >> disj2_tac >>
     drule rich_listTheory.MEM_DROP_IMP >> simp[MEM_REVERSE]) >>
  `TAKE (w2n sz) (DROP (w2n off) m ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w)` by
    (irule padded_memory_read_cong >> rpt strip_tac >> first_x_assum irule >>
     simp[source_memory_read_byte_def, source_memory_read_ranges_def,
          memory_range_of_operands_def, byte_in_memory_range_def]) >>
  (* the static-frame guard's undefined-operand case is impossible here *)
  TRY (qpat_x_assum `eval_operands (Lit tc::rest) s = NONE` mp_tac >>
       qspecl_then [`rest`, `s`, `off`, `sz`, `topics`] mp_tac
         venomExecProofsTheory.log_operands_defined >>
       simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
       simp[eval_operands_def, eval_operand_def] >> NO_TAC) >>
  simp[frame_view_def]
QED

Theorem memory_read_step_frame_view:
  step_inst fuel ctx inst s = OK s' /\
  MEM inst.inst_opcode [MLOAD; ILOAD; SHA3; LOG] /\
  codegen_ready_fn fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  (!i. source_memory_read_byte inst s i ==>
       read_byte i m = read_byte i s.vs_memory) ==>
  ?m'. step_inst fuel ctx inst (frame_view fn ra s with vs_memory := m) =
         OK (frame_view fn ra s' with vs_memory := m') /\
       (!i. read_byte i m = read_byte i s.vs_memory ==>
            read_byte i m' = read_byte i s'.vs_memory) /\
       (!i. EVERY (\r. ~byte_in_memory_range r i)
              (source_memory_write_ranges inst s) ==>
            read_byte i m' = read_byte i m)
Proof
  strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst_base inst s = OK s'` by
    (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
     simp[Once step_inst_def]) >>
  `step_inst_base inst (frame_view fn ra s with vs_memory := m) =
   OK (frame_view fn ra s' with vs_memory := m) /\ s'.vs_memory = s.vs_memory` by
    (Cases_on `inst.inst_opcode` >> gvs[]
     >- (irule load_base_frame_view >> simp[])
     >- (irule load_base_frame_view >> simp[])
     >- (irule sha3_base_frame_view >> simp[])
     >> irule log_base_frame_view >> simp[]) >>
  qexists_tac `m` >> simp[Once step_inst_def]
QED

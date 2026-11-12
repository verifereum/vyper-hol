Theory asmOptNonemptyWitness
Ancestors
  asmOptimizer codegenAsmProgOk codegen symbolResolve stackPlanGen
  stackPlanOps planExec asmWf list rich_list

Theorem terminal_encode_nonempty:
  asm_terminal_op t ==> encode_inst offsets t <> []
Proof
  rw[asm_terminal_op_def] >>
  simp[encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def]
QED

Theorem terminal_witness_assemble_nonempty:
  (?pre t post. p = pre ++ t :: post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) ==> assemble p <> []
Proof
  strip_tac >> gvs[assemble_def, pairTheory.UNCURRY, MAP_APPEND, FLAT_APPEND] >>
  metis_tac[terminal_encode_nonempty]
QED

Theorem codegen_assembly_terminal_witness:
  codegen_assembly rpolicy unit = SOME p ==>
  ?pre t post. p = pre ++ t :: post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post
Proof
  rw[codegen_assembly_def, AllCaseEqs()] >>
  gvs[context_plan_ops_def, execute_plan_def, MAP_APPEND, FLAT_APPEND,
      revert_postamble_def, exec_stack_op_def] >>
  qmatch_goalsub_abbrev_tac `FLAT ops` >>
  qexistsl [`FLAT ops ++ [AsmLabel "revert"; AsmPush (encode_num_bytes_fuel 32 0); AsmOp "DUP1"]`,
            `AsmOp "REVERT"`,
            `data_segment_asm unit.cu_data_segment ++ [AsmDataHeader "code_end"]`] >>
  simp[asm_terminal_op_def, GSYM APPEND_ASSOC] >>
  mp_tac (Q.SPEC `unit.cu_data_segment` (GEN_ALL data_suffix_all_data)) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  res_tac >> Cases_on `i` >> gvs[is_data_inst_def]
QED

Theorem peep_swap_pair_filter:
  (!x. asm_swap_op x ==> ~P x) /\
  peep_swap_pair a b c rest = (out,ch) ==>
  FILTER P out = FILTER P (a::b::c::rest)
Proof
  rw[peep_swap_pair_def] >> gvs[] >> metis_tac[]
QED

Theorem peep_swap_comm_filter:
  ~P (AsmOp "SWAP1") /\ peep_swap_comm p = SOME (out,ch) ==>
  FILTER P out = FILTER P p
Proof
  rw[peep_swap_comm_def, AllCaseEqs()] >> gvs[]
QED

Theorem peep_dup_swap_filter:
  ~P (AsmOp "SWAP1") /\ peep_dup_swap p = SOME (out,ch) ==>
  FILTER P out = FILTER P p
Proof
  rw[peep_dup_swap_def, AllCaseEqs()] >> gvs[]
QED

Theorem stack_peephole_opts_filter:
  !p out ch.
  (!x. asm_swap_op x ==> ~P x) /\
  ~P (AsmOp "DUP1") /\ ~P (AsmOp "DUP2") /\ ~P (AsmOp "POP") /\
  stack_peephole_opts p = SOME (out,ch) ==>
  FILTER P out = FILTER P p
Proof
  recInduct stack_peephole_opts_ind >> rpt strip_tac >>
  `~P (AsmOp "SWAP1") /\ ~P (AsmOp "SWAP2")` by
    (gvs[asm_swap_op_def] >> metis_tac[]) >>
  qpat_x_assum `stack_peephole_opts asm = _` mp_tac >>
  simp[Once stack_peephole_opts_def] >>
  simp[AllCaseEqs()] >> strip_tac >> simp[] >>
  gvs[]
  >- (PairCases_on `z` >> gvs[])
  >- (PairCases_on `z` >> gvs[])
  >- (PairCases_on `z` >> gvs[]) >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `FILTER P l3 = FILTER P (a::b::c::rest)` by
    metis_tac[peep_swap_pair_filter, peep_swap_comm_filter, peep_dup_swap_filter] >>
  `l3 <> []` by metis_tac[peep_dup_swap_length] >>
  Cases_on `l3` >> gvs[] >> PairCases_on `z` >> gvs[] >>
  Cases_on `P a` >> Cases_on `P b` >> Cases_on `P c` >> gvs[]
QED

Theorem terminal_witness_cons[local]:
  (?pre t post. h::p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) <=>
  (asm_terminal_op h /\ EVERY (\i. !l. i <> AsmLabel l) p) \/
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  simp[Once EQ_SYM_EQ, APPEND_EQ_CONS] >> metis_tac[]
QED

Theorem terminal_witness_filter:
  (!t. asm_terminal_op t ==> P t) /\ (!l. P (AsmLabel l)) ==>
  ((?pre t post. FILTER P p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) <=>
   (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post))
Proof
  strip_tac >>
  `!xs. EVERY (\i. !l. i <> AsmLabel l) (FILTER P xs) =
        EVERY (\i. !l. i <> AsmLabel l) xs` by
    (simp[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  Induct_on `p` >> simp[] >>
  qx_gen_tac `h` >>
  Cases_on `P h` >>
  pure_asm_rewrite_tac[FILTER, COND_CLAUSES, GSYM APPEND_ASSOC, APPEND,
                       terminal_witness_cons] >>
  gvs[] >> metis_tac[]
QED

Theorem stack_peephole_opts_terminal_witness:
  (?pre t post. p = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post) /\
  stack_peephole_opts p = SOME (out,ch) ==>
  ?pre t post. out = pre ++ t::post /\ asm_terminal_op t /\
    EVERY (\i. !l. i <> AsmLabel l) post
Proof
  strip_tac >>
  qabbrev_tac `keep = \i. asm_terminal_op i \/ ?l. i = AsmLabel l` >>
  `!i. asm_swap_op i ==> ~keep i` by
    (simp[Abbr `keep`, asm_terminal_op_def] >> rpt strip_tac >>
     gvs[asm_swap_op_def]) >>
  `FILTER keep out = FILTER keep p` by
    (irule stack_peephole_opts_filter >>
     simp[Abbr `keep`, asm_terminal_op_def] >> metis_tac[]) >>
  `!xs. (?pre t post. FILTER keep xs = pre ++ t::post /\ asm_terminal_op t /\
          EVERY (\i. !l. i <> AsmLabel l) post) <=>
        (?pre t post. xs = pre ++ t::post /\ asm_terminal_op t /\
          EVERY (\i. !l. i <> AsmLabel l) post)` by
    (gen_tac >> irule terminal_witness_filter >> simp[Abbr `keep`]) >>
  first_assum (qspec_then `out` (fn th => once_rewrite_tac[GSYM th])) >>
  qpat_x_assum `FILTER keep out = _` (fn th => rewrite_tac[th]) >>
  first_x_assum (qspec_then `p` (fn th => rewrite_tac[th])) >>
  qexistsl [`pre`, `t`, `post`] >> simp[]
QED

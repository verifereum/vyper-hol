(* TOP-LEVEL: literal allocation requests read from actual emitted code.
   Membership, nesting and instruction-ID uniqueness provide a concrete
   heterogeneous reservation profile without numerical runtime-ID bounds. *)
Theory compileAllocationRequests
Ancestors
  compileAllocaProvenance compileAllocaProfiles compileIdFlow abiRequestProfile
  localPtrsProps compileEnv fragExec venomInst list pair words pred_set

Definition instruction_alloca_requests_def:
  instruction_alloca_requests inst =
    if inst.inst_opcode = ALLOCA then
      case inst.inst_operands of [Lit size_word] => [(inst.inst_id,w2n size_word)] | _ => []
    else []
End

Definition compiler_alloca_requests_def:
  compiler_alloca_requests before after =
    FLAT (MAP instruction_alloca_requests
      (FILTER (\inst. ~compiler_instruction_member before inst)
        (after.cs_current_insts ++ fn_insts_blocks after.cs_blocks)))
End

Theorem instruction_alloca_requests_member:
  !inst request.
    MEM request (instruction_alloca_requests inst) <=>
    ?size_word. inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\
      request = (inst.inst_id,w2n size_word)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = ALLOCA` >> simp[instruction_alloca_requests_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `inst.inst_operands = operand::rest` >> Cases_on `operand` >> Cases_on `rest` >> simp[]
QED

Theorem compiler_alloca_requests_member:
  !before after request.
    MEM request (compiler_alloca_requests before after) <=>
    ?inst size_word. compiler_instruction_member after inst /\ ~compiler_instruction_member before inst /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit size_word] /\ request = (inst.inst_id,w2n size_word)
Proof
  simp[compiler_alloca_requests_def, MEM_FLAT, MEM_MAP, MEM_FILTER,
    instruction_alloca_requests_member, MEM_APPEND, compiler_blocks_instruction_member,
    compiler_instruction_member_def, PULL_EXISTS] >> metis_tac[]
QED

Theorem compiler_alloca_requests_ids:
  !before after id byte_count.
    MEM (id,byte_count) (compiler_alloca_requests before after) ==>
    MEM id (compiler_alloca_ids before after)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_alloca_requests_member] >>
  disch_then (qx_choose_then `inst` (qx_choose_then `size_word` strip_assume_tac)) >>
  simp_tac bool_ss [compiler_alloca_ids_member] >> qexists_tac `inst` >> gvs[]
QED

Theorem compiler_alloca_requests_literal:
  !before after inst byte_count.
    compiler_instruction_member after inst /\ ~compiler_instruction_member before inst /\
    inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w byte_count)] /\ byte_count < dimword(:256) ==>
    MEM (inst.inst_id,byte_count) (compiler_alloca_requests before after)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [compiler_alloca_requests_member] >>
  qexistsl_tac [`inst`, `n2w byte_count`] >> simp[]
QED

Theorem compiler_alloca_requests_subprofile:
  !before child_before child_after after.
    cs_extends before child_before /\ cs_extends child_after after ==>
    !request. MEM request (compiler_alloca_requests child_before child_after) ==>
      MEM request (compiler_alloca_requests before after)
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `request` >>
  simp_tac bool_ss [compiler_alloca_requests_member] >>
  disch_then (qx_choose_then `inst` (qx_choose_then `size_word` strip_assume_tac)) >>
  `compiler_instruction_member after inst` by
    (qspecl_then [`child_after`, `after`, `inst`] mp_tac compiler_instruction_member_extends >> simp[]) >>
  `~compiler_instruction_member before inst` by
    (DISCH_TAC >> qspecl_then [`before`, `child_before`, `inst`]
      mp_tac compiler_instruction_member_extends >> simp[]) >>
  qexistsl_tac [`inst`, `size_word`] >> simp[]
QED

Theorem compiler_alloca_requests_consistent:
  !before after func.
    cs_extends before after /\ fn_has_code before after func /\ fn_inst_ids_distinct func ==>
    abi_requests_consistent (compiler_alloca_requests before after)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_requests_consistent_def] >>
  MAP_EVERY qx_gen_tac [`id`, `left`, `right`] >> strip_tac >>
  qpat_x_assum `MEM (id,left) _` (mp_tac o REWRITE_RULE [compiler_alloca_requests_member]) >>
  disch_then (qx_choose_then `left_inst` (qx_choose_then `left_word` strip_assume_tac)) >>
  qpat_x_assum `MEM (id,right) _` (mp_tac o REWRITE_RULE [compiler_alloca_requests_member]) >>
  disch_then (qx_choose_then `right_inst` (qx_choose_then `right_word` strip_assume_tac)) >>
  fs[] >>
  `MEM left_inst (fn_insts func)` by
    (qspecl_then [`before`, `after`, `func`, `left_inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  `MEM right_inst (fn_insts func)` by
    (qspecl_then [`before`, `after`, `func`, `right_inst`] mp_tac compiler_new_instruction_member >> simp[]) >>
  `left_inst = right_inst` by
    (qspecl_then [`func`, `left_inst`, `right_inst`] mp_tac fn_inst_ids_distinct_inj >> simp[]) >> gvs[]
QED

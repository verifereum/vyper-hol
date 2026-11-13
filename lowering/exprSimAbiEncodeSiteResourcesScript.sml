Theory exprSimAbiEncodeSiteResources
Ancestors
  exprSimAbiEncodeSiteRecovery exprSimAbiEncodeSiteEncoder abiEncoderAppend
  fragExec exprSimAbiGasBridge
  exprLoweringProps compileEnv venomInst venomWf abiEncoderProps list rich_list

Theorem abi_encode_code_current_members[local]:
  fn_has_code a b f /\ MEM i b.cs_current_insts ==> MEM i (fn_insts f)
Proof
  rw[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >>
  qexistsl [`bb`, `b.cs_current_bb`] >> simp[]
QED

Theorem abi_encode_drop_member[local]:
  MEM i (DROP n xs) ==> MEM i xs
Proof
  simp[MEM_DROP, MEM_EL] >> metis_tac[]
QED

Theorem abi_encode_frag_code_members:
  cs_extends a b /\ fn_has_code a b f /\ MEM i (frag_code a b) ==>
  MEM i (fn_insts f)
Proof
  simp_tac bool_ss [frag_code_def, LET_THM] >>
  IF_CASES_TAC
  >- (simp[emitted_insts_def] >> strip_tac >>
      irule abi_encode_code_current_members >>
      metis_tac[abi_encode_drop_member]) >>
  simp[MEM_APPEND, MEM_FLAT, MEM_MAP] >> strip_tac
  >- (irule lookup_block_fn_insts >>
      qexistsl [`LAST (emitted_blocks a b)`, `(LAST (emitted_blocks a b)).bb_label`] >>
      fs[fn_has_code_def] >> metis_tac[MEM_LAST_NOT_NIL, NULL_EQ, abi_encode_drop_member])
  >- (irule lookup_block_fn_insts >>
      qexistsl [`bb`, `bb.bb_label`] >>
      fs[fn_has_code_def] >> metis_tac[MEM_FRONT_NOT_NIL, NULL_EQ]) >>
  metis_tac[abi_encode_code_current_members]
QED

Theorem abi_encode_observer_scratch_site:
  site_step ready body_end /\ cs_extends ready body_end /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce earlier /\ earlier.cs_next_var <= ready.cs_next_var /\
  MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA /\
  i.inst_id IN frag_ids ready body_end ==>
  MEM i (fn_insts func) /\
  ?q. i.inst_operands = [Lit 32w] /\ i.inst_outputs = [q] /\
      not_local_ptr ce scopes q
Proof
  strip_tac >>
  `!j. MEM j (frag_code ready body_end) ==> MEM j (fn_insts obs)` by
    metis_tac[abi_encode_frag_code_members] >>
  `local_ptrs_reserved ce ready` by metis_tac[local_ptrs_reserved_next_var] >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) (fn_insts obs))` by
    (`!bbs. MAP (\j. j.inst_id) (fn_insts_blocks bbs) =
       FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) bbs)` by
       (Induct >> simp[fn_insts_blocks_def]) >>
     fs[fn_inst_ids_distinct_def, fn_insts_def]) >>
  `ready.cs_next_id <= i.inst_id /\ i.inst_id < body_end.cs_next_id` by
    fs[frag_ids_def] >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  drule_all site_interval_alloca_not_local >> simp[]
QED

Theorem abi_encode_compiled_scratch_site:
  compile_abi_encode_to_buf dst src ei ready = (out,body_end) /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
       j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  local_ptrs_reserved ce earlier /\ earlier.cs_next_var <= ready.cs_next_var /\
  MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA /\
  i.inst_id IN frag_ids ready body_end ==>
  MEM i (fn_insts func) /\
  ?q. i.inst_operands = [Lit 32w] /\ i.inst_outputs = [q] /\
      not_local_ptr ce scopes q
Proof
  strip_tac >> irule abi_encode_observer_scratch_site >>
  drule abi_encode_body_site_step >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

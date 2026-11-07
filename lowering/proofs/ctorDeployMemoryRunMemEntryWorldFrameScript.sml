Theory ctorDeployMemoryRunMemEntryWorldFrame
Ancestors
  venomExecSemantics venomState venomInstProps list fragGasPathMem fragExec

Theorem ctor_prefix_step_world:
  step_inst fuel ctx inst s = OK t /\
  MEM inst.inst_opcode
    [ADD; SUB; MUL; Div; Mod; EQ; LT; GT; ISZERO; AND; OR; XOR; NOT;
     SHL; SHR; SAR; SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY;
     ASSIGN; ALLOCA; DLOAD; DLOADBYTES; CALLVALUE; ASSERT; JMP; JNZ] ==>
  t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >>
  gvs[MEM] >>
  fs[Once step_inst_def] >>
  fs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_read0_def, exec_read1_def,
      exec_write2_def, exec_alloca_def, AllCaseEqs()] >>
  simp[update_var_def, jump_to_def, mstore_def, mstore8_def,
       mcopy_def, write_memory_with_expansion_def]
QED

Theorem ctor_prefix_phis_world:
  !insts s t. eval_phis s insts = OK t ==>
  t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def] >>
  first_x_assum drule >> simp[]
QED

Theorem ctor_prefix_jump_world:
  (jump_to lbl s).vs_tx_ctx = s.vs_tx_ctx /\
  (jump_to lbl s).vs_block_ctx = s.vs_block_ctx /\
  (jump_to lbl s).vs_outcomes = s.vs_outcomes
Proof
  simp[jump_to_def]
QED

Theorem ctor_prefix_index_world:
  (s with vs_inst_idx := n).vs_tx_ctx = s.vs_tx_ctx /\
  (s with vs_inst_idx := n).vs_block_ctx = s.vs_block_ctx /\
  (s with vs_inst_idx := n).vs_outcomes = s.vs_outcomes
Proof
  simp[]
QED

Theorem ctor_prefix_path_invariant:
  !P ctx func s n t.
    gas_path_mem ctx func s n (OK t) /\ P s /\
    (!u k v. P u /\ gas_path_mem_edge ctx func u k (OK v) ==> P v) ==>
    P t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
  qid_spec_tac `t` >>
  `!cx fn a k r. gas_path_mem cx fn a k r ==>
     !b. r = OK b ==> P a ==>
       (!u j v. P u /\ gas_path_mem_edge cx fn u j (OK v) ==> P v) ==>
       P b` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >>
      qpat_x_assum `!b. r = OK b ==> _` irule >>
      simp[] >> metis_tac[])
  >> rpt strip_tac >> gvs[exit_result_def]
QED

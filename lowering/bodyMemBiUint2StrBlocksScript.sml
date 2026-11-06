(* Memory checks for the concrete uint2str instruction templates. *)
Theory bodyMemBiUint2StrBlocks
Ancestors
  bodyMemBiUint2StrBounds exprSimUint2Str fragExecMem instMemFrontier
  memSafeRun venomInst venomState finite_map list rich_list
  venomExecSemantics exprLoweringProps

Theorem u2s_control_mem_ok:
  run_inst_seq_mem_ok (u2s_setup a op buf) s /\
  run_inst_seq_mem_ok (u2s_check a) s /\
  run_inst_seq_mem_ok (u2s_cond a) s
Proof
  rpt conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_setup_def, u2s_check_def, u2s_cond_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_body_nonstore_mem_ok[local]:
  run_inst_seq_mem_ok (TAKE 4 (u2s_body a buf n)) s /\
  run_inst_seq_mem_ok (DROP 5 (u2s_body a buf n)) s
Proof
  conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_body_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_body_mem_ok:
  eval_operand (Var (u2s_var a 0)) s = SOME xw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  eval_operand buf s = SOME bw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw + n2w n - iw) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (u2s_body a buf n) s
Proof
  strip_tac >>
  `u2s_body a buf n = TAKE 4 (u2s_body a buf n) ++
    DROP 4 (u2s_body a buf n)` by simp[] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_body_nonstore_mem_ok] >> rpt strip_tac >>
  drule_all u2s_body_address_run >> strip_tac >> gvs[] >>
  `DROP 4 (u2s_body a buf n) =
    [EL 4 (u2s_body a buf n)] ++ DROP 5 (u2s_body a buf n)` by
    simp[u2s_body_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_body_nonstore_mem_ok, run_inst_seq_mem_ok_last,
       u2s_body_def, u2s_inst_def, below_frontier_MSTORE,
       inst_dload_in_section_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def]
QED

Theorem u2s_final_address_run[local]:
  eval_operand buf s = SOME bw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  (!z. buf = Var z ==> not_fresh_at a z) ==>
  run_inst_seq (TAKE 2 (u2s_final a buf n)) s =
    OK (update_var (u2s_var a 15) (bw+n2w n-iw)
      (update_var (u2s_var a 14) (bw+n2w n) s))
Proof
  strip_tac >>
  simp[u2s_final_def, u2s_inst_def, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_pure2_def,
       eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem u2s_final_nonstore_mem_ok[local]:
  run_inst_seq_mem_ok (TAKE 2 (u2s_final a buf n)) s /\
  run_inst_seq_mem_ok (DROP 3 (u2s_final a buf n)) s
Proof
  conj_tac >> irule run_inst_seq_mem_ok_every >>
  simp[u2s_final_def, u2s_inst_def] >>
  rpt conj_tac >> rpt gen_tac >>
  simp[inst_dload_in_section_def, mk_inst_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem u2s_final_mem_ok:
  eval_operand buf s = SOME bw /\
  eval_operand (Var (u2s_var a 1)) s = SOME iw /\
  (!z. buf = Var z ==> not_fresh_at a z) /\
  w2n (bw + n2w n - iw) + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (u2s_final a buf n) s
Proof
  strip_tac >>
  `u2s_final a buf n = TAKE 2 (u2s_final a buf n) ++
    DROP 2 (u2s_final a buf n)` by simp[] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_final_nonstore_mem_ok] >> rpt strip_tac >>
  drule_all u2s_final_address_run >> strip_tac >> gvs[] >>
  `DROP 2 (u2s_final a buf n) =
    [EL 2 (u2s_final a buf n)] ++ DROP 3 (u2s_final a buf n)` by
    simp[u2s_final_def] >>
  pop_assum (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_mem_ok_append >>
  simp[u2s_final_nonstore_mem_ok, run_inst_seq_mem_ok_last,
       u2s_final_def, u2s_inst_def, below_frontier_MSTORE,
       inst_dload_in_section_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[mk_inst_def]
QED


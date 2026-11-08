Theory bodyPtrPrecompileBuiltinsLoad
Ancestors typedCopyPtr fragGasSeqPtr fragGasPathPtr bodyPtrDefs
          memLocDefs contextCodegenRel codegenRel exprLoweringProps
          ptrDiscipline ptrSafeRun ptrCoverage compileEnv venomInst
          venomState venomInstProofs venomExecSemantics finite_map

(* The toolkit's fixed lower bound is zero. MLOAD itself does not inspect
   allocation lower bounds; the global allocation check is supplied explicitly. *)
Theorem mload_check_at[local]:
  ptr_covers G tn x s 32 /\ ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id MLOAD [Var x] [y]) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[mem_read_ops_def]) >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds, opcode_case_def, combinTheory.K_THM] >>
  simp[exec_read1_def, eval_operand_def, AllCaseEqs(), mload_def,
       update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem clean_mload_path:
 !D lo ctx fn PG G tn s t x y id bb.
 step_inst_base (mk_inst id MLOAD [Var x] [y]) s = OK t /\
 ptr_covers G tn x s 32 /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
 (!w. lookup_var x s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
 ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 isPREFIX [mk_inst id MLOAD [Var x] [y]]
   (DROP s.vs_inst_idx bb.bb_instructions) ==>
 gas_path_ptr D lo ctx fn PG G tn s 0
   (step_prov PG G (mk_inst id MLOAD [Var x] [y]) t)
   (step_taint (mk_inst id MLOAD [Var x] [y]) s t tn)
   (OK (t with vs_inst_idx := s.vs_inst_idx + 1)) /\
 op_prov (step_prov PG G (mk_inst id MLOAD [Var x] [y]) t) (Var y) = NONE /\
 op_taint (step_taint (mk_inst id MLOAD [Var x] [y]) s t tn) (Var y) = {}
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (`inst_seq_ptr D lo ctx fn PG G tn [mk_inst id MLOAD [Var x] [y]] s
         (step_prov PG G (mk_inst id MLOAD [Var x] [y]) t)
         (step_taint (mk_inst id MLOAD [Var x] [y]) s t tn)` by
        (simp[inst_seq_ptr_def] >> irule mload_check_at >> simp[]) >>
      `run_inst_seq [mk_inst id MLOAD [Var x] [y]] s = OK t` by
        simp[run_inst_seq_def] >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        [mk_inst id MLOAD [Var x] [y]]` by simp[mk_inst_def, is_terminator_def] >>
      drule_all run_inst_seq_gas_path_ptr >>
      simp[mk_inst_def, is_terminator_def]) >>
  conj_tac
  >- simp[op_prov_def, step_prov_def, out_prov_def, mk_inst_def,
          set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  `?a. lookup_var x s = SOME a` by fs[ptr_covers_def] >>
  `t = update_var y (mload (w2n a) s) s` by
    (gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
         eval_operand_def]) >>
  gvs[] >> irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def]
QED

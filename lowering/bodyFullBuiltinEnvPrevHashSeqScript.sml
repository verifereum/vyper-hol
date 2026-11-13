(* Horizon-uniform scalar ghost execution for Env PrevHash. *)
Theory bodyFullBuiltinEnvPrevHashSeq
Ancestors
  builtinProps fragGasSeqPtr bodyFullGhostFrame exprLowering exprLoweringProps emitHelper
  emitHelperProps compileEnv loweringStateRelDefs ptrDiscipline venomState
  venomInst venomExecSemantics finite_map list rich_list fragExecMem
  allocaHistoryFragment instMemFrontier memSafeRun loweringSlice contextCodegenRel codegenRel ptrSafeRun bodyPtrDefs

Theorem env_prevhash_seq_ghosts:
 compile_env_var PrevHash sa = (op,sb) /\ fresh_vars_wrt sa s /\
 run_inst_seq (emitted_insts sa sb) s = OK t /\
 local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
 (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
 (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)
 ==> ?G' tn'.
 run_inst_seq_mem_ok (emitted_insts sa sb) s /\
 op_prov G' op = NONE /\ op_taint tn' op = {} /\
 (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
 (!D lo. ghost_inv_at D lo d cenv cx es G tn s ==>
   inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
   ghost_inv_at D lo d cenv cx es G' tn'
     (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
 strip_tac >>
 gvs[compile_env_var_def, emit_op_def, comp_bind_def, fresh_var_def,
     fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
     emitted_insts_def] >>
 RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
 pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
 gvs[] >>
 qmatch_goalsub_abbrev_tac `mk_inst iid NUMBER [] [v0]` >>
 qmatch_goalsub_abbrev_tac `mk_inst iid1 SUB _ [v1]` >>
 qmatch_goalsub_abbrev_tac `mk_inst iid2 BLOCKHASH _ [v2]` >>
 qexistsl_tac [`DRESTRICT G (COMPL {v0;v1;v2})`,
   `tn with t_var := tn.t_var |+ (v0,{}) |+ (v1,{}) |+ (v2,{})`] >>
 `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1 /\ x <> v2` by
   (simp[Abbr `v0`, Abbr `v1`, Abbr `v2`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
 simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
 conj_tac
 >- (irule run_inst_seq_mem_ok_every >>
     simp[MEM, mk_inst_def, inst_dload_in_section_def] >>
     rpt strip_tac >> irule below_frontier_no_ranges >>
     simp[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
 rpt gen_tac >> strip_tac >>
 fs[run_inst_seq_def, step_inst_base_opcode_eqs, exec_read0_def,
    exec_pure2_def, exec_read1_def, mk_inst_def, eval_operands_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
 conj_tac
 >- (simp[Once inst_seq_ptr_def] >>
     simp[step_inst_base_opcode_eqs, exec_read0_def,
       exec_pure2_def, exec_read1_def, eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, step_taint_def, out_taint_def, set_var_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def] >>
     FAIL_TAC "ptr checks") >>
 FAIL_TAC "exterior frame"
QED

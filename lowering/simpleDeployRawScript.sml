(* Raw execution of the three-instruction constructor-free entry. *)
Theory simpleDeployRaw
Ancestors
  ctorDeployLoweringNoCtor ctorDeployMemoryRunMemNoCtor ctorDeployMemoryRunPtrNoCtor
  runFromGasPathMem fragGasPathMem fragExec memSafeRun gasCount ptrDiscipline
  vyperCompiler venomExecSemantics venomExecProps venomInst venomState list finite_map words

(* A function with no GAS and no INVOKE counts no reads on any path. *)
Theorem gas_path_mem_gas_free:
  !ctx fn s n r.
    gas_path_mem ctx fn s n r ==>
    (!bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions ==>
            i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) ==>
    n = 0
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[gas_path_mem_edge_def] >>
  `MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()] >>
     metis_tac[lookup_block_MEM, EL_MEM]) >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `!bb i. _`
       (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
  gvs[gas_count_step_def] >> metis_tac[]
QED

Theorem simple_deploy_raw_execution:
  ctx = install_immutable_reservation imm
    (mk_venom_context [fn] (SOME "__deploy")) /\
  fn = mk_raw_function "__deploy" [<|bb_label := "__deploy";
    bb_instructions :=
      [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bs))] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit (n2w (LENGTH bs))] [];
       mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bs))] []]|>] /\
  vs.vs_allocas = FEMPTY /\ ~vs.vs_halted /\
  imm <= vs.vs_alloca_next /\ vs.vs_alloca_next < dimword (:256) /\
  LENGTH bs < dimword (:256) /\ off < dimword (:256) /\
  FLOOKUP vs.vs_labels "runtime_begin" = SOME (n2w off) /\
  TAKE (LENGTH bs) (DROP off vs.vs_code ++ REPLICATE (LENGTH bs) 0w) = bs ==>
  ?post. run_context 1 ctx vs = Halt post /\ post.vs_returndata = bs /\
    post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
    post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
    post.vs_requests = vs.vs_requests /\
    gas_path_mem ctx fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
      0 (Halt post) /\
    (!D fuel. ptr_safe_blocks D imm fuel ctx fn [] FEMPTY entry_taint
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `vs`,`imm` |-> `imm`,`bytes` |-> `bs`,
                  `codepos` |-> `off`] no_ctor_simple_context_execution) >>
  simp[] >> disch_then (qx_choose_then `post` strip_assume_tac) >>
  qexists_tac `post` >> asm_rewrite_tac[] >>
  qabbrev_tac `start = vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                                  vs_inst_idx := 0|>` >>
  qabbrev_tac `bb = <|bb_label := "__deploy";
    bb_instructions :=
      [mk_inst 0 ALLOCA [Lit (n2w (LENGTH bs))] ["%0"];
       mk_inst 1 CODECOPY [Var "%0"; Label "runtime_begin"; Lit (n2w (LENGTH bs))] [];
       mk_inst 2 RETURN [Var "%0"; Lit (n2w (LENGTH bs))] []]|>` >>
  `fn = mk_raw_function "__deploy" [bb]` by simp[Abbr `bb`] >>
  `ctx.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__deploy"` by
    simp[Abbr `bb`, install_immutable_reservation_def, mk_venom_context_def,
         lookup_function_def, FIND_def, INDEX_FIND_def, mk_raw_function_def,
         fn_entry_label_def, entry_block_def] >>
  `lookup_block start.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0` by
    simp[Abbr `start`, Abbr `bb`, mk_raw_function_def, lookup_block_def,
         FIND_def, INDEX_FIND_def, phi_prefix_length_def, mk_inst_def] >>
  `start with vs_inst_idx := 0 = start` by simp[Abbr `start`] >>
  `run_blocks 1 ctx fn start = Halt post` by
    (mp_tac (Q.SPECL [`1`,`ctx`,`vs`,`"__deploy"`,`fn`,`"__deploy"`]
       run_context_run_blocks) >>
     simp[GSYM markerTheory.Abbrev_def, GSYM arithmeticTheory.ONE]) >>
  `run_from 0 ctx fn start = Halt post` by
    metis_tac[run_blocks_run_from_no_phi, arithmeticTheory.ONE] >>
  `mem_safe_blocks 1 ctx fn start` by
    (simp[Abbr `start`, Abbr `bb`] >> irule simple_deploy_entry_mem_safe >> simp[]) >>
  `mem_safe_run 0 ctx fn start` by
    metis_tac[mem_safe_blocks_run, eval_phis_no_phi, arithmeticTheory.ONE] >>
  `?n. gas_path_mem ctx fn start n (Halt post)` by
    (irule run_from_gas_path_mem >> simp[exit_result_def, Abbr `start`] >>
     metis_tac[]) >>
  `!block inst. MEM block fn.fn_blocks /\ MEM inst block.bb_instructions ==>
     inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (simp[mk_raw_function_def, Abbr `bb`] >> rpt strip_tac >> gvs[mk_inst_def]) >>
  conj_tac
  >- metis_tac[gas_path_mem_gas_free] >>
  `~ctx_has_dalloca ctx` by
     simp[ctx_has_dalloca_def, install_immutable_reservation_def, mk_venom_context_def,
          mk_raw_function_def, fn_insts_def, fn_insts_blocks_def,
          combinTheory.o_DEF, Abbr `bb`, mk_inst_def] >>
  rpt gen_tac >>
  qspecl_then [`D`,`imm`,`ctx`,`n2w (LENGTH bs):256 word`,`vs`]
    mp_tac simple_deploy_entry_ptr_safe >>
  simp[Abbr `start`, Abbr `bb`]
QED

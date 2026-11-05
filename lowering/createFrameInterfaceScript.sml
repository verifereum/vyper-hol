Theory createFrameInterface
Ancestors
  list rich_list fragExec emitHelperProps builtinCreate rawCreateContractProbe
  vyperCompiler venomState venomExecSemantics venomInst compileEnv emitHelper
  venomMemProps

(* A live operand carries its VALUE, not just its definedness. In particular,
   salts and constructor-tuple pointers belong in this list. *)
Definition create_live_def:
  create_live live s <=>
    EVERY (\(op,w). eval_operand op s = SOME w) live
End

Definition create_operand_entry_def:
  create_operand_entry cs live s <=>
    fresh_vars_wrt cs s /\ create_live live s
End

Theorem create_live_update_fresh:
  create_operand_entry cs live s /\ cs.cs_next_var <= n ==>
  create_live live (update_var (STRING #"%" (toString n)) w s)
Proof
  rw[create_operand_entry_def, create_live_def, EVERY_MEM] >>
  PairCases_on `e` >> gvs[] >>
  first_x_assum (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  irule eval_operand_update_fresh >> simp[] >>
  qexists_tac `cs` >> simp[]
QED

(* General callback frame: s' may have arbitrary changes to source-owned
   state, but private saved operands retain their original values. Memory
   snapshot framing is a separate obligation, not implied by this frame. *)
Definition create_operand_frame_def:
  create_operand_frame live before after <=>
    create_live live before /\ create_live live after
End

Theorem create_live_frame_trans:
  create_operand_frame live s1 s2 /\
  create_operand_frame live s2 s3 ==>
  create_operand_frame live s1 s3
Proof
  simp[create_operand_frame_def]
QED

Theorem create_operand_entry_rejects_missing_salt:
  ~create_operand_entry (initial_compile_state "entry")
     [(Var "missing_salt", salt)] (init_venom_state "entry")
Proof
  simp[create_operand_entry_def, create_live_def, eval_operand_def,
       lookup_var_def, init_venom_state_def]
QED

(* A scheduled callback gets its ordinary source simulation in source_pre,
   source_normal and source_exit. It is permitted to exit exceptionally;
   no successful evaluation of the callback/pipeline is assumed. Private
   snapshots are supplied by saved and must be framed on NORMAL return.
   The result can be an operand or a located VyperValue. *)
Definition create_callback_spec_def:
  create_callback_spec ctx (callback : 'a compiler)
      source_pre source_normal source_exit live saved <=>
    !cs op cs'. callback cs = (op,cs') ==>
      cs_extends cs cs' /\
      frag_exec ctx cs cs'
        (\s. source_pre cs s /\ create_live live s /\ saved s)
        (\s. source_normal op cs' s /\ create_live live s /\ saved s)
        source_exit
End

(* Concrete generated CFG: put a STOP continuation in the current success
   block. REVERSE cs_blocks restores emission order. Neither test runs just
   emitted_insts, which is empty after the final new_block. *)
Definition create_check_probe_fn_def:
  create_check_probe_fn addr =
    let cs = SND (compile_check_create_result (Lit addr) T
                    (initial_compile_state "entry")) in
    <| fn_name := "probe";
       fn_blocks := REVERSE cs.cs_blocks ++
         [<| bb_label := cs.cs_current_bb;
             bb_instructions := cs.cs_current_insts ++
                [mk_inst cs.cs_next_id STOP [] []] |>] |>
End

Theorem create_check_probe_contains_code:
  fn_has_code (initial_compile_state "entry")
    (SND (compile_check_create_result (Lit addr) T
      (initial_compile_state "entry"))) (create_check_probe_fn addr)
Proof
  EVAL_TAC >> rpt conj_tac >> rpt strip_tac >>
  gvs[] >> rule_assum_tac (CONV_RULE EVAL) >> gvs[] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >>
  simp[Once EQ_SYM_EQ]
QED

Theorem create_check_probe_fn_normalized:
  create_check_probe_fn addr =
    <| fn_name := "probe";
       fn_blocks :=
       [<|bb_label := "entry";
          bb_instructions := [mk_inst 0 JNZ
             [Lit addr; Label "@create_ok_1"; Label "@create_fail_0"] []]|>;
        <|bb_label := "@create_fail_0";
          bb_instructions :=
            [mk_inst 1 RETURNDATASIZE [] ["%0"];
             mk_inst 2 ALLOCA [Lit 0w] ["%1"];
             mk_inst 3 RETURNDATACOPY [Var "%1"; Lit 0w; Var "%0"] [];
             mk_inst 4 REVERT [Var "%1"; Var "%0"] []]|>;
        <|bb_label := "@create_ok_1";
          bb_instructions := [mk_inst 5 STOP [] []]|>] |>
Proof
  EVAL_TAC
QED

Theorem create_check_branch_step:
  s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  exec_block fuel ctx
    <|bb_label := "entry";
      bb_instructions := [mk_inst 0 JNZ
        [Lit addr; Label "@create_ok_1"; Label "@create_fail_0"] []]|> s =
    OK (jump_to (if addr = 0w then "@create_fail_0" else "@create_ok_1") s)
Proof
  strip_tac >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def,
       step_inst_def, step_inst_base_def, eval_operand_def,
       is_terminator_def, jump_to_def] >>
  Cases_on `addr = 0w` >> simp[]
QED

Theorem create_check_stop_step:
  s.vs_inst_idx = 0 ==>
  exec_block fuel ctx
    <|bb_label := "@create_ok_1";
      bb_instructions := [mk_inst 5 STOP [] []]|> s = Halt (halt_state (set_returndata [] s))
Proof
  strip_tac >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def,
       step_inst_def, step_inst_base_def, is_terminator_def, halt_state_def,
       set_returndata_def]
QED

Theorem create_check_success_traverses_cfg:
  s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\
  ~s.vs_halted /\ addr <> 0w ==>
  run_from 3 ctx (create_check_probe_fn addr) s =
    Halt (halt_state (set_returndata [] (jump_to "@create_ok_1" s)))
Proof
  strip_tac >>
  simp[run_from_def, create_check_probe_fn_normalized, lookup_block_def,
       FIND_def, INDEX_FIND_def, create_check_branch_step, jump_to_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_def, INDEX_FIND_def,
       eval_phis_def, phi_prefix_length_def] >>
  simp[create_check_stop_step, halt_state_def, set_returndata_def,
       jump_to_def, mk_inst_def]
QED

Definition create_check_revert_bb_def:
  create_check_revert_bb =
    <|bb_label := "@create_fail_0";
      bb_instructions :=
        [mk_inst 1 RETURNDATASIZE [] ["%0"];
         mk_inst 2 ALLOCA [Lit 0w] ["%1"];
         mk_inst 3 RETURNDATACOPY [Var "%1"; Lit 0w; Var "%0"] [];
         mk_inst 4 REVERT [Var "%1"; Var "%0"] []]|>
End

Theorem create_revert_read_written[local]:
  TAKE (LENGTH bytes)
    (DROP offset (write_memory_with_expansion offset bytes s).vs_memory ++
     REPLICATE (LENGTH bytes) 0w) = bytes
Proof
  `LENGTH bytes <= LENGTH
      (DROP offset (write_memory_with_expansion offset bytes s).vs_memory)` by
    (simp[LENGTH_DROP, LENGTH_write_memory_with_expansion,
          arithmeticTheory.MAX_DEF] >> IF_CASES_TAC >> decide_tac) >>
  fs[LENGTH_DROP, TAKE_APPEND, write_memory_with_expansion_read_self]
QED

Theorem create_revert_write_frame[local,simp]:
  (write_memory_with_expansion off bytes s).vs_vars = s.vs_vars ∧
  (write_memory_with_expansion off bytes s).vs_current_bb = s.vs_current_bb ∧
  (write_memory_with_expansion off bytes s).vs_inst_idx = s.vs_inst_idx ∧
  (write_memory_with_expansion off bytes s).vs_returndata = s.vs_returndata ∧
  (write_memory_with_expansion off bytes s).vs_halted = s.vs_halted
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem create_check_revert_block:
  s.vs_inst_idx = 0 /\ LENGTH s.vs_returndata < dimword(:256) ==>
  ?t. exec_block fuel ctx create_check_revert_bb s = Abort Revert_abort t /\
      t.vs_returndata = s.vs_returndata /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_halted
Proof
  strip_tac >>
  simp[create_check_revert_bb_def, Once exec_block_def,
       get_instruction_def, mk_inst_def, step_inst_def, step_inst_base_def,
       exec_read0_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def,
       update_var_def, eval_operand_def, lookup_var_def,
       step_inst_def, step_inst_base_def, is_terminator_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP s.vs_allocas 2` >>
  TRY (rename1 `FLOOKUP s.vs_allocas 2 = SOME allocation` >>
       PairCases_on `allocation`) >>
  simp[exec_alloca_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_def, step_inst_base_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, mk_inst_def] >>
  simp[step_inst_def, step_inst_base_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[create_revert_read_written, revert_state_def, set_returndata_def,
       finite_mapTheory.FLOOKUP_UPDATE, is_terminator_def]
QED

Theorem create_check_failure_traverses_cfg:
  s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  LENGTH s.vs_returndata < dimword(:256) ==>
  ?t. run_from 3 ctx (create_check_probe_fn 0w) s = Abort Revert_abort t /\
      t.vs_returndata = s.vs_returndata /\
      t.vs_current_bb = "@create_fail_0" /\ t.vs_halted
Proof
  strip_tac >>
  simp[run_from_def, create_check_probe_fn_normalized, lookup_block_def,
       FIND_def, INDEX_FIND_def, create_check_branch_step, jump_to_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_def, INDEX_FIND_def,
       eval_phis_def, phi_prefix_length_def] >>
  qmatch_goalsub_abbrev_tac `exec_block 2 ctx bb entered` >>
  `bb = create_check_revert_bb` by simp[Abbr `bb`, create_check_revert_bb_def] >>
  `entered.vs_inst_idx = 0 /\ entered.vs_returndata = s.vs_returndata` by
    simp[Abbr `entered`] >>
  `?t. exec_block 2 ctx bb entered = Abort Revert_abort t /\
       t.vs_returndata = s.vs_returndata /\
       t.vs_current_bb = "@create_fail_0" /\ t.vs_halted` by
    (gvs[] >> drule create_check_revert_block >>
     disch_then (qspecl_then [`2`, `ctx`] mp_tac) >>
     simp[Abbr `entered`]) >>
  simp[]
QED

Theorem create_check_failure_empty_returndata:
  s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  s.vs_returndata = [] ==>
  ?t. run_from 3 ctx (create_check_probe_fn 0w) s = Abort Revert_abort t /\
      t.vs_returndata = []
Proof
  strip_tac >>
  drule create_check_failure_traverses_cfg >> simp[] >> metis_tac[]
QED

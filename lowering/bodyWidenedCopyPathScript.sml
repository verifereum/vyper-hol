Theory bodyWidenedCopyPath
Ancestors
  placeMemoryForwardPath fragGasMode fragGasPathMem gasCount memSafeRun
  venomExecSemantics venomExecProofs venomState arithmetic instMemFrontier

Theorem gas_marked_path_zero_iteration_mode:
  !memory (n:num) i loop_inv Q ctx func s.
  i <= n /\ loop_inv i s /\
  (!j u. j < n /\ loop_inv j u ==>
    ?v. gas_marked_path memory ctx func u 0 (OK v) /\ loop_inv (SUC j) v) /\
  (!u. loop_inv n u ==>
    ?v. gas_marked_path memory ctx func u 0 (OK v) /\ Q v) ==>
  ?t. gas_marked_path memory ctx func s 0 (OK t) /\ Q t
Proof
  gen_tac >> completeInduct_on `(n:num) - i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- metis_tac[] >>
  `i < n` by decide_tac >>
  `?v. gas_marked_path memory ctx func s 0 (OK v) /\ loop_inv (SUC i) v`
    by metis_tac[] >>
  rename1 `loop_inv (SUC i) next` >>
  `?t. gas_marked_path memory ctx func next 0 (OK t) /\ Q t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `n - SUC i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`n`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     qexists_tac `loop_inv` >> simp[]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD]
QED

Theorem gas_marked_path_zero_jump_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> GAS /\
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path T ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_mem_edge ctx func s 0 (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_mem_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, gas_count_step_def,
          mem_safe_step_non_invoke] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  simp[gas_marked_path_def] >>
  metis_tac[gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem typed_copy_control_mem_checks:
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ) ==>
  inst_mem_below_frontier inst s /\ inst_dload_in_section inst s
Proof
  strip_tac >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

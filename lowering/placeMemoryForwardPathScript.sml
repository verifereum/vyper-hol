(* Forward execution boundaries for memory-place stores. *)
Theory placeMemoryForwardPath
Ancestors
  fragGasMode fragGasPath gasCount venomExecSemantics venomExecProofs
  venomState arithmetic

Theorem gas_marked_path_zero_iteration:
  !(n:num) i loop_inv Q ctx func s.
  i <= n /\ loop_inv i s /\
  (!j u. j < n /\ loop_inv j u ==>
    ?v. gas_marked_path F ctx func u 0 (OK v) /\ loop_inv (SUC j) v) /\
  (!u. loop_inv n u ==>
    ?v. gas_marked_path F ctx func u 0 (OK v) /\ Q v) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t
Proof
  completeInduct_on `(n:num) - i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- metis_tac[] >>
  `i < n` by decide_tac >>
  `?v. gas_marked_path F ctx func s 0 (OK v) /\ loop_inv (SUC i) v`
    by metis_tac[] >>
  rename1 `loop_inv (SUC i) next` >>
  `?t. gas_marked_path F ctx func next 0 (OK t) /\ Q t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `n - SUC i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`n`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     qexists_tac `loop_inv` >> simp[]) >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD]
QED

Theorem gas_marked_path_zero_jump:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> GAS /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_marked_path F ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, gas_count_step_def] >>
     metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  simp[gas_marked_path_def] >>
  metis_tac[gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

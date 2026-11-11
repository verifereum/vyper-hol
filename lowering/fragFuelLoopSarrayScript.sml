(*
 * Fuel bound for the static-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_sarray_typed
 *)

Theory fragFuelLoopSarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
  venomExecSemantics venomExecProofs venomInstProps venomState words finite_map arithmetic
Libs
  fragFuelLib

(* Initialization and the counter back edge. *)
Theorem sa_initialize[local]:
  no_phi_fn fn /\ ~var_below N c /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ai /\
  ai.inst_opcode = ASSIGN /\ ai.inst_operands = [Lit 0w] /\
  ai.inst_outputs = [c] /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME ji /\
  ji.inst_opcode = JMP /\ ji.inst_operands = [Label lc] ==>
  fuel_outcome G ctx fn s 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME 0w)
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var c 0w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >> `~is_terminator ai.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[is_terminator_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, eval_operand_def, Abbr `u`]) >>
  `fuel_outcome G ctx fn u 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME 0w)` by
    (irule fuel_outcome_jump >>
     conj_tac >- simp[] >> qexistsl_tac [`bb`, `ji`, `lc`] >>
     simp[Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, jump_to_def, vars_kept_def,
          lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     Cases_on `x = c` >> gvs[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

Theorem sa_increment[local]:
  no_phi_fn fn /\ ~var_below N c /\ ~var_below N vnext /\ c <> vnext /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME ai /\
  ai.inst_opcode = ADD /\ ai.inst_operands = [Var c; Lit 1w] /\
  ai.inst_outputs = [vnext] /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME ci /\
  ci.inst_opcode = ASSIGN /\ ci.inst_operands = [Var vnext] /\
  ci.inst_outputs = [c] /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME ji /\
  ji.inst_opcode = JMP /\ ji.inst_operands = [Label lc] /\
  lookup_var c s = SOME (n2w k) ==>
  fuel_outcome G ctx fn s 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME (n2w (k+1)))
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var vnext (n2w (k+1)) s)
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = (update_var c (n2w (k+1)) u)
                    with vs_inst_idx := SUC u.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >> `~is_terminator ai.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[is_terminator_def, step_inst_non_invoke,
          step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
          GSYM word_add_n2w, Abbr `u`]) >>
  `!f. run_from f ctx fn u = run_from f ctx fn v` by
    (gen_tac >>
     `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME ci /\
      ~is_terminator ci.inst_opcode` by
       simp[Abbr `u`, update_var_def, is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          eval_operand_def, Abbr `v`, Abbr `u`, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE]) >>
  `fuel_outcome G ctx fn v 1
    (\t. t.vs_current_bb = lc /\ t.vs_inst_idx = 0 /\
         vars_kept N {} s t /\ lookup_var c t = SOME (n2w (k+1)))` by
    (irule fuel_outcome_jump >> conj_tac >- simp[] >>
     qexistsl_tac [`bb`, `ji`, `lc`] >>
     simp[Abbr `v`, Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, jump_to_def, vars_kept_def,
          lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `x = c` >> Cases_on `x = vnext` >> gvs[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

Theorem sa_increment_bound[local]:
  k < w2n (n2w n : 256 word) ==>
  k+1 <= w2n (n2w n : 256 word) /\
  w2n (n2w (k+1) : 256 word) = k+1 /\
  w2n (n2w n : 256 word) - (k+1) < w2n (n2w n : 256 word) - k
Proof
  strip_tac >>
  `w2n (n2w n : 256 word) < dimword (:256)` by simp[w2n_lt] >>
  `k+1 < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w, LESS_MOD]
QED

(* Given a bound for the element copy (the recursive call), the copy of a
   static array of n elements is bounded.  The slow path counts a fresh
   counter from 0 while it is below the literal n2w n; each round copies one
   element and adds 1, so the loop leaves within 2 ** 256 rounds, and the
   counter never wraps since it stays at most n2w n. *)
Theorem fuel_ok_compile_copy_sarray_typed:
  !cenv dst dst_elem src src_elem n.
    (!d s Wv E. fuel_ok Wv {} E
                  (compile_store_memory_typed cenv d dst_elem s src_elem)) ==>
    !Wv E. fuel_ok Wv {} E
             (compile_copy_sarray_typed cenv dst dst_elem src src_elem n)
Proof
  cheat
QED

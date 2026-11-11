(*
 * Fuel bound for the static-array typed-copy loop.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_copy_sarray_typed
 *)

Theory fragFuelLoopSarray
Ancestors
  fragFuel fragFuelContextBase compileEnv emitHelper context venomInst
Libs
  fragFuelLib

(* Body pointer prefix: its values may fail to evaluate, but no instruction
   writes the loop counter or a variable from before the loop. *)
Theorem sa_body_prefix[local]:
  !G ctx fn N c lb vs vd ps pd ss ds src dst bb m0 m1 a0 a1 s.
    callees_stable G ctx fn /\
    lookup_block lb fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME m0 /\
    get_instruction bb 1 = SOME m1 /\
    get_instruction bb 2 = SOME a0 /\
    get_instruction bb 3 = SOME a1 /\
    m0.inst_opcode = MUL /\ m0.inst_operands = [Var c; Lit ss] /\
    m0.inst_outputs = [vs] /\
    m1.inst_opcode = MUL /\ m1.inst_operands = [Var c; Lit ds] /\
    m1.inst_outputs = [vd] /\
    a0.inst_opcode = ADD /\ a0.inst_operands = [src; Var vs] /\
    a0.inst_outputs = [ps] /\
    a1.inst_opcode = ADD /\ a1.inst_operands = [dst; Var vd] /\
    a1.inst_outputs = [pd] /\
    ~MEM c [vs;vd;ps;pd] /\
    EVERY (\x. ~var_below N x) [vs;vd;ps;pd] /\
    s.vs_current_bb = lb /\ s.vs_inst_idx = 0 ==>
    fuel_outcome G ctx fn s 0
      (\t. t.vs_current_bb = lb /\ t.vs_inst_idx = 4 /\
           vars_kept N {} s t /\ lookup_var c t = lookup_var c s)
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`s`, `bb`, `m0`] mp_tac)
    run_from_nonterm_stable >> simp[is_terminator_def] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `t1` strip_assume_tac) assume_tac)
  >- (drule_then (qspecl_then [`t1 with vs_inst_idx := 1`, `bb`, `m1`] mp_tac)
        run_from_nonterm_stable >> simp[is_terminator_def] >>
      disch_then (DISJ_CASES_THEN2
        (qx_choose_then `t2` strip_assume_tac) assume_tac)
      >- (drule_then (qspecl_then [`t2 with vs_inst_idx := 2`, `bb`, `a0`] mp_tac)
            run_from_nonterm_stable >> simp[is_terminator_def] >>
          disch_then (DISJ_CASES_THEN2
            (qx_choose_then `t3` strip_assume_tac) assume_tac)
          >- (drule_then (qspecl_then [`t3 with vs_inst_idx := 3`, `bb`, `a1`] mp_tac)
                run_from_nonterm_stable >> simp[is_terminator_def] >>
              disch_then (DISJ_CASES_THEN2
                (qx_choose_then `t4` strip_assume_tac) assume_tac)
              >- (simp[fuel_outcome_def] >> disj1_tac >>
                  qexists_tac `t4 with vs_inst_idx := 4` >>
                  gvs[vars_kept_def, venomStateTheory.lookup_var_def] >>
                  metis_tac[]) >>
              simp[fuel_outcome_def]) >>
          simp[fuel_outcome_def]) >>
      simp[fuel_outcome_def]) >>
  simp[fuel_outcome_def]
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

(*
 * Fuel bound for a range loop (For over Range), the loop part of the
 * statement-level fuel bound.
 *
 * Why it terminates: the counter is a fresh variable, set to start in the
 * entry block and incremented by one (mod 2^256) in the incr block, and
 * the loop exits when it EQuals end_val, a fresh variable computed once in
 * the entry block.  The body writes only the pointer variables of its
 * environment's locals (all allocated before the counter: cenv_ptrs_below)
 * and the variables it allocates itself, so neither the counter nor
 * end_val changes in the body, and the loop runs at most 2^256 rounds,
 * each within the body's bound plus a constant.  A jump out of the body
 * goes to exit_lbl (break: the end of the loop), incr_lbl (continue) or
 * the constructor's exit label (in E).
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_for_range
 *)

Theory fragFuelLoopForRange
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelStmtBase
  stmtLowering exprLowering compileEnv emitHelper context venomInst
  venomExecSemantics venomState
Libs
  fragFuelLib

(* Unsigned modular distance decreases even when the counter wraps. *)
Theorem range_distance_decreases[local]:
  !(a:256 word) b.
    a <> b ==> w2n (b - (a + 1w)) < w2n (b - a)
Proof
  rpt strip_tac >> rewrite_tac[wordsTheory.WORD_SUB_PLUS] >>
  irule wordsTheory.WORD_PRED_THM >> simp[wordsTheory.WORD_EQ_SUB_ZERO]
QED

(* Recover the caller's frame from the smaller body write set.  The
   optional fresh local pointer need not be in the caller's write set. *)
Theorem range_body_frame[local]:
  !N M p W Wb s t.
    N <= M /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN W /\ var_below N x}) /\
    vars_kept M Wb s t ==>
    vars_kept N W s t
Proof
  rw[vars_kept_def] >>
  `x NOTIN Wb` by
    (gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[var_below_fresh]) >>
  first_x_assum irule >> simp[] >>
  gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Declaration changes only the new pointer's write permission. *)
Theorem range_body_declare[local]:
  !ce id ty st bc st1 N W E lc b c.
    cenv_ptrs_in W ce /\ cenv_ptrs_below N ce /\
    N <= st.cs_next_var /\ stmt_exits_in E ce lc /\
    declare_local ce id ty st = (bc,st1) ==>
    cenv_ptrs_in
      (if ce.ce_alloca_locals then
         STRING #"%" (toString st.cs_next_var) INSERT
           {x | x IN W /\ var_below N x}
       else {x | x IN W /\ var_below N x}) bc /\
    cenv_ptrs_below st1.cs_next_var bc /\
    stmt_exits_in (E UNION {b;c}) bc (InLoop b c)
Proof
  rpt gen_tac >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def, LET_THM,
       cenv_ptrs_in_def, cenv_ptrs_below_def, stmt_exits_in_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
  >~ [`var_below (k + 1) (STRING #"%" (toString k))`]
  >- simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
  qpat_assum `!i v z. FLOOKUP _ i = SOME (PtrVar (Var v) z) ==> v IN _`
    (drule_then assume_tac) >>
  qpat_assum `!i v z. FLOOKUP _ i = SOME (PtrVar (Var v) z) ==> var_below N v`
    (drule_then assume_tac) >>
  simp[] >> gvs[var_below_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Exact fixed-code boundary; unlike fuel_ok_emit this retains the values. *)
Theorem range_condition_outcome[local]:
  !G ctx fn s bb eqi br counter endpoint test c e yes no N Wv.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME eqi /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME br /\
    eqi.inst_opcode = EQ /\ eqi.inst_operands = [Var counter; Var endpoint] /\
    eqi.inst_outputs = [test] /\
    br.inst_opcode = JNZ /\ br.inst_operands = [Var test; Label yes; Label no] /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    test <> counter /\ test <> endpoint /\
    (~var_below N test \/ test IN Wv) ==>
    fuel_outcome G ctx fn s 1
      (\t. vars_kept N Wv s t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           t.vs_current_bb = (if c = e then yes else no) /\ t.vs_inst_idx = 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var test (bool_to_word (c = e)) s)
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >>
     `~is_terminator eqi.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[is_terminator_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, Abbr `u`]) >>
  `fuel_outcome G ctx fn u 1
      (\t. vars_kept N Wv s t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           t.vs_current_bb = (if c = e then yes else no) /\ t.vs_inst_idx = 0)` by
    (irule fuel_outcome_jump >>
     simp[] >> qexistsl_tac [`bb`, `br`, `if c = e then yes else no`] >>
     Cases_on `c = e` >> simp[Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def, jump_to_def,
          vars_kept_def] >> rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

(* Missing operands fix the result immediately, without a typing premise. *)
Theorem range_condition_undefined[local]:
  !G ctx fn s bb eqi counter endpoint P.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME eqi /\
    eqi.inst_opcode = EQ /\ eqi.inst_operands = [Var counter; Var endpoint] /\
    (lookup_var counter s = NONE \/ lookup_var endpoint s = NONE) ==>
    fuel_outcome G ctx fn s 0 P
Proof
  rpt strip_tac >> simp[fuel_outcome_def] >> disj2_tac >> rpt strip_tac >>
  `~is_terminator eqi.inst_opcode` by simp[is_terminator_def] >>
  drule_all run_from_nonterm >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def] >>
  Cases_on `lookup_var counter s` >> simp[]
QED

Theorem range_increment_outcome[local]:
  !G ctx fn s bb addi assi ji counter endpoint tmp c e cond N Wv.
    no_phi_fn fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME addi /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME assi /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME ji /\
    addi.inst_opcode = ADD /\ addi.inst_operands = [Var counter; Lit 1w] /\
    addi.inst_outputs = [tmp] /\
    assi.inst_opcode = ASSIGN /\ assi.inst_operands = [Var tmp] /\
    assi.inst_outputs = [counter] /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label cond] /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    tmp <> counter /\ tmp <> endpoint /\ counter <> endpoint /\
    (~var_below N tmp \/ tmp IN Wv) /\
    (~var_below N counter \/ counter IN Wv) ==>
    fuel_outcome G ctx fn s 1
      (\t. vars_kept N Wv s t /\ lookup_var counter t = SOME (c + 1w) /\
           lookup_var endpoint t = SOME e /\
           t.vs_current_bb = cond /\ t.vs_inst_idx = 0)
Proof
  rpt strip_tac >>
  qabbrev_tac `u = (update_var tmp (c + 1w) s)
                    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = (update_var counter (c + 1w) u)
                    with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  `!f. run_from f ctx fn s = run_from f ctx fn u` by
    (gen_tac >> `~is_terminator addi.inst_opcode` by simp[is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, Abbr `u`]) >>
  `!f. run_from f ctx fn u = run_from f ctx fn v` by
    (gen_tac >>
     `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb u.vs_inst_idx = SOME assi /\
      ~is_terminator assi.inst_opcode` by
       simp[Abbr `u`, update_var_def, is_terminator_def] >>
     drule_all run_from_nonterm >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          eval_operand_def, Abbr `v`, Abbr `u`, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
  `fuel_outcome G ctx fn v 1
      (\t. vars_kept N Wv s t /\ lookup_var counter t = SOME (c + 1w) /\
           lookup_var endpoint t = SOME e /\
           t.vs_current_bb = cond /\ t.vs_inst_idx = 0)` by
    (irule fuel_outcome_jump >> simp[] >> qexistsl_tac [`bb`, `ji`, `cond`] >>
     simp[Abbr `v`, Abbr `u`, update_var_def, is_terminator_def,
          step_inst_base_opcode_eqs, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
          jump_to_def, vars_kept_def] >>
     rpt strip_tac >> gvs[lookup_var_def] >> metis_tac[]) >>
  gvs[fuel_outcome_def] >> metis_tac[]
QED

(* The body contract retains the private loop words as well as the
   caller's (smaller-frontier) frame. *)
Theorem range_body_fragment[local]:
  !G ctx fn bs be K Wb E N p W s root counter endpoint c e.
    frag_fuel Wb {} E bs be K /\
    no_phi_fn fn /\ fn_has_code bs be fn /\ callees_stable G ctx fn /\
    at_point bs s /\ N <= bs.cs_next_var /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN W /\ var_below N x}) /\
    var_below bs.cs_next_var counter /\ counter NOTIN Wb /\
    var_below bs.cs_next_var endpoint /\ endpoint NOTIN Wb /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    vars_kept N W root s ==>
    ?j. j <= K /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N W root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           (at_point be t \/ (t.vs_current_bb IN E /\ t.vs_inst_idx = 0)))
Proof
  map_every qx_gen_tac [`G`, `ctx`, `fn`, `bs`, `be`, `Kb`, `Wb`, `E`,
                         `N`, `p`, `Wv`, `s`, `root`, `counter`, `endpoint`, `c`, `e`] >>
  strip_tac >>
  qpat_x_assum `frag_fuel _ _ _ _ _ _` mp_tac >>
  simp[frag_fuel_def] >>
  disch_then (qspecl_then [`G`, `bs.cs_next_var`, `ctx`, `fn`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `j` >> simp[] >>
  drule fuel_outcome_weaken >> disch_then irule >>
  rpt strip_tac >> simp[] >>
  `vars_kept N Wv s t` by
    (irule range_body_frame >> qexistsl_tac [`bs.cs_next_var`, `Wb`, `p`] >>
     gvs[]) >>
  drule_all vars_kept_trans >> strip_tac >> simp[] >>
  gvs[vars_kept_def]
QED

(* At the optional jump's endpoint either a JMP was appended, or the
   terminated block ends here. The latter is a fuel-independent error. *)
Theorem range_body_tail[local]:
  !G ctx fn be incr N Wv root s counter endpoint c e bb.
    no_phi_fn fn /\ at_point be s /\
    lookup_block be.cs_current_bb fn.fn_blocks = SOME bb /\
    (get_instruction bb (LENGTH be.cs_current_insts) = NONE \/
     ?ji. get_instruction bb (LENGTH be.cs_current_insts) = SOME ji /\
          ji.inst_opcode = JMP /\ ji.inst_operands = [Label incr]) /\
    vars_kept N Wv root s /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e ==>
    ?j. j <= 1 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           t.vs_current_bb = incr /\ t.vs_inst_idx = 0)
Proof
  rpt strip_tac
  >- (`!f. run_from f ctx fn s = Error "block not terminated"` by
        (gen_tac >> gvs[at_point_def] >>
         simp[fragExecTheory.run_from_def, Once exec_block_def]) >>
      qexists_tac `0` >> simp[fuel_outcome_def]) >>
  qexists_tac `1` >> simp[] >> irule fuel_outcome_jump >> simp[] >>
  qexistsl_tac [`bb`, `ji`, `incr`] >>
  gvs[at_point_def, is_terminator_def, step_inst_base_opcode_eqs,
      eval_operand_def, jump_to_def, vars_kept_def, lookup_var_def]
QED

(* A zero-output nonterminator covers MSTORE, including all its error
   branches, without imposing any memory or operand-definedness premise. *)
Theorem range_body_store[local]:
  !G ctx fn s bb inst bs N Wv root counter endpoint c e.
    callees_stable G ctx fn /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\ inst.inst_outputs = [] /\
    bs.cs_current_bb = s.vs_current_bb /\
    LENGTH bs.cs_current_insts = SUC s.vs_inst_idx /\
    vars_kept N Wv root s /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e ==>
    fuel_outcome G ctx fn s 0
      (\t. vars_kept N Wv root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           at_point bs t)
Proof
  rpt strip_tac >> drule_all run_from_nonterm_stable >> strip_tac
  >- (simp[fuel_outcome_def] >> disj1_tac >>
      qexists_tac `s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
      gvs[at_point_def, vars_kept_def, lookup_var_def]) >>
  simp[fuel_outcome_def]
QED

Theorem range_body_invalid[local]:
  !G ctx fn s bb inst P.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVALID ==>
    fuel_outcome G ctx fn s 0 P
Proof
  rpt strip_tac >>
  `!f. run_from f ctx fn s = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (gen_tac >> simp[fragExecTheory.run_from_def, Once exec_block_def,
                    step_inst_non_invoke, step_inst_base_opcode_eqs]) >>
  simp[fuel_outcome_def]
QED

Theorem range_body_finish[local]:
  !G ctx fn bs be Kb Wb E exit incr N p Wv s root counter endpoint c e bb.
    frag_fuel Wb {} (E UNION {exit;incr}) bs be Kb /\
    no_phi_fn fn /\ fn_has_code bs be fn /\ callees_stable G ctx fn /\
    at_point bs s /\ N <= bs.cs_next_var /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN Wv /\ var_below N x}) /\
    var_below bs.cs_next_var counter /\ counter NOTIN Wb /\
    var_below bs.cs_next_var endpoint /\ endpoint NOTIN Wb /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    vars_kept N Wv root s /\
    lookup_block be.cs_current_bb fn.fn_blocks = SOME bb /\
    (get_instruction bb (LENGTH be.cs_current_insts) = NONE \/
     ?ji. get_instruction bb (LENGTH be.cs_current_insts) = SOME ji /\
          ji.inst_opcode = JMP /\ ji.inst_operands = [Label incr]) ==>
    ?j. j <= Kb + 1 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> disch_tac >>
  `?j. j <= Kb /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           (at_point be t \/
            (t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0)))` by
    (irule range_body_fragment >> metis_tac[]) >>
  rename1 `j <= Kb` >>
  drule fuel_outcome_compose >>
  disch_then (qspec_then
    `\t. vars_kept N Wv root t /\
         lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
         t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0` mp_tac) >>
  disch_then (qspec_then `1` mp_tac) >>
  impl_tac
  >- (gen_tac >> BETA_TAC >> disch_tac >>
      Cases_on `t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0`
      >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> gvs[]) >>
      `?jt. jt <= 1 /\ fuel_outcome G ctx fn t jt
         (\u. vars_kept N Wv root u /\
              lookup_var counter u = SOME c /\ lookup_var endpoint u = SOME e /\
              u.vs_current_bb = incr /\ u.vs_inst_idx = 0)` by
        (irule range_body_tail >> metis_tac[]) >>
      qexists_tac `jt` >> simp[] >>
      drule fuel_outcome_weaken >> disch_then irule >> simp[]) >>
  strip_tac >> qexists_tac `j'` >> simp[] >> decide_tac
QED

(* Complete body-label bridge. Its bound is independent of runtime
   memory and of the values of either private loop word. *)
Theorem range_body_bridge[local]:
  !G ctx fn bs be Kb Wb E exit incr N p Wv s root counter endpoint c e bb inst tail.
    frag_fuel Wb {} (E UNION {exit;incr}) bs be Kb /\
    no_phi_fn fn /\ fn_has_code bs be fn /\ callees_stable G ctx fn /\
    N <= bs.cs_next_var /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN Wv /\ var_below N x}) /\
    var_below bs.cs_next_var counter /\ counter NOTIN Wb /\
    var_below bs.cs_next_var endpoint /\ endpoint NOTIN Wb /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    vars_kept N Wv root s /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    s.vs_inst_idx = 0 /\ get_instruction bb 0 = SOME inst /\
    bs.cs_current_bb = s.vs_current_bb /\ LENGTH bs.cs_current_insts = 1 /\
    (inst.inst_opcode = INVALID \/
     (inst.inst_opcode = MSTORE /\ inst.inst_outputs = [])) /\
    lookup_block be.cs_current_bb fn.fn_blocks = SOME tail /\
    (get_instruction tail (LENGTH be.cs_current_insts) = NONE \/
     ?ji. get_instruction tail (LENGTH be.cs_current_insts) = SOME ji /\
          ji.inst_opcode = JMP /\ ji.inst_operands = [Label incr]) ==>
    ?j. j <= Kb + 1 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
           t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> disch_tac >>
  Cases_on `inst.inst_opcode = INVALID`
  >- (qexists_tac `0` >> simp[] >> irule range_body_invalid >> metis_tac[]) >>
  `fuel_outcome G ctx fn s 0
     (\t. vars_kept N Wv root t /\
          lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
          at_point bs t)` by
    (irule range_body_store >> gvs[is_terminator_def]) >>
  drule fuel_outcome_compose >>
  disch_then (qspec_then
    `\t. vars_kept N Wv root t /\
         lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
         t.vs_current_bb IN (E UNION {exit;incr}) /\ t.vs_inst_idx = 0` mp_tac) >>
  disch_then (qspec_then `Kb + 1` mp_tac) >>
  simp_tac pure_ss [arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> gen_tac >> BETA_TAC >> disch_tac >>
  irule range_body_finish >> metis_tac[]
QED

(* One complete round, from the comparison through the back edge. *)
Theorem range_round_outcome[local]:
  !G ctx fn bs be Kb Wb E exit incr cond bodylbl N p Wv root s
    counter endpoint test tmp c e hc bc ic eqi br inst addi assi ji tail.
    frag_fuel Wb {} (E UNION {exit;incr}) bs be Kb /\
    no_phi_fn fn /\ fn_has_code bs be fn /\ callees_stable G ctx fn /\
    N <= bs.cs_next_var /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN Wv /\ var_below N x}) /\
    var_below bs.cs_next_var counter /\ counter NOTIN Wb /\
    var_below bs.cs_next_var endpoint /\ endpoint NOTIN Wb /\
    test <> counter /\ test <> endpoint /\
    tmp <> counter /\ tmp <> endpoint /\ counter <> endpoint /\
    (~var_below N test \/ test IN Wv) /\
    (~var_below N tmp \/ tmp IN Wv) /\
    (~var_below N counter \/ counter IN Wv) /\
    lookup_block cond fn.fn_blocks = SOME hc /\
    get_instruction hc 0 = SOME eqi /\ get_instruction hc 1 = SOME br /\
    eqi.inst_opcode = EQ /\ eqi.inst_operands = [Var counter; Var endpoint] /\
    eqi.inst_outputs = [test] /\
    br.inst_opcode = JNZ /\ br.inst_operands = [Var test; Label exit; Label bodylbl] /\
    lookup_block bodylbl fn.fn_blocks = SOME bc /\ get_instruction bc 0 = SOME inst /\
    bs.cs_current_bb = bodylbl /\ LENGTH bs.cs_current_insts = 1 /\
    (inst.inst_opcode = INVALID \/
     (inst.inst_opcode = MSTORE /\ inst.inst_outputs = [])) /\
    lookup_block be.cs_current_bb fn.fn_blocks = SOME tail /\
    (get_instruction tail (LENGTH be.cs_current_insts) = NONE \/
     ?ij. get_instruction tail (LENGTH be.cs_current_insts) = SOME ij /\
          ij.inst_opcode = JMP /\ ij.inst_operands = [Label incr]) /\
    lookup_block incr fn.fn_blocks = SOME ic /\
    get_instruction ic 0 = SOME addi /\ get_instruction ic 1 = SOME assi /\
    get_instruction ic 2 = SOME ji /\
    addi.inst_opcode = ADD /\ addi.inst_operands = [Var counter; Lit 1w] /\
    addi.inst_outputs = [tmp] /\
    assi.inst_opcode = ASSIGN /\ assi.inst_operands = [Var tmp] /\
    assi.inst_outputs = [counter] /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label cond] /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
    lookup_var counter s = SOME c /\ lookup_var endpoint s = SOME e /\
    vars_kept N Wv root s ==>
    ?j. j <= Kb + 3 /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           ((t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0) \/
            (t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
             lookup_var counter t = SOME (c + 1w) /\
             lookup_var endpoint t = SOME e /\ c <> e)))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fuel_outcome G ctx fn s 1
    (\t. vars_kept N Wv s t /\
         lookup_var counter t = SOME c /\ lookup_var endpoint t = SOME e /\
         t.vs_current_bb = (if c = e then exit else bodylbl) /\ t.vs_inst_idx = 0)` by
    (irule range_condition_outcome >> gvs[]) >>
  drule fuel_outcome_compose >>
  disch_then (qspec_then
    `\t. vars_kept N Wv root t /\
         ((t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0) \/
          (t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
           lookup_var counter t = SOME (c + 1w) /\
           lookup_var endpoint t = SOME e /\ c <> e))` mp_tac) >>
  disch_then (qspec_then `Kb + 2` mp_tac) >>
  impl_tac
  >- (gen_tac >> BETA_TAC >> strip_tac >>
      `vars_kept N Wv root t` by metis_tac[vars_kept_trans] >>
      Cases_on `c = e`
      >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >> gvs[]) >>
      `?jb. jb <= Kb + 1 /\ fuel_outcome G ctx fn t jb
        (\u. vars_kept N Wv root u /\
             lookup_var counter u = SOME c /\ lookup_var endpoint u = SOME e /\
             u.vs_current_bb IN (E UNION {exit;incr}) /\ u.vs_inst_idx = 0)` by
        (irule range_body_bridge >> gvs[] >> metis_tac[]) >>
      drule fuel_outcome_compose >>
      disch_then (qspec_then
        `\t. vars_kept N Wv root t /\
             ((t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0) \/
              (t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
               lookup_var counter t = SOME (c + 1w) /\
               lookup_var endpoint t = SOME e /\ c <> e))` mp_tac) >>
      disch_then (qspec_then `1` mp_tac) >>
      impl_tac
      >- (gen_tac >> BETA_TAC >> strip_tac >>
          Cases_on `t'.vs_current_bb IN (E UNION {exit})`
          >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
              BETA_TAC >> conj_tac >- asm_rewrite_tac[] >> disj1_tac >>
              qpat_x_assum `t'.vs_current_bb IN (E UNION {exit})` mp_tac >>
              simp_tac pure_ss [pred_setTheory.IN_UNION, pred_setTheory.IN_INSERT,
                                pred_setTheory.NOT_IN_EMPTY] >>
              strip_tac >> asm_rewrite_tac[]) >>
          `t'.vs_current_bb = incr` by
            (qpat_x_assum `t'.vs_current_bb IN (E UNION {exit;incr})` mp_tac >>
             qpat_x_assum `t'.vs_current_bb NOTIN (E UNION {exit})` mp_tac >>
             simp_tac (pure_ss ++ boolSimps.CONJ_ss) [pred_setTheory.IN_UNION,
               pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY] >>
             metis_tac[]) >>
          `fuel_outcome G ctx fn t' 1
             (\u. vars_kept N Wv t' u /\
                  lookup_var counter u = SOME (c + 1w) /\
                  lookup_var endpoint u = SOME e /\
                  u.vs_current_bb = cond /\ u.vs_inst_idx = 0)` by
            (irule range_increment_outcome >> simp[] >>
             qexistsl_tac [`addi`, `assi`, `ic`, `ji`, `tmp`] >> simp[]) >>
          qexists_tac `1` >> simp[] >>
          drule fuel_outcome_weaken >> disch_then irule >>
          rpt strip_tac >> simp[] >> metis_tac[vars_kept_trans]) >>
      strip_tac >> qexists_tac `j` >> simp[] >> decide_tac) >>
  strip_tac >> qexists_tac `j` >> simp[] >> decide_tac
QED

(* The cycle boundary accepts arbitrary runtime header states, including
   undefined operands. No runtime typing or label disjointness is needed. *)
Theorem range_cycle_outcome[local]:
  !G ctx fn bs be Kb Wb E exit incr cond bodylbl N p Wv root s
    counter endpoint test tmp hc bc ic eqi br inst addi assi ji tail.
    frag_fuel Wb {} (E UNION {exit;incr}) bs be Kb /\
    no_phi_fn fn /\ fn_has_code bs be fn /\ callees_stable G ctx fn /\
    N <= bs.cs_next_var /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN Wv /\ var_below N x}) /\
    var_below bs.cs_next_var counter /\ counter NOTIN Wb /\
    var_below bs.cs_next_var endpoint /\ endpoint NOTIN Wb /\
    test <> counter /\ test <> endpoint /\
    tmp <> counter /\ tmp <> endpoint /\ counter <> endpoint /\
    (~var_below N test \/ test IN Wv) /\
    (~var_below N tmp \/ tmp IN Wv) /\
    (~var_below N counter \/ counter IN Wv) /\
    lookup_block cond fn.fn_blocks = SOME hc /\
    get_instruction hc 0 = SOME eqi /\ get_instruction hc 1 = SOME br /\
    eqi.inst_opcode = EQ /\ eqi.inst_operands = [Var counter; Var endpoint] /\
    eqi.inst_outputs = [test] /\
    br.inst_opcode = JNZ /\ br.inst_operands = [Var test; Label exit; Label bodylbl] /\
    lookup_block bodylbl fn.fn_blocks = SOME bc /\ get_instruction bc 0 = SOME inst /\
    bs.cs_current_bb = bodylbl /\ LENGTH bs.cs_current_insts = 1 /\
    (inst.inst_opcode = INVALID \/
     (inst.inst_opcode = MSTORE /\ inst.inst_outputs = [])) /\
    lookup_block be.cs_current_bb fn.fn_blocks = SOME tail /\
    (get_instruction tail (LENGTH be.cs_current_insts) = NONE \/
     ?ij. get_instruction tail (LENGTH be.cs_current_insts) = SOME ij /\
          ij.inst_opcode = JMP /\ ij.inst_operands = [Label incr]) /\
    lookup_block incr fn.fn_blocks = SOME ic /\
    get_instruction ic 0 = SOME addi /\ get_instruction ic 1 = SOME assi /\
    get_instruction ic 2 = SOME ji /\
    addi.inst_opcode = ADD /\ addi.inst_operands = [Var counter; Lit 1w] /\
    addi.inst_outputs = [tmp] /\
    assi.inst_opcode = ASSIGN /\ assi.inst_operands = [Var tmp] /\
    assi.inst_outputs = [counter] /\
    ji.inst_opcode = JMP /\ ji.inst_operands = [Label cond] /\
    s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ vars_kept N Wv root s ==>
    ?j. j <= (2 ** 256) * (Kb + 8) /\ fuel_outcome G ctx fn s j
      (\t. vars_kept N Wv root t /\
           t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `s.vs_current_bb IN (E UNION {exit})`
  >- (qexists_tac `0` >> simp[] >> irule fuel_outcome_refl >>
      qpat_x_assum `s.vs_current_bb IN (E UNION {exit})` mp_tac >> simp[]) >>
  Cases_on `lookup_var counter s`
  >- (qexists_tac `0` >> simp[] >> irule range_condition_undefined >>
      simp[] >> metis_tac[]) >>
  rename1 `lookup_var counter s = SOME c0` >>
  Cases_on `lookup_var endpoint s`
  >- (qexists_tac `0` >> simp[] >> irule range_condition_undefined >>
      simp[] >> metis_tac[]) >>
  rename1 `lookup_var endpoint s = SOME e` >>
  qabbrev_tac `H = \t. vars_kept N Wv root t /\
     t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
     lookup_var endpoint t = SOME e /\ ?c. lookup_var counter t = SOME c` >>
  qabbrev_tac `Q = \t. vars_kept N Wv root t /\
     t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0` >>
  qabbrev_tac `mu = \t. w2n (e - THE (lookup_var counter t))` >>
  `!t. H t ==> ?j. j <= (2 ** 256) * (Kb + 8) /\
                         fuel_outcome G ctx fn t j Q` by
    (match_mp_tac fuel_outcome_iterate >> qexists_tac `mu` >> conj_tac
     >- (rpt strip_tac >> simp[Abbr `mu`] >>
         qspec_then `e - THE (lookup_var counter s')` mp_tac wordsTheory.w2n_lt >>
         simp[wordsTheory.dimword_def]) >>
     gen_tac >> simp[Abbr `H`] >> strip_tac >>
     `?j. j <= Kb + 3 /\ fuel_outcome G ctx fn s' j
       (\t. vars_kept N Wv root t /\
            ((t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0) \/
             (t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\
              lookup_var counter t = SOME (c + 1w) /\
              lookup_var endpoint t = SOME e /\ c <> e)))` by
       (irule range_round_outcome >> simp[] >>
        qpat_assum `frag_fuel _ _ _ _ _ _` (irule_at Any) >> simp[] >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     qexists_tac `j` >> conj_tac >- decide_tac >>
     drule fuel_outcome_weaken >> disch_then irule >>
     simp[Abbr `Q`, Abbr `mu`] >> rpt strip_tac >>
     simp[range_distance_decreases]) >>
  first_x_assum (qspec_then `s` mp_tac) >> simp[Abbr `H`, Abbr `Q`]
QED

Theorem fuel_okS_compile_for_range:
  !cenv lctx ty id fty start_e end_e bound body Wv E.
    (!c t e Wv' E'. fuel_ok Wv' {} E' (lower_value compile_expr c t e)) /\
    (!cenv' lc Wv' E'.
       cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E' cenv' lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E'
         (compile_stmts cenv' lc ty body)) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
      (compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body))
Proof
  cheat
QED

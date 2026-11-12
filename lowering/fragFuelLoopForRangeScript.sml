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

Theorem range_compiled_tail[local]:
  !n W Wb E counter endpoint cond bodylbl incr exit op ops (B:unit compiler).
    Wb SUBSET {x | x IN W /\ var_below n x} /\
    counter NOTIN Wb /\ endpoint NOTIN Wb /\ counter <> endpoint /\
    counter IN W /\ (op = MSTORE \/ op = INVALID) /\
    fuel_okS (\st. n <= st.cs_next_var) Wb {} (E UNION {exit;incr}) B ==>
    fuel_okS (\st. n <= st.cs_next_var /\
                   var_below st.cs_next_var counter /\
                   var_below st.cs_next_var endpoint) W {} E
      (do emit_inst JMP [Label cond] [];
          new_block cond;
          test <- emit_op EQ [Var counter; Var endpoint];
          emit_inst JNZ [test; Label exit; Label bodylbl] [];
          new_block bodylbl;
          emit_void op ops;
          B;
          emit_jmp_if_not_terminated incr;
          new_block incr;
          tmp <- emit_op ADD [Var counter; Lit 1w];
          emit_inst ASSIGN [tmp] [counter];
          emit_inst JMP [Label cond] [];
          new_block exit;
          return () od)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp_tac std_ss [fuel_okS_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ st = _` mp_tac >>
  simp_tac (srw_ss()) [comp_bind_def, comp_ignore_bind_def,
    emit_inst_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
    emit_def, new_block_def, comp_return_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `B bs` >>
  Cases_on `B bs` >> rename1 `B bs = (u,be)` >> Cases_on `u` >>
  `n <= bs.cs_next_var` by simp[Abbr `bs`] >>
  `cs_extends bs be /\ bs.cs_next_var <= be.cs_next_var /\
   (cs_no_phi bs ==> cs_no_phi be) /\
   ?Kb. frag_fuel Wb {} (E UNION {exit;incr}) bs be Kb` by
    (qpat_x_assum `fuel_okS _ _ _ _ B` mp_tac >>
     simp_tac std_ss [fuel_okS_def] >> disch_then drule >> simp[]) >>
  Cases_on `emit_jmp_if_not_terminated incr be` >>
  rename1 `emit_jmp_if_not_terminated incr be = (u,ae)` >>
  simp_tac (srw_ss()) [] >> strip_tac >> gnvs[] >>
  `cs_extends st bs` by
    (rewrite_tac[cs_extends_def] >> qexists_tac `TAKE 2 bs.cs_blocks` >>
     simp[Abbr `bs`]) >>
  qmatch_goalsub_abbrev_tac `cs_extends st sf` >>
  `cs_extends ae sf` by
    (rewrite_tac[cs_extends_def] >> qexists_tac `TAKE 2 sf.cs_blocks` >>
     simp[Abbr `sf`]) >>
  `cs_extends be ae /\ ae.cs_next_var = be.cs_next_var /\
   (cs_no_phi be ==> cs_no_phi ae)` by
    (qpat_x_assum `emit_jmp_if_not_terminated _ _ = _` mp_tac >>
     simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def,
          LET_THM] >> Cases_on `block_is_terminated be` >>
     simp[emit_inst_def, comp_return_def, comp_bind_def, fresh_id_def,
          emit_def, LET_THM] >> strip_tac >> gvs[cs_extends_def,
          cs_no_phi_def, mk_inst_def] >> qexists_tac `[]` >> simp[]) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  conj_tac >- (gvs[Abbr `bs`] >> decide_tac) >>
  conj_tac
  >- (strip_tac >>
      `cs_no_phi bs` by
        (qpat_x_assum `cs_no_phi st` mp_tac >>
         simp[Abbr `bs`, cs_no_phi_def, mk_inst_def] >> gvs[]) >>
      `cs_no_phi ae` by metis_tac[] >>
      gvs[Abbr `sf`, cs_no_phi_def, mk_inst_def]) >>
  qexists_tac `1 + (2 ** 256) * (Kb + 8)` >>
  simp_tac std_ss [frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  fs[] >>
  `cs_extends st be /\ cs_extends be sf /\ cs_extends bs sf` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code st bs fn /\ fn_has_code bs be fn /\
   fn_has_code bs sf fn /\ fn_has_code ae sf fn` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `!bb. MEM bb (TAKE 2 bs.cs_blocks) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (qpat_x_assum `fn_has_code st bs fn` mp_tac >>
     simp[fragExecTheory.fn_has_code_def,
          fragExecTheory.emitted_blocks_def, Abbr `bs`] >> metis_tac[]) >>
  `!bb. MEM bb (TAKE 2 sf.cs_blocks) ==>
        lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (qpat_x_assum `fn_has_code ae sf fn` mp_tac >>
     simp[fragExecTheory.fn_has_code_def,
          fragExecTheory.emitted_blocks_def, Abbr `sf`] >> metis_tac[]) >>
  `?bc. lookup_block bodylbl fn.fn_blocks = SOME bc /\
        isPREFIX bs.cs_current_insts bc.bb_instructions` by
    (drule_all fragExecTheory.fn_has_code_start >> simp[Abbr `bs`]) >>
  `lookup_block ae.cs_current_bb fn.fn_blocks =
     SOME <|bb_label := ae.cs_current_bb;
            bb_instructions := ae.cs_current_insts|>` by
    (qpat_x_assum `!bb. MEM bb (TAKE 2 sf.cs_blocks) ==> _`
       (qspec_then `<|bb_label := ae.cs_current_bb;
                     bb_instructions := ae.cs_current_insts|>` mp_tac) >>
     simp[Abbr `sf`]) >>
  `ae.cs_current_bb = be.cs_current_bb /\
   (get_instruction <|bb_label := ae.cs_current_bb;
                      bb_instructions := ae.cs_current_insts|>
        (LENGTH be.cs_current_insts) = NONE \/
    ?ij. get_instruction <|bb_label := ae.cs_current_bb;
                           bb_instructions := ae.cs_current_insts|>
        (LENGTH be.cs_current_insts) = SOME ij /\
         ij.inst_opcode = JMP /\ ij.inst_operands = [Label incr])` by
    (qpat_x_assum `emit_jmp_if_not_terminated _ _ = _` mp_tac >>
     simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def, LET_THM] >>
     Cases_on `block_is_terminated be` >>
     simp[emit_inst_def, comp_return_def, comp_bind_def, fresh_id_def,
          emit_def, LET_THM] >> strip_tac >> simp[get_instruction_def] >>
     qpat_x_assum `_ with <|cs_next_id := _; cs_current_insts := _|> = ae`
       (SUBST1_TAC o SYM) >>
     simp[mk_inst_def, rich_listTheory.EL_APPEND2]) >>
  qabbrev_tac `hc = HD bs.cs_blocks` >>
  qabbrev_tac `ec = EL 1 bs.cs_blocks` >>
  qabbrev_tac `ic = HD sf.cs_blocks` >>
  `bs.cs_blocks = hc::ec::st.cs_blocks /\ hc.bb_label = cond /\
   ec.bb_label = st.cs_current_bb` by
    simp[Abbr `hc`, Abbr `ec`, Abbr `bs`] >>
  `sf.cs_blocks = ic ::
       <|bb_label := ae.cs_current_bb; bb_instructions := ae.cs_current_insts|> ::
       ae.cs_blocks /\ ic.bb_label = incr` by
    simp[Abbr `ic`, Abbr `sf`] >>
  `lookup_block cond fn.fn_blocks = SOME hc` by
    (qpat_x_assum `!bb. MEM bb (TAKE 2 bs.cs_blocks) ==> _`
       (qspec_then `hc` mp_tac) >> simp[]) >>
  `lookup_block incr fn.fn_blocks = SOME ic` by
    (qpat_x_assum `!bb. MEM bb (TAKE 2 sf.cs_blocks) ==> _`
       (qspec_then `ic` mp_tac) >> simp[]) >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME ec` by
    (qpat_x_assum `!bb. MEM bb (TAKE 2 bs.cs_blocks) ==> _`
       (qspec_then `ec` mp_tac) >> simp[]) >>
  `ec.bb_instructions = st.cs_current_insts ++
       [mk_inst st.cs_next_id JMP [Label cond] []]` by
    simp[Abbr `ec`, Abbr `bs`] >>
  `fuel_outcome G ctx fn s 1
     (\t. vars_kept st.cs_next_var W' s t /\
          t.vs_current_bb = cond /\ t.vs_inst_idx = 0)` by
    (irule fuel_outcome_jump >> conj_tac >- simp[] >>
     qexistsl_tac [`ec`, `mk_inst st.cs_next_id JMP [Label cond] []`, `cond`] >>
     simp[at_point_def, get_instruction_def,
          rich_listTheory.EL_APPEND2, mk_inst_def, is_terminator_def,
          step_inst_base_opcode_eqs, eval_operand_def, jump_to_def,
          vars_kept_def] >>
     qpat_x_assum `at_point st s` mp_tac >>
     simp[at_point_def, rich_listTheory.EL_APPEND2]) >>
  `hc.bb_instructions =
     [mk_inst (st.cs_next_id + 1) EQ [Var counter; Var endpoint]
        [STRING #"%" (toString st.cs_next_var)];
      mk_inst (st.cs_next_id + 2) JNZ
        [Var (STRING #"%" (toString st.cs_next_var)); Label exit; Label bodylbl] []]` by
    simp[Abbr `hc`, Abbr `bs`] >>
  `ic.bb_instructions =
     [mk_inst ae.cs_next_id ADD [Var counter; Lit 1w]
        [STRING #"%" (toString ae.cs_next_var)];
      mk_inst (ae.cs_next_id + 1) ASSIGN
        [Var (STRING #"%" (toString ae.cs_next_var))] [counter];
      mk_inst (ae.cs_next_id + 2) JMP [Label cond] []]` by
    simp[Abbr `ic`, Abbr `sf`] >>
  `bs.cs_next_var = st.cs_next_var + 1 /\
   bs.cs_current_bb = bodylbl /\
   bs.cs_current_insts = [mk_inst (st.cs_next_id + 3) op ops []]` by
    simp[Abbr `bs`] >>
  `sf.cs_current_bb = exit /\ sf.cs_current_insts = []` by
    simp[Abbr `sf`] >>
  `get_instruction hc 0 = SOME
       (mk_inst (st.cs_next_id + 1) EQ [Var counter; Var endpoint]
         [STRING #"%" (toString st.cs_next_var)]) /\
   get_instruction hc 1 = SOME
       (mk_inst (st.cs_next_id + 2) JNZ
         [Var (STRING #"%" (toString st.cs_next_var)); Label exit; Label bodylbl] []) /\
   get_instruction ic 0 = SOME
       (mk_inst ae.cs_next_id ADD [Var counter; Lit 1w]
         [STRING #"%" (toString ae.cs_next_var)]) /\
   get_instruction ic 1 = SOME
       (mk_inst (ae.cs_next_id + 1) ASSIGN
         [Var (STRING #"%" (toString ae.cs_next_var))] [counter]) /\
   get_instruction ic 2 = SOME
       (mk_inst (ae.cs_next_id + 2) JMP [Label cond] [])` by
    simp[get_instruction_def] >>
  `get_instruction bc 0 = SOME (mk_inst (st.cs_next_id + 3) op ops [])` by
    (qpat_x_assum `isPREFIX _ bc.bb_instructions` mp_tac >>
     simp[get_instruction_def, rich_listTheory.IS_PREFIX_APPEND] >>
     strip_tac >> simp[]) >>
  `st.cs_next_var <= ae.cs_next_var` by simp[] >>
  `STRING #"%" (toString st.cs_next_var) <> counter /\
   STRING #"%" (toString st.cs_next_var) <> endpoint /\
   STRING #"%" (toString ae.cs_next_var) <> counter /\
   STRING #"%" (toString ae.cs_next_var) <> endpoint` by
    (qpat_x_assum `var_below st.cs_next_var counter` mp_tac >>
     qpat_x_assum `var_below st.cs_next_var endpoint` mp_tac >>
     simp_tac std_ss [var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `~var_below st.cs_next_var (STRING #"%" (toString st.cs_next_var)) /\
   ~var_below st.cs_next_var (STRING #"%" (toString ae.cs_next_var))` by
    metis_tac[var_below_fresh, arithmeticTheory.LESS_EQ_REFL] >>
  `var_below bs.cs_next_var counter /\ var_below bs.cs_next_var endpoint` by
    gvs[var_below_def, arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_SUC_REFL] >>
  `Wb SUBSET (STRING #"%" (toString st.cs_next_var) INSERT
       {x | x IN W' /\ var_below st.cs_next_var x})` by
    (qpat_x_assum `Wb SUBSET _` mp_tac >>
     simp[pred_setTheory.SUBSET_DEF, var_below_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  (drule fuel_outcome_compose >>
  disch_then (qspec_then
    `\t. vars_kept st.cs_next_var W' s t /\
         t.vs_current_bb IN (E UNION {exit}) /\ t.vs_inst_idx = 0` mp_tac) >>
  disch_then (qspec_then `(2 ** 256) * (Kb + 8)` mp_tac) >>
  impl_tac
  >- (gen_tac >> BETA_TAC >> strip_tac >>
      irule (SPEC_ALL range_cycle_outcome |>
        Q.INST [`cond` |-> `cond`, `bodylbl` |-> `bodylbl`,
                `incr` |-> `incr`, `exit` |-> `exit`] |>
        Q.INST [`counter` |-> `counter`, `endpoint` |-> `endpoint`,
                `p` |-> `st.cs_next_var`]) >>
      qpat_assum `frag_fuel _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `lookup_block cond fn.fn_blocks = SOME hc` (irule_at Any) >>
      qpat_assum `lookup_block incr fn.fn_blocks = SOME ic` (irule_at Any) >>
      qpat_assum `lookup_block bodylbl fn.fn_blocks = SOME bc` (irule_at Any) >>
      `lookup_block be.cs_current_bb fn.fn_blocks =
         SOME <|bb_label := ae.cs_current_bb;
                bb_instructions := ae.cs_current_insts|>` by metis_tac[] >>
      qpat_assum `lookup_block be.cs_current_bb fn.fn_blocks = SOME _`
        (irule_at Any) >>
      qpat_assum `get_instruction hc 0 = SOME _` (irule_at Any) >>
      qpat_assum `get_instruction hc 1 = SOME _` (irule_at Any) >>
      qpat_assum `get_instruction ic 0 = SOME _` (irule_at Any) >>
      qpat_assum `get_instruction ic 1 = SOME _` (irule_at Any) >>
      qpat_assum `get_instruction ic 2 = SOME _` (irule_at Any) >>
      qpat_assum `get_instruction bc 0 = SOME _` (irule_at Any) >>
      simp[mk_inst_def] >> qexists_tac `st` >>
      fs[var_below_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `j` >> conj_tac >- gvs[] >>
  irule fuel_outcome_weaken >> goal_assum (drule_at Any) >>
  gen_tac >> BETA_TAC >> strip_tac >> conj_tac
  >- (fs[vars_kept_def, var_below_def] >> metis_tac[]) >>
  `sf.cs_current_bb = exit /\ sf.cs_current_insts = []` by
    simp[Abbr `sf`] >>
  fs[at_point_def] >> metis_tac[])
QED

Theorem range_declare_continuation[local]:
  !k ce id ty lc E Wv.
    (!bc W. cenv_ptrs_in W bc /\ stmt_exits_in E bc lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var bc) W {} E (k bc)) /\
    cenv_ptrs_in Wv ce /\ stmt_exits_in E ce lc ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var ce) Wv {} E
      (do bc <- declare_local ce id ty; k bc od)
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[declare_local_def, LET_THM] >> BETA_TAC >>
  reverse (Cases_on `ce.ce_alloca_locals`)
  >- (asm_rewrite_tac[] >> pure_rewrite_tac[comp_bind_return] >> BETA_TAC >>
      irule fuel_okS_mono >>
      qpat_assum `!bc W. _` (irule_at Any) >>
      simp[cenv_ptrs_in_def, cenv_ptrs_below_def, stmt_exits_in_def] >>
      qexists_tac `Wv` >> gvs[cenv_ptrs_in_def, stmt_exits_in_def] >>
      metis_tac[]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[comp_bind_assoc, comp_bind_return] >> BETA_TAC >>
  match_mp_tac fuel_okS_fresh_var >> gen_tac >> BETA_TAC >>
  pure_rewrite_tac[comp_bind_return] >> BETA_TAC >>
  irule fuel_okS_mono >>
  qpat_assum `!bc W. _` (irule_at Any) >>
  simp[cenv_ptrs_in_def, cenv_ptrs_below_def, stmt_exits_in_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `STRING #"%" (toString n) INSERT Wv` >>
  qpat_x_assum `!bc W. _` kall_tac >>
  gvs[cenv_ptrs_in_def, stmt_exits_in_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> Cases_on `id = id'` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `id = id'` >> gvs[]
  >~ [`var_below _ (STRING #"%" _)`] >- simp[var_below_def]
  >~ [`var_below _ x`]
  >- (qpat_assum `!i v z. FLOOKUP _ i = SOME (PtrVar (Var v) z) ==> var_below n v`
        (drule_then assume_tac) >>
      gvs[var_below_def] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem range_entry_continuation[local]:
  (!n W Wb E counter endpoint cond bodylbl incr exit op ops (B:unit compiler).
    Wb SUBSET {x | x IN W /\ var_below n x} /\
    counter NOTIN Wb /\ endpoint NOTIN Wb /\ counter <> endpoint /\
    counter IN W /\ (op = MSTORE \/ op = INVALID) /\
    fuel_okS (\st. n <= st.cs_next_var) Wb {} (E UNION {exit;incr}) B ==>
    fuel_okS (\st. n <= st.cs_next_var /\
                   var_below st.cs_next_var counter /\
                   var_below st.cs_next_var endpoint) W {} E
      (do emit_inst JMP [Label cond] [];
          new_block cond;
          test <- emit_op EQ [Var counter; Var endpoint];
          emit_inst JNZ [test; Label exit; Label bodylbl] [];
          new_block bodylbl;
          emit_void op ops;
          B;
          emit_jmp_if_not_terminated incr;
          new_block incr;
          tmp <- emit_op ADD [Var counter; Lit 1w];
          emit_inst ASSIGN [tmp] [counter];
          emit_inst JMP [Label cond] [];
          new_block exit;
          return () od)) ==>
  !ty body bc W E lc id fty start_e end_e bound start_op end_op.
    (!cenv' lc Wv' E'.
       cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E' cenv' lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E'
         (compile_stmts cenv' lc ty body)) /\
    cenv_ptrs_in W bc /\ stmt_exits_in E bc lc ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var bc) W {} E
      (do emit_local_alloca bc id;
          entry <- fresh_label "for_entry";
          cond <- fresh_label "for_cond";
          bodylbl <- fresh_label "for_body";
          incr <- fresh_label "for_incr";
          exit <- fresh_label "for_exit";
          emit_inst JMP [Label entry] [];
          new_block entry;
          counter <- fresh_var;
          emit_inst ASSIGN [start_op] [counter];
          rounds <- (case (start_e,end_e) of
            (Literal _ (IntL a),Literal _ (IntL b)) => return (Lit (i2w b - i2w a))
            | _ => emit_op SUB [end_op;start_op]);
          (case (start_e,end_e) of
            (Literal _ (IntL _),Literal _ (IntL _)) => return ()
            | _ => compile_range_bound_checks start_op end_op rounds bound (is_signed_type fty));
          endpoint <- emit_op ADD [start_op;rounds];
          emit_inst JMP [Label cond] [];
          new_block cond;
          test <- emit_op EQ [Var counter;endpoint];
          emit_inst JNZ [test;Label exit;Label bodylbl] [];
          new_block bodylbl;
          (case FLOOKUP bc.ce_vars id of
            SOME (MemLoc off _) => emit_void MSTORE [Lit (n2w off);Var counter]
            | SOME (PtrVar ptr_op _) => emit_void MSTORE [ptr_op;Var counter]
            | _ => emit_void INVALID []);
          compile_stmts bc (InLoop exit incr) ty body;
          emit_jmp_if_not_terminated incr;
          new_block incr;
          tmp <- emit_op ADD [Var counter;Lit 1w];
          emit_inst ASSIGN [tmp] [counter];
          emit_inst JMP [Label cond] [];
          new_block exit;
          return () od)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  match_mp_tac fuel_okS_ignore_bind_keep >>
  conj_tac >- simp[next_stable_cenv_ptrs_below] >>
  conj_tac >- (irule fuel_okS_of_ok >> irule fuel_ok_emit_local_alloca >> simp[]) >>
  ntac 5 (match_mp_tac fuel_okS_bind_keep >>
    (conj_tac >- simp[next_stable_cenv_ptrs_below]) >>
    (conj_tac >- (irule fuel_okS_of_ok >> simp[fuel_ok_prims])) >>
    gen_tac >> BETA_TAC) >>
  qmatch_goalsub_abbrev_tac `comp_bind fresh_var rest` >>
  `fuel_okS (\st. cenv_ptrs_below st.cs_next_var bc) W' {} E
     (do (do emit_inst JMP [Label a] []; new_block a od);
         comp_bind fresh_var rest od)` suffices_by
    simp[comp_ignore_bind_def, comp_bind_assoc] >>
  match_mp_tac fuel_okS_ignore_bind_keep >>
  conj_tac >- simp[next_stable_cenv_ptrs_below] >>
  conj_tac >- (irule fuel_okS_of_ok >> fuel_auto [fuel_ok_emit_inst_jmp] >> simp[]) >>
  simp_tac std_ss [Abbr `rest`] >>
  match_mp_tac fuel_okS_fresh_var >> qx_gen_tac `n` >> BETA_TAC >>
  irule fuel_okS_mono >>
  qexistsl_tac [`E`, `{}`, `\st. cenv_ptrs_below n bc /\ n + 1 <= st.cs_next_var`,
    `STRING #"%" (toString n) INSERT W'`] >>
  simp[pred_setTheory.SUBSET_DEF] >>
  match_mp_tac fuel_okS_ignore_bind_keep >>
  conj_tac >- (simp[next_stable_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule fuel_okS_of_ok >> irule fuel_ok_emit_inst >>
              simp[is_terminator_def]) >>
  qmatch_goalsub_abbrev_tac `comp_bind rounds_action rounds_k` >>
  `!V X. fuel_ok V {} X rounds_action` by
    (simp_tac std_ss [Abbr `rounds_action`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `start_e` >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_emit_op, fuel_ok_return, is_terminator_def]] >>
     Cases_on `end_e` >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_emit_op, fuel_ok_return, is_terminator_def]] >>
     FIRST [CASE_TAC] >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_emit_op, fuel_ok_return, is_terminator_def]] >>
     FIRST [CASE_TAC] >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_emit_op, fuel_ok_return, is_terminator_def]]) >>
  match_mp_tac fuel_okS_bind_keep >>
  conj_tac >- (simp[next_stable_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule fuel_okS_of_ok >> simp[]) >>
  qx_gen_tac `rounds` >> simp_tac std_ss [Abbr `rounds_k`] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `comp_ignore_bind checks check_k` >>
  `!V X. fuel_ok V {} X checks` by
    (simp_tac std_ss [Abbr `checks`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `start_e` >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_compile_range_bound_checks, fuel_ok_return]] >>
     Cases_on `end_e` >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_compile_range_bound_checks, fuel_ok_return]] >>
     FIRST [CASE_TAC] >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_compile_range_bound_checks, fuel_ok_return]] >>
     FIRST [CASE_TAC] >>
     FIRST [simp_tac (srw_ss()) [fuel_ok_compile_range_bound_checks, fuel_ok_return]]) >>
  match_mp_tac fuel_okS_ignore_bind_keep >>
  conj_tac >- (simp[next_stable_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule fuel_okS_of_ok >> simp[]) >>
  simp_tac std_ss [Abbr `check_k`] >>
  qpat_x_assum `Abbrev (rounds_action = _)` kall_tac >>
  qpat_x_assum `Abbrev (checks = _)` kall_tac >>
  qmatch_goalsub_abbrev_tac `comp_bind (emit_op ADD [start_op;rounds]) tail_k` >>
  pure_once_rewrite_tac[emit_op_def] >>
  pure_rewrite_tac[comp_ignore_bind_def, comp_bind_assoc] >> BETA_TAC >>
  match_mp_tac fuel_okS_bind_keep >>
  conj_tac >- (simp[next_stable_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule fuel_okS_of_ok >> simp[fuel_ok_prims]) >>
  gen_tac >> BETA_TAC >>
  pure_rewrite_tac[comp_bind_assoc] >> BETA_TAC >>
  match_mp_tac fuel_okS_fresh_var >> qx_gen_tac `m` >> BETA_TAC >>
  pure_rewrite_tac[comp_bind_assoc, comp_bind_return] >> BETA_TAC >>
  irule fuel_okS_mono >>
  qexistsl_tac [`E`, `{}`, `\st. cenv_ptrs_below n bc /\ n + 1 <= m /\ m + 1 <= st.cs_next_var`,
    `STRING #"%" (toString m) INSERT STRING #"%" (toString n) INSERT W'`] >>
  simp[pred_setTheory.SUBSET_DEF, comp_bind_return] >>
  match_mp_tac fuel_okS_bind_keep >>
  conj_tac >- (simp[next_stable_def] >> rpt strip_tac >> decide_tac) >>
  conj_tac >- (irule fuel_okS_of_ok >> irule fuel_ok_emit >>
    simp[mk_inst_def, is_terminator_def]) >>
  gen_tac >> simp_tac std_ss [Abbr `tail_k`] >> BETA_TAC >>
  reverse (Cases_on `cenv_ptrs_below n bc /\ n + 1 <= m`)
  >- (qpat_x_assum `~(_ /\ _)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rw[fuel_okS_def]) >>
  fs[] >>
  `!j. cenv_ptrs_below n bc /\ n <= j ==> cenv_ptrs_below j bc` by
    (POP_ASSUM_LIST (K ALL_TAC) >> simp[cenv_ptrs_below_def] >>
     rpt strip_tac >> first_x_assum drule >>
     simp[var_below_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  rename1 `emit_inst JNZ [_; Label exit_lbl; Label body_lbl] []` >>
  rename1 `emit_jmp_if_not_terminated incr_lbl` >>
  qabbrev_tac `Wb = {x | x IN W' /\ var_below n x}` >>
  `cenv_ptrs_in Wb bc` by
    (simp[Abbr `Wb`, cenv_ptrs_in_def] >>
     metis_tac[cenv_ptrs_in_def, cenv_ptrs_below_def]) >>
  `stmt_exits_in (E UNION {exit_lbl; incr_lbl}) bc (InLoop exit_lbl incr_lbl)` by
    (gvs[stmt_exits_in_def] >> simp[]) >>
  `fuel_okS (\st. n <= st.cs_next_var) Wb {} (E UNION {exit_lbl; incr_lbl})
     (compile_stmts bc (InLoop exit_lbl incr_lbl) ty body')` by
    (irule fuel_okS_mono >>
     qexistsl_tac [`E UNION {exit_lbl; incr_lbl}`, `{}`,
       `\st. cenv_ptrs_below st.cs_next_var bc`, `Wb`] >>
     simp[]) >>
  irule fuel_okS_mono >>
  qexistsl_tac [`E`, `{}`,
    `\st. n <= st.cs_next_var /\
      var_below st.cs_next_var (STRING #"%" (toString n)) /\
      var_below st.cs_next_var (STRING #"%" (toString m))`,
    `STRING #"%" (toString m) INSERT STRING #"%" (toString n) INSERT W'`] >>
  simp[pred_setTheory.SUBSET_DEF] >> conj_tac
  >- (simp[var_below_def, ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
  Cases_on `FLOOKUP bc.ce_vars id` >> simp_tac std_ss []
  >- (first_x_assum irule >>
      simp[ASCIInumbersTheory.toString_inj] >>
      qexists_tac `Wb` >>
      simp[Abbr `Wb`, pred_setTheory.SUBSET_DEF, var_below_fresh]) >>
  Cases_on `x` >> simp_tac (srw_ss()) [] >>
  first_x_assum irule >>
      simp[ASCIInumbersTheory.toString_inj] >>
      qexists_tac `Wb` >>
      simp[Abbr `Wb`, pred_setTheory.SUBSET_DEF, var_below_fresh]
QED

Theorem range_prefix_join[local]:
  (!n W Wb E counter endpoint cond bodylbl incr exit op ops (B:unit compiler).
    Wb SUBSET {x | x IN W /\ var_below n x} /\
    counter NOTIN Wb /\ endpoint NOTIN Wb /\ counter <> endpoint /\
    counter IN W /\ (op = MSTORE \/ op = INVALID) /\
    fuel_okS (\st. n <= st.cs_next_var) Wb {} (E UNION {exit;incr}) B ==>
    fuel_okS (\st. n <= st.cs_next_var /\
                   var_below st.cs_next_var counter /\
                   var_below st.cs_next_var endpoint) W {} E
      (do emit_inst JMP [Label cond] [];
          new_block cond;
          test <- emit_op EQ [Var counter; Var endpoint];
          emit_inst JNZ [test; Label exit; Label bodylbl] [];
          new_block bodylbl;
          emit_void op ops;
          B;
          emit_jmp_if_not_terminated incr;
          new_block incr;
          tmp <- emit_op ADD [Var counter; Lit 1w];
          emit_inst ASSIGN [tmp] [counter];
          emit_inst JMP [Label cond] [];
          new_block exit;
          return () od)) ==>
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
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp_tac std_ss [Once compile_stmt_def, LET_THM] >>
  match_mp_tac fuel_okS_bind_keep >>
  conj_tac >- simp[next_stable_cenv_ptrs_below] >>
  conj_tac >- (irule fuel_okS_of_ok >> simp[]) >>
  qx_gen_tac `start_op` >> BETA_TAC >>
  match_mp_tac fuel_okS_bind_keep >>
  conj_tac >- simp[next_stable_cenv_ptrs_below] >>
  conj_tac >- (irule fuel_okS_of_ok >> simp[]) >>
  qx_gen_tac `end_op` >> BETA_TAC >>
  ho_match_mp_tac range_declare_continuation >> qexists_tac `lctx` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule (SIMP_RULE (srw_ss()) [] range_entry_continuation) >> simp[] >> metis_tac[]
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
  match_mp_tac range_prefix_join >>
  rpt gen_tac >> strip_tac >> irule range_compiled_tail >> simp[] >>
  qexists_tac `Wb` >> simp[]
QED

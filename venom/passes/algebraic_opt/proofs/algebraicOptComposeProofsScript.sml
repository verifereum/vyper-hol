Theory algebraicOptComposeProofs
Ancestors
  algebraicOptSequenceLocalProofs algebraicOptRelationProofs
  venomExecSemantics venomState list algebraicOptDefs instIdxIndep
  algebraicOptCmpChunkProofs venomInst algebraicOptLocalProofs
  algebraicOptShapeProofs algebraicOptCmpBlockProofs

Theorem ao_scalar_exact_input_transport:
  !inst s t r.
    MEM inst.inst_opcode
      [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
       Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
    step_inst_base inst s = OK t /\
    (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
       eval_operand a r = SOME w) ==>
    ?x v. inst.inst_outputs = [x] /\ t = update_var x v s /\
          step_inst_base inst r = OK (update_var x v r)
Proof
  rpt gen_tac >> pure_rewrite_tac [MEM] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* One commutation boundary shared by both operand-placement passes. *)
Theorem ao_commutative_swap_base:
  !i a b s t.
    (i.inst_opcode = ADD \/ i.inst_opcode = MUL \/
     i.inst_opcode = AND \/ i.inst_opcode = OR \/
     i.inst_opcode = XOR \/ i.inst_opcode = EQ) /\
    i.inst_operands = [a;b] /\ step_inst_base i s = OK t ==>
    step_inst_base (i with inst_operands := [b;a]) s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  simp[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM,
       wordsTheory.WORD_AND_COMM, wordsTheory.WORD_OR_COMM,
       wordsTheory.WORD_XOR_COMM, EQ_SYM_EQ]
QED

Theorem ao_pre_flip_base_ok:
  !i s t. step_inst_base i s = OK t ==>
    step_inst_base (ao_pre_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_pre_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_pre_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_pre_flip_inst_def] >>
  IF_CASES_TAC >> gvs[] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_base_ok:
  !i s t. step_inst_base i s = OK t ==>
    step_inst_base (ao_post_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_post_flip_inst_def] >>
  IF_CASES_TAC >> gvs[] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_step_ok:
  !fuel ctx i s t. step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx (ao_post_flip_inst i) s = OK t
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >> simp[ao_post_flip_inst_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >> simp[ao_post_flip_inst_def] >>
  IF_CASES_TAC >> gvs[step_inst_non_invoke] >>
  irule ao_commutative_swap_base >> metis_tac[]
QED

Theorem ao_post_flip_chunk_ok:
  !xs fuel ctx s t. ao_cmp_exec_chunk fuel ctx xs s = OK t ==>
    ao_cmp_exec_chunk fuel ctx (MAP ao_post_flip_inst xs) s = OK t
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >>
  rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[ao_cmp_exec_chunk_def] >> strip_tac >>
  drule ao_post_flip_step_ok >> simp[]
QED

Theorem ao_scalar_singleton_layout:
  !i ra lbl idx dfg xs.
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    MEM xs [ao_opt_shift i; ao_opt_signextend ra lbl idx i;
            ao_opt_exp i; ao_opt_addsub i; ao_opt_and i;
            ao_opt_muldiv i; ao_opt_or dfg i] ==>
    ?out. xs = [out] /\ out.inst_opcode <> INVOKE /\
          ~is_terminator out.inst_opcode
Proof
  rpt gen_tac >> pure_rewrite_tac[MEM] >> strip_tac >>
  Cases_on `i.inst_operands` >>
  gvs[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
      ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
      ao_opt_or_def] >>
  rename1 `i.inst_operands = a::rest` >>
  Cases_on `rest` >>
  gvs[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
      ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
      ao_opt_or_def] >>
  rename1 `i.inst_operands = a::b::tail` >>
  Cases_on `tail` >>
  gvs[ao_opt_shift_def, ao_opt_signextend_def, ao_opt_exp_def,
      ao_opt_addsub_def, ao_opt_and_def, ao_opt_muldiv_def,
      ao_opt_or_def] >>
  Cases_on `a` >> Cases_on `b` >> gvs[] >> rpt IF_CASES_TAC >>
  gvs[is_terminator_def]
QED

Theorem ao_singleton_write_chunk:
  !xs out s x w fuel ctx.
    xs = [out] /\ out.inst_opcode <> INVOKE /\
    step_inst_base out s = OK (update_var x w s) ==>
    ?u. ao_cmp_exec_chunk fuel ctx xs s = OK u /\
        (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
        u.vs_inst_idx = s.vs_inst_idx + LENGTH xs /\
        (!y. lookup_var y u = lookup_var y (update_var x w s))
Proof
  rpt strip_tac >>
  simp[ao_cmp_exec_chunk_single, step_inst_non_invoke] >>
  simp[update_var_def, lookup_var_def, arithmeticTheory.ADD1]
QED

Theorem ao_peephole_scalar_write_chunk:
  !i s x v dfg ra lbl idx fr fuel ctx.
    MEM i.inst_opcode
      [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
       Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
    i.inst_outputs = [x] /\
    step_inst_base i s = OK (update_var x v s) /\
    SND (fr "not") <> SND (fr "iz") /\
    (!y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
         ~MEM (Var y) i.inst_operands /\ ~MEM y i.inst_outputs) /\
    fr "xor" = fr "not" /\
    (!a w. MEM a i.inst_operands /\ eval_operand a s = SOME w ==>
       in_range (range_get_range ra lbl idx a) w) ==>
    ?w u.
      ao_cmp_exec_chunk fuel ctx (ao_peephole_inst dfg ra lbl idx fr i) s = OK u /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      u.vs_inst_idx = s.vs_inst_idx + LENGTH (ao_peephole_inst dfg ra lbl idx fr i) /\
      (!y. y <> SND (fr "not") /\ y <> SND (fr "iz") ==>
        lookup_var y u = lookup_var y (update_var x w s)) /\
      (w = v \/ (i.inst_opcode = OR /\ ao_all_truthy dfg i /\
                   w = 1w /\ v <> 0w))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode = EQ`
  >- (drule_all ao_opt_eq_chunk_correct >>
      disch_then (qspecl_then [`dfg`, `fuel`, `ctx`] strip_assume_tac) >>
      qexistsl [`v`, `u`] >>
      gvs[ao_peephole_inst_def, update_var_def, lookup_var_def,
          venom_state_component_equality]) >>
  Cases_on `i.inst_opcode = GT \/ i.inst_opcode = LT \/
            i.inst_opcode = SGT \/ i.inst_opcode = SLT`
  >- (drule_all ao_opt_comparator_chunk_correct >>
      disch_then (qspecl_then [`dfg`, `fuel`, `ctx`] strip_assume_tac) >>
      qexistsl [`v`, `u`] >>
      gvs[ao_peephole_inst_def, update_var_def, lookup_var_def,
          venom_state_component_equality]) >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
   MEM (ao_peephole_inst dfg ra lbl idx fr i)
       [ao_opt_shift i; ao_opt_signextend ra lbl idx i;
        ao_opt_exp i; ao_opt_addsub i; ao_opt_and i;
        ao_opt_muldiv i; ao_opt_or dfg i]` by
    (gvs[MEM, ao_peephole_inst_def, is_terminator_def]) >>
  drule_all ao_scalar_singleton_layout >> strip_tac >>
  `MEM out (ao_peephole_inst dfg ra lbl idx fr i)` by simp[] >>
  `?w. step_inst_base out s = OK (update_var x w s) /\
       (w = v \/ (i.inst_opcode = OR /\ ao_all_truthy dfg i /\
                    w = 1w /\ v <> 0w))` by
    (Cases_on `i.inst_opcode = OR`
     >- (`MEM out (ao_opt_or dfg i)` by
           (gvs[ao_peephole_inst_def]) >>
         drule_all ao_opt_or_correct >> strip_tac >>
         gvs[update_var_def, venom_state_component_equality] >>
         qpat_x_assum `_ |+ (x, _) = _ |+ (x, _)`
           (mp_tac o Q.AP_TERM `\m. FLOOKUP m x`) >>
         simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
     qexists `v` >> simp[] >>
     gvs[MEM] >> gvs[ao_peephole_inst_def] >>
     metis_tac[ao_opt_shift_correct, ao_opt_signextend_correct,
               ao_opt_exp_correct, ao_opt_addsub_correct,
               ao_opt_and_correct, ao_opt_muldiv_correct]) >>
  drule_all ao_singleton_write_chunk >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexistsl [`w`, `u`] >> metis_tac[]
QED

Theorem ao_scalar_cross_state_chunk:
  !inst s t r p xs dfg ra lbl idx fr fuel ctx.
    MEM inst.inst_opcode
      [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
       Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
    step_inst_base inst s = OK t /\
    (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
       eval_operand a r = SOME w) /\
    p = ao_pre_flip_inst inst /\
    xs = MAP ao_post_flip_inst (ao_peephole_inst dfg ra lbl idx fr p) /\
    SND (fr "not") <> SND (fr "iz") /\
    (!y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
         ~MEM (Var y) p.inst_operands /\ ~MEM y p.inst_outputs) /\
    fr "xor" = fr "not" /\
    (!a w. MEM a p.inst_operands /\ eval_operand a r = SOME w ==>
       in_range (range_get_range ra lbl idx a) w) ==>
    ?x v w u. inst.inst_outputs = [x] /\ t = update_var x v s /\
      ao_cmp_exec_chunk fuel ctx xs r = OK u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH xs /\
      (!y. y <> SND (fr "not") /\ y <> SND (fr "iz") ==>
        lookup_var y u = lookup_var y (update_var x w r)) /\
      (w = v \/ (p.inst_opcode = OR /\ ao_all_truthy dfg p /\
                   w = 1w /\ v <> 0w))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_scalar_exact_input_transport >> strip_tac >>
  `step_inst_base p r = OK (update_var x v r)` by
    metis_tac[ao_pre_flip_base_ok] >>
  `MEM p.inst_opcode
      [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
       Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
   p.inst_outputs = [x]` by metis_tac[ao_pre_flip_inst_shape] >>
  drule_all ao_peephole_scalar_write_chunk >>
  disch_then (qspecl_then [`dfg`, `fuel`, `ctx`] strip_assume_tac) >>
  drule ao_post_flip_chunk_ok >> strip_tac >>
  qexistsl [`x`, `v`, `w`, `u`] >>
  qpat_x_assum `p = _` kall_tac >> simp[]
QED

(* Observational consequence of the chunk interface; frame and control remain
   separate conclusions of ao_scalar_cross_state_chunk. *)
Theorem ao_scalar_chunk_observations:
  !fn V s r t u p x v w fr.
    ao_main_observations fn V s r /\
    t = update_var x v s /\ p.inst_outputs = [x] /\
    SND (fr "not") NOTIN V /\ SND (fr "iz") NOTIN V /\
    (!y. y <> SND (fr "not") /\ y <> SND (fr "iz") ==>
       lookup_var y u = lookup_var y (update_var x w r)) /\
    (w = v \/ (p.inst_opcode = OR /\ ao_all_truthy dfg p /\
                 w = 1w /\ v <> 0w)) /\
    (p.inst_opcode = OR /\ ao_all_truthy dfg p ==>
       !y. MEM y p.inst_outputs ==> ~ao_main_exact fn y) ==>
    ao_main_observations fn V t u
Proof
  rpt gen_tac >> strip_tac >>
  `ao_main_observations fn V (update_var x v s) (update_var x w r)` by
    (irule ao_main_observations_update >> simp[] >>
     gvs[ao_main_lookup_some]) >>
  gvs[ao_main_observations_def] >> rpt strip_tac >>
  `x' <> SND (fr "not") /\ x' <> SND (fr "iz")` by metis_tac[] >>
  metis_tac[]
QED

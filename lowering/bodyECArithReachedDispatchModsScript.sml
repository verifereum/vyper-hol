(* Terminal EC outcomes at the actual reached operand cuts. *)
Theory bodyECArithReachedDispatchMods
Ancestors
  bodyECArithOperandsMods bodyECArithTailMods
  exprSimFullBundleProps vyperTypeExprSoundness vyperValue

(* Take the cut and launch contracts from their checked producers. *)
val (ambient, reached, pair) =
  let
    val (hyps, pair) = dest_imp (concl (BETA_RULE ec_arith_from_tail_mods))
    val prems = strip_conj hyps
  in
    (list_mk_conj (List.take (prems, length prems - 1)), List.last prems, pair)
  end;
val (cut_vars, reached_body) = strip_forall reached;
val (cut_input, cut_outcome) = dest_imp reached_body;
val staged = rand (concl ec_arith_tail_from_staging_mods);
val addrm = ``if bt = ECAdd then 6w:256 word else 7w``;
val input_len = ``if bt = ECAdd then 128w:256 word else 96w``;
val staged = subst [``addr:256 word`` |-> addrm, ``an:256 word`` |-> input_len] staged;
val launch = ``?p q. ^staged /\
  eval_operand x t2 = SOME p /\ eval_operand y t2 = SOME q /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
  expr_val_rel cx (if bt = ECAdd then ArrayT (BaseT (UintT 256)) (Fixed 2)
                   else BaseT (UintT 256)) v2 y t2``;
val staging = list_mk_forall (cut_vars, mk_imp (cut_input, launch));

Theorem ec_arith_sim_pair_given_stages_mods:
  ^ambient /\ (bt = ECAdd ==> ^staging) /\ (bt = ECMul ==> ^staging) ==> ^pair
Proof
  disch_then (CONJUNCTS_THEN2 (map_every assume_tac o CONJUNCTS)
    (CONJUNCTS_THEN2 (mk_asm "add_stage") (mk_asm "mul_stage"))) >>
  mp_tac (BETA_RULE ec_arith_from_tail_mods) >> impl_tac
  >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      rpt gen_tac >> disch_then (fn th => mk_asm "cut" th THEN
        map_every assume_tac (CONJUNCTS th)) >>
      SUBGOAL_THEN launch (qx_choosel_then [`p`,`q`] (map_every assume_tac o CONJUNCTS))
      >- (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC
          >- asm "add_stage" (drule_then (fn rule =>
               asm "cut" (ACCEPT_TAC o MATCH_MP (SPEC_ALL rule)))) >>
          asm "mul_stage" (drule_then (fn rule =>
               asm "cut" (ACCEPT_TAC o MATCH_MP (SPEC_ALL rule))))) >>
      asm_x "cut" kall_tac >> asm_x "add_stage" kall_tac >> asm_x "mul_stage" kall_tac >>
      mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] (Q.INST
        [`addr` |-> `^addrm`, `an` |-> `^input_len`] ec_arith_tail_from_staging_mods))) >>
      (impl_tac >- (
        rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE REFL_TAC)
        >- (disch_tac >> first_assum ACCEPT_TAC)
        >- (disch_tac >> first_assum ACCEPT_TAC)
        >- (qpat_assum `expr_sim_full_code _ (sa,sb,shadow_sa,shadow_sb)`
              (strip_assume_tac o MATCH_MP expr_sim_full_code_fields) >>
            first_assum ACCEPT_TAC)
        >- (qpat_assum `value_runtime_typed _ (expr_type e1) v1` mp_tac >>
            qpat_assum `expr_type e1 = a` (pure_rewrite_tac o single) >>
            qpat_assum `a = ArrayT _ _` (pure_rewrite_tac o single) >>
            simp[value_runtime_typed_def,evaluate_type_def,type_slot_size_def,
                 wordsTheory.dimword_def])
        >- (qpat_assum `value_runtime_typed _ (expr_type e2) v2` mp_tac >>
            qpat_assum `expr_type e2 = _` (pure_rewrite_tac o single) >>
            qpat_assum `a = ArrayT _ _` (pure_rewrite_tac o single) >>
            Cases_on `bt = ECAdd` >>
            simp[value_runtime_typed_def,evaluate_type_def,type_slot_size_def,
                 wordsTheory.dimword_def])
        >- (qpat_assum `storage_trace_domain _ _ es1.storage_trace`
              (assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
            qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==>
              expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
              (drule_then (map_every assume_tac o CONJUNCTS)) >>
            first_assum ACCEPT_TAC)
        >- (qpat_assum `storage_trace_domain _ _ es2.storage_trace`
              (assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
            qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==>
              expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
              (drule_then (map_every assume_tac o CONJUNCTS)) >>
            first_assum ACCEPT_TAC)
        >- (gen_tac >> disch_tac >>
            qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==>
              stmt_state_rel _ _ _ _ _ _ _ /\ _`
              (drule_then (ACCEPT_TAC o CONJUNCT1)))
        >- (gen_tac >> disch_tac >>
            qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==>
              expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
              (drule_then (map_every assume_tac o CONJUNCTS)) >>
            conj_tac >> first_assum ACCEPT_TAC)
        >- (gen_tac >> disch_tac >>
            qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==>
              expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
              (drule_then (map_every assume_tac o CONJUNCTS)) >>
            conj_tac >> first_assum ACCEPT_TAC))) >>
      disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

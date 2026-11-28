(* Prefix introductions for residual non-call BoolChain head expressions. *)
Theory s1PrefixBoolChainHeadOtherExpr
Ancestors
  s1PrefixAtomicExprIntro s1PrefixAttribute s1PrefixStructLit
  s1PrefixCheckedContextFull s1PrefixPopFullGuard s1PrefixPopIndexIntro
  s1PrefixTypeBuiltinGuarded s1PrefixPreds exprCallBounds vyperAST list alist
  s1PrefixSyntaxCalls vyperTypeCallGraph vyperTypeEvalProofs supportedExprs
  s1PrefixBoolChainHeadMakeArray[qualified,ignore_grammar]

Theorem bool_chain_head_other_expr_prefix_ok:
  !cx h.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr h)) /\
    (!ann bt xs. h <> Builtin ann bt xs) /\
    (!ann ct xs dr. h <> Call ann ct xs dr) /\
    (!ty c a b. h <> IfExp ty c a b) /\
    (!ann obj idx. h <> Subscript ann obj idx) /\
    (!x. expr_size x < expr_size h /\
        (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr x)) ==> body_expr_prefix_ok cx x) ==>
    body_expr_prefix_ok cx h
Proof
  rpt gen_tac >> Cases_on `h` >> simp[] >> strip_tac >>
  TRY (irule atomic_expr_prefix_ok >> simp[] >> NO_TAC) >>
  TRY (rename1 `body_expr_prefix_ok cx (Pop ann bt)` >>
       irule pop_prefix_from_smaller_indices >> strip_tac
       >- (rpt strip_tac >> irule pop_full_target_at_entry >>
           fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
           res_tac >> fs[int_calls_expr_def]) >>
       rpt strip_tac >> qpat_assum `!x. expr_size x < _ /\ _ ==> _` irule >>
       rpt conj_tac
       >- (rpt strip_tac >> res_tac >>
           fs[int_calls_expr_def, int_calls_target_indices] >> metis_tac[]) >>
       drule target_indices_size >> simp[expr_size_def] >> NO_TAC) >>
  reverse (Cases_on `?tops env es. body_const_cells_agree [(NONE,tops)] cx env es`) >>
  TRY (qpat_assum `~(?tops env es. _)` mp_tac >>
       once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >>
       metis_tac[] >> NO_TAC) >>
  qpat_x_assum `?tops env es. _` strip_assume_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
  fs[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND]
  >- (rename1 `body_expr_prefix_ok cx (StructLit ann nsid fields)` >>
      Cases_on `nsid` >> irule structlit_expr_prefix_ok >> simp[] >>
      irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
      simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      qpat_assum `!x. expr_size x < _ /\ _ ==> _` (qspec_then `a` irule) >>
      conj_tac
      >- (drule (Q.INST [`ann` |-> `ann`, `nsid` |-> `(q,r)`] expr_struct_field_bound) >>
          simp[expr_size_def]) >>
      fs[int_calls_exprs_members, MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[])
  >- (irule attribute_expr_prefix_ok >>
      simp[expr_attribute_child_bound] >> fs[expr_size_def] >> metis_tac[])
  >- (irule body_type_builtin_case_prefix >> simp[] >> rpt strip_tac >>
      TRY (metis_tac[] >> NO_TAC) >>
      irule s1PrefixBoolChainHeadMakeArrayTheory.prefix_list_from_members >>
      rpt strip_tac >>
      qpat_assum `!x. expr_size x < _ /\ _ ==> _` irule >>
      rpt conj_tac
      >- (drule expr_list_member_bound >> decide_tac) >>
      fs[int_calls_exprs_members] >> metis_tac[])
  >> (irule pop_prefix_from_smaller_indices >> rpt conj_tac
      >- (rpt strip_tac >> qpat_assum `!x. expr_size x < _ /\ _ ==> _` irule >>
          rpt conj_tac
          >- (drule target_indices_size >> decide_tac) >>
          fs[int_calls_target_indices] >> metis_tac[]) >>
      rpt strip_tac >>
      rename1 `body_inv ts ctx ce cx` >>
      `ts = tops` by
        (qpat_assum `body_const_cells_agree [(NONE,ts)] cx _ _`
           (assume_tac o REWRITE_RULE [bodyFullPredsTheory.body_const_cells_agree_def]) >>
         gvs[]) >>
      gvs[] >> drule_all_then ACCEPT_TAC pop_full_target_at_entry)
QED

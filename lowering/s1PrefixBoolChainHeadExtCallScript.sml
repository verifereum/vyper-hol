(* The ExtCall row of the same-context expression induction. *)
Theory s1PrefixBoolChainHeadExtCall
Ancestors
  s1PrefixBoolChainExtArgDescent s1PrefixBoolChainExtArgDomain
  s1PrefixCheckedContextFull s1PrefixPreds s1PrefixSyntaxCalls vyperTypeCallGraph
  rich_list list alist

Theorem bool_chain_head_extcall_prefix_ok:
  !cx ann stat skip fname ats rt opts args dr.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr))) /\
    (!a. expr_size a < expr_size (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) /\
         (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
           EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
             (vyperTypeCallGraph$int_calls_expr a)) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `body_expr_prefix_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)` by
    (match_mp_tac
       (GEN_ALL (DISCH (lhand (concl bool_chain_extcall_contracts))
         (CONJUNCT2 (UNDISCH bool_chain_extcall_contracts)))) >>
     gen_tac >> disch_tac >>
     `MEM a args` by
       (qpat_x_assum `bool_chain_ext_arg _ _ _` mp_tac >>
        simp[bool_chain_ext_arg_def] >> rpt strip_tac >> gvs[] >>
        metis_tac[MEM_APPEND, MEM, MEM_TAKE, MEM_DROP_IMP]) >>
     conj_tac
     >- (qpat_assum `!a. EVERY _ _ ==> body_expr_full_ok cx a` irule >>
         `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
           fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
         res_tac >> fs[int_calls_expr_def, EVERY_APPEND, int_calls_exprs_members] >>
         metis_tac[]) >>
     qpat_assum `!a. expr_size a < _ /\ _ ==> _` irule >>
     rpt conj_tac
     >- (rpt strip_tac >> res_tac >>
         fs[int_calls_expr_def, EVERY_APPEND, int_calls_exprs_members] >> metis_tac[])
     >> drule bool_chain_ext_arg_smaller >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok cx (Call _ _ _ _)` mp_tac >>
  simp[Once body_expr_prefix_ok_def] >> metis_tac[]
QED

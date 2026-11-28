(* The same-context step of the expression prefix induction. *)
Theory s1PrefixBoolChainSameContextHead
Ancestors
  s1PrefixBoolChainHeadExtCall s1PrefixBoolChainHeadNested
  s1PrefixBoolChainHeadMakeArray s1PrefixBoolChainHeadIfExp
  s1PrefixNamedConstRow s1PrefixOrdinaryBuiltinRow
  s1PrefixBoolChainHeadOtherCall s1PrefixBoolChainHeadSubscript
  s1PrefixBoolChainHeadOtherExpr s1PrefixPreds vyperAST
Libs
  pairLib

Theorem bool_chain_same_context_head_prefix_ok:
  !cx h.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr h)) /\
    ~(?ann nid args dr. h = Call ann (IntCall nid) args dr) /\
    (!a. expr_size a < expr_size h /\
        (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr a)) ==> body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx h
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?ann bt xs. h = Builtin ann bt xs`
  >- (gvs[] >>
      Cases_on `?p n. bt = BoolChain p n`
      >- (gvs[] >> irule bool_chain_head_nested_prefix_ok >> simp[]) >>
      Cases_on `bt = NamedConst`
      >- (gvs[] >> irule named_const_size_row >> simp[]) >>
      Cases_on `?t n. bt = MakeArray t n`
      >- (gvs[] >> irule bool_chain_head_make_array_prefix_ok >> simp[]) >>
      irule ordinary_builtin_size_row >> simp[] >> metis_tac[]) >>
  Cases_on `?ann ct xs dr. h = Call ann ct xs dr`
  >- (gvs[] >>
      Cases_on `?stat skip fsig opts. ct = ExtCall stat skip fsig opts`
      >- (gvs[] >> PairCases_on `fsig` >>
          irule bool_chain_head_extcall_prefix_ok >> simp[]) >>
      irule bool_chain_head_other_call_prefix_ok >> simp[] >> metis_tac[]) >>
  Cases_on `?ty c a b. h = IfExp ty c a b`
  >- (gvs[] >> irule bool_chain_head_ifexp_prefix_ok >> simp[]) >>
  Cases_on `?ann obj idx. h = Subscript ann obj idx`
  >- (gvs[] >> irule bool_chain_head_subscript_prefix_ok >> simp[]) >>
  irule bool_chain_head_other_expr_prefix_ok >> simp[] >> metis_tac[]
QED

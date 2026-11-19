(* Syntactic closure of both iszero traversals, including head rechecks. *)
Theory staticAbortOptMergeIszeroWalk
Ancestors
  asmOptimizer asmOptMergeIszero list


Theorem merge_iszero_walks_preserve_contextual:
  (!pre x tail.
    asm_returns_zero_or_one x /\
    P (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail) ==>
    P (pre ++ [x] ++ tail)) /\
  (!pre l tail.
    P (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO";
               AsmPushLabel l; AsmOp "JUMPI"] ++ tail) ==>
    P (pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail)) ==>
  !p. P p ==> P (FST (merge_iszero p))
Proof
  strip_tac >>
  rule_assum_tac (REWRITE_RULE[GSYM APPEND_ASSOC, APPEND]) >>
  `!sfx pre. P (pre ++ sfx) ==>
      P (pre ++ FST (merge_iszero_pairs sfx))` by
    (ho_match_mp_tac merge_iszero_pairs_ind >>
     reverse (rpt conj_tac)
     >- simp[merge_iszero_pairs_def]
     >- simp[merge_iszero_pairs_def]
     >- simp[merge_iszero_pairs_def] >>
     rpt gen_tac >> strip_tac >> simp[merge_iszero_pairs_fst] >>
     IF_CASES_TAC
     >- (gvs[] >> rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `!pre x tail. asm_returns_zero_or_one x /\ _ ==> _`
           irule >> simp[]) >>
     gvs[] >> rpt strip_tac >>
     first_x_assum (qspec_then `pre ++ [x]` mp_tac) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  `!sfx pre. P (pre ++ sfx) ==>
      P (pre ++ FST (merge_iszero_jumpi sfx))` by
    (ho_match_mp_tac merge_iszero_jumpi_ind >>
     reverse (rpt conj_tac)
     >- simp[merge_iszero_jumpi_def]
     >- simp[merge_iszero_jumpi_def]
     >- simp[merge_iszero_jumpi_def]
     >- simp[merge_iszero_jumpi_def] >>
     rpt gen_tac >> strip_tac >> simp[merge_iszero_jumpi_fst] >>
     IF_CASES_TAC
     >- (Cases_on `c` >> gvs[asm_is_push_label_def] >>
         rpt strip_tac >> first_x_assum irule >>
         qpat_x_assum `!pre l tail.
           P (pre ++ AsmOp "ISZERO" :: _ :: _ :: _ :: tail) ==> _`
           irule >> simp[]) >>
     gvs[] >> rpt strip_tac >>
     first_x_assum (qspec_then `pre ++ [a]` mp_tac) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  rpt strip_tac >> simp[merge_iszero_fst] >>
  first_x_assum (qspecl_then [`FST (merge_iszero_pairs p)`, `[]`] mp_tac) >>
  first_x_assum (qspecl_then [`p`, `[]`] mp_tac) >> simp[APPEND]
QED

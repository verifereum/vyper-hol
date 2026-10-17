Theory vyperNsidSizeBounds
Ancestors
  cv cv_prim cv_std cv_rep

Overload Num[local] = “cv$Num”
Overload Pair[local] = “cv$Pair”

Definition cv_nsid_tree_count_def:
  (cv_nsid_tree_count (f:cv->num) (Num n) = 0:num) ∧
  (cv_nsid_tree_count f (Pair tag payload) =
    if cv$c2b (cv_lt (Num 1) tag) then
      cv_nsid_tree_count f (cv_fst payload) +
      cv_nsid_tree_count f (cv_snd
        (if cv$c2b (cv_lt (Num 2) tag) then cv_snd payload else payload)) +
      (if cv$c2b (cv_lt (Num 2) tag)
       then 1 + f (cv_fst (cv_snd payload)) else 0)
    else 1 + f payload)
Termination
  WF_REL_TAC `measure (cv_size o SND)`
  \\ rpt strip_tac
  \\ Cases_on `payload` \\ simp[cv_size_def, cv_fst_def, cv_snd_def]
  \\ TRY (Cases_on `g'` \\ simp[cv_size_def, cv_fst_def, cv_snd_def])
  \\ IF_CASES_TAC \\ simp[cv_size_def, cv_fst_def, cv_snd_def]
  \\ decide_tac
End

Theorem cv_nsid_tree_count_mk_BN:
  ∀f l r. cv_nsid_tree_count f (cv_mk_BN l r) =
    cv_nsid_tree_count f l + cv_nsid_tree_count f r
Proof
  rpt gen_tac
  \\ Cases_on `l` \\ Cases_on `r`
  \\ simp[cv_mk_BN_def, cv_nsid_tree_count_def,
          cv_if_def, c2b_def, cv_lt_def,
          cv_ispair_def, cv_fst_def, cv_snd_def]
  \\ rpt (IF_CASES_TAC
          \\ simp[cv_nsid_tree_count_def, cv_fst_def, cv_snd_def,
                  cv_if_def, c2b_def, cv_lt_def])
QED

Theorem cv_nsid_tree_count_mk_BS:
  ∀f l v r. cv_nsid_tree_count f (cv_mk_BS l v r) =
    cv_nsid_tree_count f l + (1 + f v) + cv_nsid_tree_count f r
Proof
  rpt gen_tac
  \\ Cases_on `l` \\ Cases_on `r`
  \\ simp[cv_mk_BS_def, cv_nsid_tree_count_def,
          cv_if_def, c2b_def, cv_lt_def,
          cv_ispair_def, cv_fst_def, cv_snd_def]
  \\ rpt (IF_CASES_TAC
          \\ simp[cv_nsid_tree_count_def, cv_fst_def, cv_snd_def,
                  cv_if_def, c2b_def, cv_lt_def])
  \\ decide_tac
QED

Theorem cv_nsid_tree_count_delete:
  ∀key t f old.
    cv_lookup key t = Pair (Num 1) old ⇒
    cv_nsid_tree_count f (cv_delete key t) < cv_nsid_tree_count f t
Proof
  ho_match_mp_tac cv_delete_ind
  \\ rpt strip_tac
  \\ simp[Once cv_delete_def, Once cv_lookup_def]
  \\ rpt (IF_CASES_TAC
          \\ gvs[cv_nsid_tree_count_def, cv_nsid_tree_count_mk_BN,
                 cv_nsid_tree_count_mk_BS,
                 cv_repTheory.cv_termination_simp])
  \\ qpat_x_assum `cv_lookup _ _ = Pair (Num 1) old` mp_tac
  \\ simp[Once cv_lookup_def, cv_lt_def, cv_if_def, c2b_def,
          cv_sub_def, cv_mod_def, cv_div_def, cv_fst_def, cv_snd_def,
          cv_ispair_def]
  \\ strip_tac
  \\ gvs[c2b_def, cv_lt_def]
  \\ res_tac
  \\ TRY (qpat_x_assum `∀f. cv_nsid_tree_count f _ < _`
           (qspec_then `f` assume_tac))
  \\ TRY (Cases_on `key`)
  \\ TRY (Cases_on `x1`)
  \\ TRY (Cases_on `t`)
  \\ gvs[cv_lt_def, cv_ispair_def, cv_if_def, c2b_def,
         cv_fst_def, cv_snd_def, cv_nsid_tree_count_def]
  \\ TRY (Cases_on `m` \\ gvs[c2b_def, cv_lt_def])
  \\ decide_tac
QED

Theorem cv_nsid_tree_count_insert_less:
  ∀key new t f old.
    cv_lookup key t = Pair (Num 1) old ∧ f new < f old ⇒
    cv_nsid_tree_count f (cv_insert key new t) < cv_nsid_tree_count f t
Proof
  ho_match_mp_tac cv_insert_ind
  \\ rpt strip_tac
  \\ simp[Once cv_insert_def, Once cv_lookup_def]
  \\ rpt (IF_CASES_TAC
          \\ gvs[cv_nsid_tree_count_def,
                 cv_repTheory.cv_termination_simp])
  \\ qpat_x_assum `cv_lookup _ _ = Pair (Num 1) old` mp_tac
  \\ simp[Once cv_lookup_def, cv_lt_def, cv_if_def, c2b_def,
          cv_sub_def, cv_mod_def, cv_div_def, cv_fst_def, cv_snd_def,
          cv_ispair_def]
  \\ strip_tac
  \\ gvs[c2b_def, cv_lt_def]
  \\ res_tac
  \\ TRY (qpat_x_assum `∀f old'. _` (qspecl_then [`f`,`old`] assume_tac))
  \\ TRY (Cases_on `key`)
  \\ TRY (Cases_on `x1`)
  \\ TRY (Cases_on `t`)
  \\ gvs[cv_lt_def, cv_ispair_def, cv_if_def, c2b_def,
         cv_fst_def, cv_snd_def, cv_nsid_tree_count_def]
  \\ TRY (Cases_on `m` \\ gvs[c2b_def, cv_lt_def])
  \\ res_tac
  \\ decide_tac
QED

Theorem cv_nsid_size_projections:
  ∀x. cv_size (cv_fst x) ≤ cv_size x ∧
      cv_size (cv_snd x) ≤ cv_size x
Proof
  Cases \\ simp[cv_size_def, cv_fst_def, cv_snd_def]
QED

Theorem cv_nsid_lookup_numeric_shape_aux:
  ∀key t result.
    cv_lookup key t = result ⇒
    result = Num 0 ∨ ∃old. result = Pair (Num 1) old
Proof
  completeInduct_on `cv_size t`
  \\ rpt strip_tac
  \\ Cases_on `t`
  \\ qpat_x_assum `cv_lookup key _ = result` mp_tac
  \\ simp[Once cv_lookup_def, cv_lt_def, cv_if_def, c2b_def,
          cv_ispair_def, cv_fst_def, cv_snd_def]
  \\ rpt (IF_CASES_TAC \\ gvs[])
  \\ `cv_size (cv_fst g') <= cv_size g' ∧
      cv_size (cv_snd g') <= cv_size g' ∧
      cv_size (cv_snd (cv_snd g')) <= cv_size g'`
       by (mp_tac (Q.SPEC `g'` cv_nsid_size_projections)
           \\ mp_tac (Q.SPEC `cv_snd g'` cv_nsid_size_projections)
           \\ decide_tac)
  \\ `cv_size g' < cv_size g + (cv_size g' + 1)` by decide_tac
  \\ metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem cv_nsid_lookup_numeric_shape:
  ∀key t. cv_lookup key t = Num 0 ∨
    ∃old. cv_lookup key t = Pair (Num 1) old
Proof
  metis_tac[cv_nsid_lookup_numeric_shape_aux]
QED

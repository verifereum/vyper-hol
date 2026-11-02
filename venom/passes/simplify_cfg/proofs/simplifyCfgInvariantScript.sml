(* Parametric preservation separates DFS control from instruction properties. *)
Theory simplifyCfgInvariant
Ancestors
  simplifyCfgDefs cfgTransform venomInst list

Theorem try_bypass_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) ==>
  !succs f lm a.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a ==>
    Q (FST (try_bypass f lm a succs))
Proof
  strip_tac >> Induct_on `succs` >> simp[try_bypass_def] >>
  rpt gen_tac >> strip_tac >>
  simp[Once try_bypass_def] >>
  Cases_on `lookup_block h f.fn_blocks` >> simp[] >>
  rename1 `lookup_block h f.fn_blocks = SOME b` >>
  Cases_on `can_bypass_jump f a b` >> simp[] >>
  Cases_on `lookup_block (HD (bb_succs b)) f.fn_blocks` >> simp[] >>
  rename1 `lookup_block (HD (bb_succs b)) f.fn_blocks = SOME target` >>
  Cases_on `phi_values_agree a.bb_label b.bb_label target.bb_instructions` >>
  simp[] >>
  Cases_on `do_merge_jump f a b lm` >> simp[] >>
  PairCases_on `x` >> simp[] >> metis_tac[]
QED

Theorem collapse_dfs_preserves_predicate_joint:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  (!f lm vis lbl. Q f ==> Q (FST (collapse_dfs f lm vis lbl))) /\
  (!f lm vis succs. Q f ==> Q (FST (collapse_dfs_succs f lm vis succs)))
Proof
  strip_tac >> ho_match_mp_tac collapse_dfs_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      simp[NoAsms, Once collapse_dfs_def] >>
      Cases_on `lookup_block lbl f.fn_blocks` >> simp[] >>
      rename1 `lookup_block lbl f.fn_blocks = SOME bb` >>
      Cases_on `bb_succs bb`
      >- (gvs[try_bypass_def] >> Cases_on `MEM lbl vis` >> simp[] >>
          metis_tac[]) >>
      rename1 `bb_succs bb = next::rest` >> Cases_on `rest`
      >- (simp[] >> Cases_on `lookup_block next f.fn_blocks` >> simp[]
          >- (Cases_on `MEM lbl vis` >> simp[]) >>
          rename1 `lookup_block next f.fn_blocks = SOME b` >>
          Cases_on `can_merge_blocks f bb b`
          >- (gvs[] >> first_x_assum irule >> simp[] >>
              first_x_assum irule >> simp[] >> metis_tac[]) >>
          Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
      `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
        metis_tac[lookup_block_member_label] >>
      `Q (FST (try_bypass f lm bb (next::h::t)))` by
        (irule try_bypass_preserves_predicate >> simp[] >> metis_tac[]) >>
      Cases_on `try_bypass f lm bb (next::h::t)` >>
      PairCases_on `r` >> Cases_on `r1` >> gvs[] >>
      Cases_on `MEM lbl vis` >> simp[] >> gvs[]) >>
  conj_tac
  >- simp[NoAsms, Once collapse_dfs_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[NoAsms, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs f lm vis lbl` >> PairCases_on `r` >> gvs[]
QED

Theorem collapse_dfs_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  !f lm vis lbl. Q f ==> Q (FST (collapse_dfs f lm vis lbl))
Proof
  strip_tac >> drule collapse_dfs_preserves_predicate_joint >> simp[]
QED

Theorem collapse_dfs_succs_preserves_predicate:
  (!f lm a b g lm'.
    Q f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> Q g) /\
  (!f lbl next a b.
    Q f /\ lookup_block lbl f.fn_blocks = SOME a /\
    lookup_block next f.fn_blocks = SOME b /\ can_merge_blocks f a b ==>
    Q (f with fn_blocks := update_succ_phi_labels next lbl
      (replace_block lbl (merge_blocks a b) (remove_block next f.fn_blocks))
      (bb_succs (merge_blocks a b)))) ==>
  !f lm vis succs. Q f ==> Q (FST (collapse_dfs_succs f lm vis succs))
Proof
  strip_tac >> drule collapse_dfs_preserves_predicate_joint >> simp[]
QED

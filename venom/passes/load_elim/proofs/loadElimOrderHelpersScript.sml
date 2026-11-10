Theory loadElimOrderHelpers
Ancestors
  loadElimDefs loadElimSupportHelpers loadElimLatticeSoundHelpers
  finite_map pred_set list rich_list arithmetic

Theorem le_join_raw_lookup_eq:
  FLOOKUP (load_join_raw a b) k =
    case (FLOOKUP a k, FLOOKUP b k) of
      (SOME xs, SOME ys) => SOME (operand_list_union xs ys)
    | _ => NONE
Proof
  simp[load_join_raw_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `FLOOKUP a k` >> Cases_on `FLOOKUP b k` >>
  gvs[FLOOKUP_DEF]
QED

Theorem le_operand_union_self:
  operand_list_union xs xs = xs
Proof
  simp[operand_list_union_def, FILTER_EQ_NIL, EVERY_MEM]
QED

Theorem le_join_absorption:
  load_join (load_join a b) b = load_join a b
Proof
  Cases_on `a`
  >- (Cases_on `b` >> simp[load_join_def, fmap_eq_flookup] >>
      gen_tac >> simp[le_join_raw_lookup_eq] >>
      rename1 `FLOOKUP m k` >> Cases_on `FLOOKUP m k` >>
      simp[le_operand_union_self]) >>
  Cases_on `b` >- simp[load_join_def] >>
  rename1 `load_join (load_join (SOME m) (SOME n)) (SOME n)` >>
  simp[load_join_def, fmap_eq_flookup] >> gen_tac >>
  simp[le_join_raw_lookup_eq] >>
  rename1 `FLOOKUP m k` >>
  Cases_on `FLOOKUP m k` >> Cases_on `FLOOKUP n k` >>
  simp[le_operand_union_absorb_right]
QED

Definition le_lattice_leq_def:
  (le_lattice_leq NONE b <=> T) /\
  (le_lattice_leq (SOME a) NONE <=> F) /\
  (le_lattice_leq (SOME a) (SOME b) <=>
    !k ys. FLOOKUP b k = SOME ys ==>
      ?xs tail. FLOOKUP a k = SOME xs /\ ys = xs ++ tail)
End

Definition le_key_rank_def:
  (le_key_rank vals NONE = CARD vals + 1) /\
  (le_key_rank vals (SOME vs) = LENGTH vs)
End

Definition le_lattice_rank_def:
  (le_lattice_rank keys vals NONE = 0) /\
  (le_lattice_rank keys vals (SOME m) =
    1 + SIGMA (\k. le_key_rank vals (FLOOKUP m k)) keys)
End

Theorem le_operand_union_prefix:
  ?tail. operand_list_union xs ys = xs ++ tail
Proof
  simp[operand_list_union_def]
QED

Theorem le_join_inflationary:
  le_lattice_leq a (load_join a b)
Proof
  Cases_on `a` >- simp[le_lattice_leq_def] >>
  Cases_on `b`
  >- (simp[load_join_def, le_lattice_leq_def] >> metis_tac[APPEND_NIL]) >>
  simp[load_join_def, le_lattice_leq_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[le_operand_union_prefix]
QED

Theorem le_supported_list_length[local]:
  FINITE vals /\ EVERY (\v. v IN vals) vs /\ ALL_DISTINCT vs ==>
  LENGTH vs <= CARD vals
Proof
  rpt strip_tac >>
  `set vs SUBSET vals` by (gvs[SUBSET_DEF, EVERY_MEM]) >>
  drule_all CARD_SUBSET >>
  simp[ALL_DISTINCT_CARD_LIST_TO_SET]
QED

Theorem le_supported_key_rank_bound:
  FINITE vals /\ le_lattice_supported keys vals (SOME m) ==>
  le_key_rank vals (FLOOKUP m k) <= CARD vals + 1
Proof
  simp[le_lattice_supported_def, unwrap_load_lattice_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP m k` >> simp[le_key_rank_def] >>
  first_x_assum drule >> strip_tac >>
  drule_all le_supported_list_length >> simp[]
QED

Theorem le_key_rank_mono:
  FINITE vals /\
  le_lattice_supported keys vals (SOME a) /\
  le_lattice_leq (SOME a) (SOME b) ==>
  le_key_rank vals (FLOOKUP a k) <= le_key_rank vals (FLOOKUP b k)
Proof
  simp[le_lattice_supported_def, unwrap_load_lattice_def, le_lattice_leq_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP b k`
  >- (simp[le_key_rank_def] >> Cases_on `FLOOKUP a k` >>
      simp[le_key_rank_def] >> first_x_assum drule >> strip_tac >>
      drule_all le_supported_list_length >> simp[]) >>
  first_x_assum drule >> strip_tac >> simp[le_key_rank_def]
QED

Theorem le_key_rank_equal:
  FINITE vals /\
  le_lattice_supported keys vals (SOME a) /\
  le_lattice_leq (SOME a) (SOME b) /\
  le_key_rank vals (FLOOKUP a k) = le_key_rank vals (FLOOKUP b k) ==>
  FLOOKUP a k = FLOOKUP b k
Proof
  simp[le_lattice_supported_def, unwrap_load_lattice_def, le_lattice_leq_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP b k`
  >- (Cases_on `FLOOKUP a k` >> gvs[le_key_rank_def] >>
      first_x_assum drule >> strip_tac >>
      drule_all le_supported_list_length >> simp[]) >>
  first_x_assum drule >> strip_tac >> gvs[le_key_rank_def]
QED

Theorem le_lattice_rank_bound:
  FINITE keys /\ FINITE vals /\ le_lattice_supported keys vals a ==>
  le_lattice_rank keys vals a <= 1 + CARD keys * (CARD vals + 1)
Proof
  rpt strip_tac >> Cases_on `a` >> simp[le_lattice_rank_def] >>
  `SIGMA (\k. le_key_rank vals (FLOOKUP x k)) keys <=
    SIGMA (K (CARD vals + 1)) keys` suffices_by simp[SUM_IMAGE_CONSTANT, MULT_COMM] >>
  irule SUM_IMAGE_MONO_LESS_EQ >> simp[] >> rpt strip_tac >>
  irule le_supported_key_rank_bound >> metis_tac[]
QED

Theorem le_lattice_rank_mono:
  FINITE keys /\ FINITE vals /\
  le_lattice_supported keys vals a /\ le_lattice_leq a b ==>
  le_lattice_rank keys vals a <= le_lattice_rank keys vals b
Proof
  rpt strip_tac >> Cases_on `a` >> Cases_on `b` >>
  gvs[le_lattice_rank_def, le_lattice_leq_def] >>
  irule SUM_IMAGE_MONO_LESS_EQ >> simp[] >> rpt strip_tac >>
  irule le_key_rank_mono >> simp[le_lattice_leq_def] >> metis_tac[]
QED

Theorem le_lattice_rank_strict:
  FINITE keys /\ FINITE vals /\
  le_lattice_supported keys vals a /\ le_lattice_supported keys vals b /\
  le_lattice_leq a b /\ a <> b ==>
  le_lattice_rank keys vals a < le_lattice_rank keys vals b
Proof
  rpt strip_tac >> Cases_on `a` >> Cases_on `b` >>
  gvs[le_lattice_rank_def, le_lattice_leq_def] >>
  irule SUM_IMAGE_MONO_LESS >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule le_key_rank_mono >>
      simp[le_lattice_leq_def] >> metis_tac[]) >>
  `?k. FLOOKUP x k <> FLOOKUP x' k` by metis_tac[fmap_eq_flookup] >>
  `k IN keys` by
    (gvs[le_lattice_supported_def, unwrap_load_lattice_def] >>
     Cases_on `FLOOKUP x k` >> Cases_on `FLOOKUP x' k` >> gvs[] >> metis_tac[]) >>
  qexists `k` >> simp[] >>
  `le_key_rank vals (FLOOKUP x k) <= le_key_rank vals (FLOOKUP x' k)` by
    (irule le_key_rank_mono >> simp[le_lattice_leq_def] >> metis_tac[]) >>
  `le_key_rank vals (FLOOKUP x k) <> le_key_rank vals (FLOOKUP x' k)` by
    (strip_tac >> drule le_key_rank_equal >>
     simp[le_lattice_leq_def] >> metis_tac[]) >> simp[]
QED

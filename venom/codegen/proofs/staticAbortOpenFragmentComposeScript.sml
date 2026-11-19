(* Occurrence-indexed gluing and rooted restriction of open fragments. *)
Theory staticAbortOpenFragmentCompose
Ancestors
  asmSem pred_set arithmetic

Theorem open_fragment_compose:
!p (V:(num#num)->bool) X e
 (S:(num#num)->asm_state->bool) (I:(num#num)->'a)
 (OK:(num#num)->'a->bool) (Good:(num#num)->bool)
 (R:(num#num)->(num#num)->bool) link
 (local_rank:(num#num)->num) (order:num->num) (B:num) req.
!A. A = V DIFF X ==>
!E. E = (\x y. x IN A /\ ?z. R x z /\ y = (if z IN X then link z else z)) ==>
!W. W = {x | x IN A /\
  ?n (path:num->num#num). path 0 = e /\ path n = x /\
    (!k. k < n ==> E (path k) (path(SUC k)))} ==>
!rank. rank = (\x. order (FST x) * (B+1) + local_rank x) ==>
FINITE V /\ X SUBSET V /\ e IN A /\
(!x. x IN V ==> local_rank x <= B /\ ?t. S x t) /\
(!x. x IN A ==> Good x) /\
(!z. z IN X ==>
  link z IN A /\ order (FST(link z)) < order(FST z) /\
  I (link z) = I z /\ (!t. S (link z) t <=> S z t)) /\
(!x z. R x z ==>
  x IN A /\ z IN V /\ FST x = FST z /\
  local_rank z < local_rank x /\ OK x (I z)) /\
(!x t. x IN A /\ S x t ==>
  (?u. (asm_steps (SND(compute_label_offsets p))
           (build_offset_to_pc p) p 1 t = AsmRevert u \/
         asm_steps (SND(compute_label_offsets p))
           (build_offset_to_pc p) p 1 t = AsmFault u) /\
        u.as_requests = req) \/
  (?z u. R x z /\
     asm_steps (SND(compute_label_offsets p))
       (build_offset_to_pc p) p 1 t = AsmOK u /\ S z u)) ==>
FINITE W /\ e IN W /\
(!x. x IN W ==> Good x /\ (?t. S x t)) /\
(!x y. x IN W /\ E x y ==>
  y IN W /\ rank y < rank x /\ OK x (I y)) /\
(!x. x IN W ==>
  ?n (path:num->num#num). path 0 = e /\ path n = x /\
    (!k. k <= n ==> path k IN W) /\
    (!k. k < n ==> E (path k) (path(SUC k)))) /\
(!x t. x IN W /\ S x t ==>
  (?u. (asm_steps (SND(compute_label_offsets p))
           (build_offset_to_pc p) p 1 t = AsmRevert u \/
         asm_steps (SND(compute_label_offsets p))
           (build_offset_to_pc p) p 1 t = AsmFault u) /\
        u.as_requests = req) \/
  (?y u. y IN W /\ E x y /\
     asm_steps (SND(compute_label_offsets p))
       (build_offset_to_pc p) p 1 t = AsmOK u /\ S y u))
Proof
  ntac 14 gen_tac >>
  qx_gen_tac `A` >> disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  qabbrev_tac `dest = \z. if z IN X then link z else z` >>
  qx_gen_tac `E` >>
  disch_then (fn eq => qpat_assum `Abbrev (dest = _)`
    (fn d => assume_tac (eq |> REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] d)]
      |> CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))) >>
  qabbrev_tac `reach = \x. ?n (path:num->num#num).
    path 0 = e /\ path n = x /\
    !k. k < n ==> E (path k) (path(SUC k))` >>
  qx_gen_tac `nodes` >> disch_tac >>
  `Abbrev (nodes = {x | x IN A /\ reach x})` by
    simp[markerTheory.Abbrev_def, Abbr `reach`] >>
  qpat_x_assum `nodes = _` kall_tac >>
  qx_gen_tac `rank` >> disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  strip_tac >>
  `!z. z IN V ==> dest z IN A /\ I' (dest z) = I' z /\
      (!t. S' (dest z) t <=> S' z t)` by
    (gen_tac >> strip_tac >> Cases_on `z IN X` >>
     simp[Abbr `dest`] >> gvs[Abbr `A`] >> metis_tac[]) >>
  `!x y. E x y ==> y IN A /\ rank y < rank x /\ OK' x (I' y)` by
    (rpt gen_tac >> simp[Abbr `E`] >> strip_tac >>
     qpat_assum `!x z. R x z ==> _` drule >> strip_tac >>
     `dest z IN A /\ I' (dest z) = I' z` by metis_tac[] >>
     simp[] >> simp[Abbr `rank`] >>
     Cases_on `z IN X`
     >- (qpat_assum `!z. z IN X ==> _` drule >> strip_tac >>
         `local_rank (link z) <= B` by
           (gvs[Abbr `A`] >> metis_tac[]) >>
         simp[Abbr `dest`] >>
         `SUC (order (FST (link z))) <= order (FST z)` by decide_tac >>
         `SUC (order (FST (link z))) * (B+1) <=
          order (FST z) * (B+1)` by
           (irule LESS_MONO_MULT >> simp[]) >>
         qpat_x_assum `SUC _ * _ <= _` mp_tac >>
         rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
     simp[Abbr `dest`]) >>
  `reach e` by
    (simp[Abbr `reach`] >> qexistsl [`0`, `\k. e`] >> simp[]) >>
  `!x y. reach x /\ E x y ==> reach y` by
    (rpt gen_tac >> simp[Abbr `reach`] >> strip_tac >>
     qexistsl [`SUC n`, `\k. if k <= n then path k else y`] >>
     simp[] >> gen_tac >> strip_tac >>
     Cases_on `k < n`
     >- (simp[] >> first_x_assum irule >> simp[]) >>
     `k = n` by decide_tac >> simp[]) >>
  `!x y. x IN nodes /\ E x y ==> y IN nodes` by
    (simp[Abbr `nodes`] >> metis_tac[]) >>
  conj_tac
  >- (irule SUBSET_FINITE_I >> qexists `V` >>
      simp[SUBSET_DEF, Abbr `nodes`, Abbr `A`]) >>
  conj_tac >- simp[Abbr `nodes`] >>
  conj_tac >- (simp[Abbr `nodes`, Abbr `A`] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (gen_tac >> simp[Abbr `nodes`] >> strip_tac >>
      qpat_x_assum `reach x` mp_tac >> simp[Abbr `reach`] >>
      strip_tac >> qexistsl [`n`, `path`] >> simp[] >>
      gen_tac >> strip_tac >> conj_tac
      >- (Cases_on `k` >- simp[] >>
          rename1 `SUC j <= n` >> `j < n` by decide_tac >>
          metis_tac[]) >>
      qexistsl [`k`, `path`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `x IN A` by gvs[Abbr `nodes`] >>
  qpat_x_assum `!x t. x IN A /\ S' x t ==> _` drule_all >>
  disch_then (DISJ_CASES_THEN2 (fn th => metis_tac[th]) strip_assume_tac) >>
  disj2_tac >> qexistsl [`dest z`, `u`] >>
  `E x (dest z)` by (simp[Abbr `E`] >> metis_tac[]) >>
  metis_tac[]
QED

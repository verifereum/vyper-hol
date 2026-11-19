(* Retained-exit composition at an arbitrary semantic interface. *)
Theory staticAbortOpenFragmentSplice
Ancestors pair[qualified,ignore_grammar]
  asmSem pred_set arithmetic

Theorem open_fragment_splice:
!K Good OK Step Fail
 (V1:(num#num)->bool) (V2:(num#num)->bool) X2 e1 e2 z
 (r1:(num#num)->num) (r2:(num#num)->num)
 (I1:(num#num)->'a) (I2:(num#num)->'a) R1 R2 f.
!Frag. Frag = (\V X r I R.
  FINITE V /\ X SUBSET V /\
  (!x. x IN V ==> ?t:asm_state. K (I x) t) /\
  (!x. x IN V DIFF X ==> Good (I x)) /\
  (!x y. R x y ==> x IN V DIFF X /\ y IN V /\
     r y < r x /\ OK (I x) (I y)) /\
  (!x t. x IN V DIFF X /\ K (I x) t ==>
     Fail t \/ ?y u. R x y /\ Step t u /\ K (I y) u)) ==>
!Reach. Reach = (\R e x. ?n (path:num->num#num).
  path 0=e /\ path n=x /\ !k. k<n ==> R (path k) (path(SUC k))) ==>
!L. L = (\x:num#num. (f,2*SND x)) ==>
!D. D = (\x:num#num. (f,2*SND x+1)) ==>
!d. d = (\x. if x=z then D e2 else L x) ==>
!U. U = IMAGE L (V1 DELETE z) UNION IMAGE D V2 ==>
!e. e = d e1 ==>
!E. E = (\a b. (?x y. R1 x y /\ a=L x /\ b=d y) \/
                (?x y. R2 x y /\ a=D x /\ b=D y)) ==>
Frag V1 {z} r1 I1 R1 /\ Frag V2 X2 r2 I2 R2 /\
e1 IN V1 /\ e2 IN V2 /\ I1 z=I2 e2 /\
(!x. x IN V1 ==> FST x=f /\ Reach R1 e1 x) /\
(!x. x IN V2 ==> FST x=f /\ Reach R2 e2 x) ==>
?r I. Frag U (IMAGE D X2) r I E /\ e IN U /\ I e=I1 e1 /\
  (!x. x IN V1 DELETE z ==> I(L x)=I1 x) /\
  (!x. x IN V2 ==> I(D x)=I2 x) /\
  (!x. x IN U ==> FST x=f /\ Reach E e x)
Proof
  ntac 18 gen_tac >>
  map_every (fn name => qx_gen_tac name >> disch_then
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Frag`, `Reach`, `L`, `D`, `d`, `U`, `e`, `E`] >>
  qabbrev_tac `Y = IMAGE D X2` >>
  fs[Abbr `Frag`] >> strip_tac >>
  qabbrev_tac `B=MAX_SET (IMAGE r2 V2)` >>
  qabbrev_tac `J= \(x:num#num).
    if EVEN(SND x) then I1(f,SND x DIV 2) else I2(f,SND x DIV 2)` >>
  qabbrev_tac `rr= \(x:num#num).
    if EVEN(SND x) then r1(f,SND x DIV 2)+B+1 else r2(f,SND x DIV 2)` >>
  `!x. x IN V2 ==> r2 x<=B` by
    (rpt strip_tac >> simp[Abbr `B`] >> irule MAX_SET_PROPERTY >>
     simp[] >> metis_tac[IN_IMAGE]) >>
  `(!x. x IN V1 ==> J(L x)=I1 x /\ rr(L x)=r1 x+B+1) /\
   (!x. x IN V2 ==> J(D x)=I2 x /\ rr(D x)=r2 x)` by
    ((conj_tac >> rpt strip_tac >>
     `FST x=f` by metis_tac[] >>
     `x=(f,SND x)` by metis_tac[pairTheory.PAIR] >>
     simp[Abbr `J`, Abbr `rr`, Abbr `L`, Abbr `D`,
       EVEN_ADD, EVEN_MULT] >> (metis_tac[pairTheory.PAIR, Abbr `J`, Abbr `rr`, Abbr `L`, Abbr `D`, EVEN_ADD, EVEN_MULT]))) >>
  `!x. x IN V1 ==> J(d x)=I1 x` by
    (rpt strip_tac >> Cases_on `x=z` >> simp[Abbr `d`]) >>
  qexistsl [`rr`, `J`] >>
  conj_tac >- suspend "fragment" >>
  conj_tac >- (simp[Abbr `e`, Abbr `d`, Abbr `U`] >>
    Cases_on `e1=z` >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `e`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  suspend "reachable"
QED

Resume open_fragment_splice[fragment]:
  `!x y. L x <> D y` by
    (simp[Abbr `L`, Abbr `D`] >> POP_ASSUM_LIST (K all_tac) >>
     rpt gen_tac >> strip_tac >>
     pop_assum (mp_tac o AP_TERM ``EVEN``) >> simp[EVEN_MULT, EVEN_ADD]) >>
  `!x y. x IN V2 /\ y IN V2 ==> (D x=D y <=> x=y)` by
    (rpt strip_tac >>
     `FST x=f /\ FST y=f` by metis_tac[] >>
     simp[Abbr `D`] >> metis_tac[pairTheory.PAIR]) >>
  `!x. x IN V1 /\ x<>z ==> L x IN U /\ L x NOTIN Y` by
    (simp[Abbr `U`, Abbr `Y`, IN_IMAGE] >> metis_tac[]) >>
  `!x. x IN V2 ==> D x IN U /\ (D x IN Y <=> x IN X2)` by
    (simp[Abbr `U`, Abbr `Y`, IN_IMAGE] >> metis_tac[SUBSET_DEF]) >>
  `!x. x IN V1 ==> d x IN U` by
    (rpt strip_tac >> Cases_on `x=z` >> simp[Abbr `d`]) >>
  conj_tac >- simp[Abbr `U`] >>
  conj_tac >- (simp[Abbr `Y`, SUBSET_DEF, IN_IMAGE] >> metis_tac[SUBSET_DEF]) >>
  conj_tac >- (simp[Abbr `U`, IN_IMAGE] >> metis_tac[]) >>
  conj_tac >- (simp[Abbr `U`, IN_IMAGE] >> metis_tac[]) >>
  conj_tac >- suspend "edge" >>
  suspend "step"
QED

Resume open_fragment_splice[edge]:
  simp[Abbr `E`] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (qpat_x_assum `!x y. R1 x y ==> _` drule >> strip_tac >>
      simp[] >> Cases_on `y'=z` >> simp[Abbr `d`] >>
      `r2 e2<=B` by metis_tac[] >> decide_tac) >>
  qpat_x_assum `!x y. R2 x y ==> _` drule >> strip_tac >> simp[]
QED

Resume open_fragment_splice[step]:
  simp[Abbr `U`, IN_IMAGE] >> rpt gen_tac >> strip_tac >> gvs[]
  >- suspend "left_step" >>
  suspend "right_step"
QED

Resume open_fragment_splice[left_step]:
  rename1 `K' (I1 a) t` >>
  qpat_x_assum `!x t. (x IN V1 /\ x<>z) /\ _ ==> _`
    (qspecl_then [`a`, `t`] mp_tac) >> simp[] >> strip_tac >- simp[] >>
  rename1 `R1 a b` >> rename1 `Step t v` >>
  `b IN V1` by metis_tac[] >>
  disj2_tac >> qexistsl [`d b`, `v`] >> simp[Abbr `E`] >> metis_tac[]
QED

Resume open_fragment_splice[right_step]:
  rename1 `K' (I2 a) t` >>
  qpat_x_assum `!x t. (x IN V2 /\ x NOTIN X2) /\ _ ==> _`
    (qspecl_then [`a`, `t`] mp_tac) >> simp[] >> strip_tac >- simp[] >>
  rename1 `R2 a b` >> rename1 `Step t v` >>
  `b IN V2` by metis_tac[] >>
  disj2_tac >> qexistsl [`D b`, `v`] >> simp[Abbr `E`] >> metis_tac[]
QED

Resume open_fragment_splice[reachable]:
  `!a b. R1 a b ==> E (d a) (d b)` by
    (rpt strip_tac >>
     `a <> z` by
       (qpat_assum `!x y. R1 x y ==> _`
         (qspecl_then [`a`,`b`] mp_tac) >> simp[]) >>
     `d a = L a` by simp[Abbr `d`] >>
     simp[Abbr `E`] >> disj1_tac >> qexistsl [`a`,`b`] >> simp[]) >>
  `!a b. R2 a b ==> E (D a) (D b)` by
    (rpt strip_tac >> simp[Abbr `E`] >>
     disj2_tac >> qexistsl [`a`,`b`] >> simp[]) >>
  `!x. x IN V1 ==> Reach E e (d x)` by
    (rpt strip_tac >>
     qpat_x_assum `!x. x IN V1 ==> FST x = f /\ Reach R1 e1 x`
       (qspec_then `x` mp_tac) >> simp[Abbr `Reach`] >>
     strip_tac >> rename1 `left n = x` >>
     qexistsl [`n`, `\k. d (left k)`] >> simp[Abbr `e`]) >>
  `Reach E e (D e2)` by
    (`d z = D e2` by simp[Abbr `d`] >>
     qpat_x_assum `!x. x IN V1 ==> Reach E e (d x)`
       (qspec_then `z` mp_tac) >> simp[]) >>
  `!x. x IN V2 ==> Reach E e (D x)` by
    (rpt strip_tac >>
     qpat_x_assum `!x. x IN V2 ==> FST x = f /\ Reach R2 e2 x`
       (qspec_then `x` mp_tac) >> simp[] >>
     qpat_x_assum `Reach E e (D e2)` mp_tac >> simp[Abbr `Reach`] >>
     strip_tac >> rename1 `left m = D e2` >>
     strip_tac >> rename1 `right n = x` >>
     qabbrev_tac `h = \k. if k<m then left k else D (right (k-m))` >>
     `!k. k<=m ==> h k=left k` by
       (rpt strip_tac >> Cases_on `k=m` >> simp[Abbr `h`]) >>
     qexistsl [`m+n`, `h`] >>
     conj_tac >- simp[] >>
     conj_tac >- simp[Abbr `h`] >>
     rpt strip_tac >> Cases_on `k<m`
     >- (`SUC k<=m` by simp[] >> simp[]) >>
     `~(SUC k<m)` by simp[] >>
     `SUC k-m=SUC(k-m)` by simp[] >>
     `k-m<n` by simp[] >> simp[Abbr `h`]) >>
  simp[Abbr `U`, IN_IMAGE] >> rpt strip_tac >> gvs[]
  >- simp[Abbr `L`]
  >- (rename1 `Reach E e (L a)` >> `d a = L a` by simp[Abbr `d`] >>
      qpat_x_assum `!x. x IN V1 ==> Reach E e (d x)`
        (qspec_then `a` mp_tac) >> simp[]) >>
  simp[Abbr `D`]
QED

Finalise open_fragment_splice

(* Pointwise masked byte agreement and modular pointer displacement.
 * Neither relation claims reachability or a global memory translation.
 *)
Theory lowerDloadRelocation
Ancestors
  ptrDiscipline words pred_set arithmetic list

Definition ld_byte_rel_def:
  ld_byte_rel (R:num -> num -> bool) (Ts:num set) (Tt:num set)
              (ms:num -> 'a) mt <=>
    !a b. R a b ==>
      (b IN Tt ==> a IN Ts) /\ (a NOTIN Ts ==> ms a = mt b)
End

Definition ld_ptr_rel_def:
  ld_ptr_rel bs bt (x:bytes32) y <=> y = x + n2w bt - n2w bs
End

Theorem ld_byte_rel_identity:
  ld_byte_rel ($=) Ts Ts m m
Proof
  simp[ld_byte_rel_def]
QED

Theorem ld_byte_rel_restrict:
  ld_byte_rel R Ts Tt ms mt /\ (!a b. R' a b ==> R a b) ==>
  ld_byte_rel R' Ts Tt ms mt
Proof
  simp[ld_byte_rel_def] >> metis_tac[]
QED

Theorem ld_byte_rel_taint:
  ld_byte_rel R Ts Tt ms mt /\ R a b /\ b IN Tt ==> a IN Ts
Proof
  simp[ld_byte_rel_def] >> metis_tac[]
QED

Theorem ld_byte_rel_read:
  ld_byte_rel R Ts Tt ms mt /\ R a b /\ a NOTIN Ts ==> ms a = mt b
Proof
  simp[ld_byte_rel_def] >> metis_tac[]
QED

(* Paired overwrite: written bytes may themselves carry a mask. *)
Theorem ld_byte_rel_overwrite:
  ld_byte_rel R Ts Tt ms mt /\
  (!a b. R a b ==> (a IN Ws <=> b IN Wt)) /\
  (!a b. R a b /\ a IN Ws ==>
     (b IN Ut ==> a IN Us) /\ (a NOTIN Us ==> ds a = dt b)) ==>
  ld_byte_rel R ((Ts DIFF Ws) UNION (Us INTER Ws))
                ((Tt DIFF Wt) UNION (Ut INTER Wt))
    (\a. if a IN Ws then ds a else ms a)
    (\b. if b IN Wt then dt b else mt b)
Proof
  simp[ld_byte_rel_def] >> rpt strip_tac >>
  Cases_on `a IN Ws` >> gvs[] >> metis_tac[]
QED

Theorem ld_byte_rel_clean_overwrite:
  ld_byte_rel R Ts Tt ms mt /\
  (!a b. R a b ==> (a IN Ws <=> b IN Wt)) /\
  (!a b. R a b /\ a IN Ws ==> ds a = dt b) ==>
  ld_byte_rel R (Ts DIFF Ws) (Tt DIFF Wt)
    (\a. if a IN Ws then ds a else ms a)
    (\b. if b IN Wt then dt b else mt b)
Proof
  strip_tac >>
  mp_tac (Q.INST [`Us` |-> `{}`, `Ut` |-> `{}`] ld_byte_rel_overwrite) >>
  simp[] >> disch_then irule >> simp[]
QED

Theorem ld_byte_rel_range_read:
  ld_byte_rel R Ts Tt ms mt /\
  (!i. i < n ==> R (a+i) (b+i)) ==>
  !i. i < n ==>
    ((b+i IN Tt ==> a+i IN Ts) /\
     (a+i NOTIN Ts ==> ms (a+i) = mt (b+i)))
Proof
  simp[ld_byte_rel_def] >> metis_tac[]
QED

Theorem ld_ptr_rel_identity:
  ld_ptr_rel b b x x
Proof
  pure_rewrite_tac[ld_ptr_rel_def] >>
  qabbrev_tac `bbword = (n2w b:bytes32)` >>
  CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem ld_ptr_rel_add:
  ld_ptr_rel bs bt x y ==> ld_ptr_rel bs bt (x+k) (y+k)
Proof
  pure_rewrite_tac[ld_ptr_rel_def] >>
  qabbrev_tac `src = (n2w bs:bytes32)` >>
  qabbrev_tac `tgt = (n2w bt:bytes32)` >>
  CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem ld_ptr_rel_sub:
  ld_ptr_rel bs bt x y ==> ld_ptr_rel bs bt (x-k) (y-k)
Proof
  pure_rewrite_tac[ld_ptr_rel_def] >>
  qabbrev_tac `src = (n2w bs:bytes32)` >>
  qabbrev_tac `tgt = (n2w bt:bytes32)` >>
  CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem ld_ptr_rel_offset:
  ld_ptr_rel bs bt (n2w (bs+d)) y ==> y = n2w (bt+d)
Proof
  pure_rewrite_tac[ld_ptr_rel_def, GSYM word_add_n2w] >>
  qabbrev_tac `sbword = (n2w bs:bytes32)` >>
  qabbrev_tac `tbword = (n2w bt:bytes32)` >>
  qabbrev_tac `dword = (n2w d:bytes32)` >>
  CONV_TAC wordsLib.WORD_ARITH_CONV
QED

Theorem ld_ptr_rel_endpoint:
  ld_ptr_rel bs bt x y /\
  bs <= w2n x /\ w2n x <= bs+sz /\
  bs+sz < dimword(:256) /\ bt+sz < dimword(:256) ==>
  w2n y = bt + (w2n x-bs)
Proof
  strip_tac >>
  `bs + (w2n x - bs) = w2n x` by decide_tac >>
  `ld_ptr_rel bs bt (n2w (bs + (w2n x-bs))) y` by simp[] >>
  drule ld_ptr_rel_offset >> disch_then SUBST1_TAC >>
  `bt + (w2n x-bs) < dimword(:256)` by decide_tac >>
  simp[w2n_n2w]
QED

Theorem ld_ptr_rel_compare:
  ld_ptr_rel bs bt x x' /\ ld_ptr_rel bs bt y y' /\
  bs <= w2n x /\ w2n x <= bs+sz /\
  bs <= w2n y /\ w2n y <= bs+sz /\
  bs+sz < dimword(:256) /\ bt+sz < dimword(:256) ==>
  ((x <+ y <=> x' <+ y') /\
   (y <+ x <=> y' <+ x') /\ (x = y <=> x' = y'))
Proof
  strip_tac >>
  `w2n x' = bt + (w2n x-bs)` by metis_tac[ld_ptr_rel_endpoint] >>
  `w2n y' = bt + (w2n y-bs)` by metis_tac[ld_ptr_rel_endpoint] >>
  once_rewrite_tac[GSYM w2n_11] >>
  simp[WORD_LO, Excl "w2n_11"] >> decide_tac
QED

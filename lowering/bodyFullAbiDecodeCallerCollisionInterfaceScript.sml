Theory bodyFullAbiDecodeCallerCollisionInterface

Theorem abi_decode_caller_collision_selected:
  !K Aentry N J S B D.
    ((Aentry /\ K ==>
        ?r0 Gs ts r Gf tnf. J r0 Gs ts r Gf tnf /\ S r) /\
     (!r. B r /\ (~K ==> N) /\ (K ==> S r) ==> D r) /\
     Aentry /\ K) ==>
    ?r0 Gs ts r Gf tnf.
      J r0 Gs ts r Gf tnf /\ S r /\ (B r ==> D r)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ ==> (?x. _)` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `J r0 Gs ts r Gf tnf` >>
  qexistsl [`r0`, `Gs`, `ts`, `r`, `Gf`, `tnf`] >>
  simp[] >>
  qpat_x_assum `!res. _ ==> D res` (qspec_then `r` mp_tac) >>
  simp[]
QED

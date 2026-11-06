(* Correlated owned coverage with saved-tail reference locality. *)
structure lowerDloadOwnedTransitionPackageLib =
struct
open HolKernel boolLib bossLib
open lowerDloadSafetyRelationTheory lowerDloadSafetyAmbientTheory
val ld_owned = ``\lo P C C' vs0 Sigma names fn' ti t.
  ?stk PG G tn fn inst s t0 A frames N X p h.
    ld_sync lo P C vs0 stk PG G tn fn inst s t0 A frames N /\
    ld_global lo A frames /\
    EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
    (!j k. j < k /\ k < LENGTH frames ==>
      list_precedes (EL j frames).lf_fn.fn_name
                    (EL k frames).lf_fn.fn_name names) /\
    fn' = ld_image (HD frames) /\
    ld_envelope (HD frames).lf_supply fn s s.vs_inst_idx X p /\
    ld_prefix C' fn' X p h t0 t /\ ti = EL h X /\
    EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
      j IN P f.lf_fn.fn_name) frames /\
    (!g. MEM g (TL frames) ==>
      FRANGE g.lf_H SUBSET ld_slots A (TL frames) /\
      (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A (TL frames)))``;
end

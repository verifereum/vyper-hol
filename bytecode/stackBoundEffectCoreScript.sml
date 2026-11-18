(* Projection kernel for ordinary stack-effect proofs.
   Neutral computations preserve these fields even when they fail. *)
Theory stackBoundEffectCore
Ancestors
  stackBoundInterface vfmExecution vfmState vfmContext vfmConstants
  list pair arithmetic

Definition sb_eff_frame_def:
  sb_eff_frame s t <=>
    s.contexts <> [] /\ t.contexts <> [] /\
    LENGTH t.contexts = LENGTH s.contexts /\
    (FST (HD t.contexts)).msgParams = (FST (HD s.contexts)).msgParams /\
    (FST (HD t.contexts)).pc = (FST (HD s.contexts)).pc /\
    (FST (HD t.contexts)).jumpDest = (FST (HD s.contexts)).jumpDest
End

Definition sb_eff_neutral_def:
  sb_eff_neutral (m : 'a execution) <=>
    !s r t. s.contexts <> [] /\ m s = (r,t) ==>
      sb_eff_frame s t /\
      (FST (HD t.contexts)).stack = (FST (HD s.contexts)).stack /\
      r <> INR (SOME StackOverflow)
End

Definition sb_eff_raw_def:
  sb_eff_raw pops pushes (m : unit execution) <=>
    !s r t. s.contexts <> [] /\ m s = (r,t) ==>
      sb_eff_frame s t /\
      (r = INL () ==>
        pops <= LENGTH (FST (HD s.contexts)).stack /\
        ?vs. LENGTH vs = pushes /\
          (FST (HD t.contexts)).stack =
            vs ++ DROP pops (FST (HD s.contexts)).stack) /\
      (r = INR (SOME StackOverflow) ==>
        pops <= LENGTH (FST (HD s.contexts)).stack /\
        stack_limit < pushes + (LENGTH (FST (HD s.contexts)).stack - pops))
End

Theorem sb_eff_frame_refl:
  s.contexts <> [] ==> sb_eff_frame s s
Proof
  simp[sb_eff_frame_def]
QED

Theorem sb_eff_frame_trans:
  sb_eff_frame s u /\ sb_eff_frame u t ==> sb_eff_frame s t
Proof
  simp[sb_eff_frame_def]
QED

Theorem sb_eff_neutral_return[simp]:
  sb_eff_neutral (return x)
Proof
  simp[sb_eff_neutral_def, return_def, sb_eff_frame_refl]
QED

Theorem sb_eff_neutral_fail[simp]:
  e <> StackOverflow ==> sb_eff_neutral (fail e)
Proof
  simp[sb_eff_neutral_def, fail_def, sb_eff_frame_refl]
QED

Theorem sb_eff_neutral_assert[simp]:
  e <> StackOverflow ==> sb_eff_neutral (assert b e)
Proof
  Cases_on `b` >> simp[sb_eff_neutral_def, assert_def, sb_eff_frame_refl]
QED

Theorem sb_eff_neutral_bind:
  sb_eff_neutral g /\ (!x. sb_eff_neutral (f x)) ==>
  sb_eff_neutral (bind g f)
Proof
  rw[sb_eff_neutral_def, bind_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[sb_eff_frame_trans, sb_eff_frame_def]
QED

Theorem sb_eff_neutral_ignore_bind:
  sb_eff_neutral g /\ sb_eff_neutral f ==>
  sb_eff_neutral (ignore_bind g f)
Proof
  simp[ignore_bind_def, sb_eff_neutral_bind]
QED

(* Charging gas changes only gasUsed; the rejected charge is OutOfGas. *)
Theorem sb_eff_neutral_consume_gas[simp]:
  sb_eff_neutral (consume_gas n)
Proof
  rw[sb_eff_neutral_def, consume_gas_def, bind_def,
     ignore_bind_def, get_current_context_def, set_current_context_def,
     return_def, fail_def, assert_def] >>
  gvs[AllCaseEqs(), sb_eff_frame_def] >>
  Cases_on `s.contexts` >> gvs[]
QED

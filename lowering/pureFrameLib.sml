structure pureFrameLib =
struct
open HolKernel boolLib

(* Project P ==> ?xs. frame /\ result to P ==> ?xs. result. *)
fun drop_frame th =
  let
    val (witnesses, result) = strip_exists (rand (concl th))
    val project = DISCH result (CONJUNCT2 (ASSUME result))
    fun under_exists witness lemma =
      HO_MATCH_MP boolTheory.MONO_EXISTS (GEN witness lemma)
  in
    IMP_TRANS th (itlist under_exists witnesses project)
  end

end

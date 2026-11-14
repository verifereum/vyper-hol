structure asmCallViewLib =
struct
open HolKernel boolLib bossLib;

(* Legacy preparation consumers need the state/operand view, not the
   terminal four-witness gas block. Discard it before choosing witnesses:
   simplifying its exact charge equations would unfold implementation costs.
   The block is recognized by its call_gas equality, never witness names. *)
fun legacy_strip th =
  let
    val tm = concl th
    val (vs,body) = strip_exists tm
    val first = if is_conj body then fst (dest_conj body) else body
    val is_gas = is_eq first andalso
      is_const (fst (strip_comb (lhs first))) andalso
      #Name (dest_thy_const (fst (strip_comb (lhs first)))) = "call_gas"
  in
    if not (null vs) andalso is_gas then
      if length vs = 4 then ALL_TAC
      else FAIL_TAC "legacy call view: changed gas witness block"
    else if is_conj tm then CONJUNCTS_THEN legacy_strip th
    else if is_exists tm then CHOOSE_THEN legacy_strip th
    else STRIP_ASSUME_TAC th
  end;

fun asm_call_legacy_view th =
  legacy_strip (BETA_RULE (REWRITE_RULE [LET_THM] th));
end

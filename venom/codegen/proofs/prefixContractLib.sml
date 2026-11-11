(* Representation normalization for boundary simulation contracts.
 * No facts are exported: the supplied theorem is specialized, rewritten,
 * and consumed immediately by the caller's ordinary theorem tactic. *)
structure prefixContractLib =
struct
open HolKernel boolLib bossLib

fun prefix_contract_tac normalize apply substitutions facts contract =
  apply (GEN_ALL (normalize facts
    (Q.INST substitutions (SPEC_ALL contract))));

end

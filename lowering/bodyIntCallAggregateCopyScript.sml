Theory bodyIntCallAggregateCopy
Ancestors
  exprSimCopy exprSimStorageCopy venomState

(* copy_static hides only registers, memory and execution position.
   Contract observations therefore project from its exact equality. *)
Theorem copy_static_contract_storage:
  copy_static t = copy_static s ==>
  contract_storage t = contract_storage s
Proof
  strip_tac >>
  `contract_storage (copy_static t) = contract_storage (copy_static s)` by simp[] >>
  qpat_x_assum `copy_static _ = copy_static _` kall_tac >>
  gvs[copy_static_def, contract_storage_def]
QED

Theorem copy_static_contract_transient:
  copy_static t = copy_static s ==>
  contract_transient t = contract_transient s
Proof
  strip_tac >>
  `contract_transient (copy_static t) = contract_transient (copy_static s)` by simp[] >>
  qpat_x_assum `copy_static _ = copy_static _` kall_tac >>
  gvs[copy_static_def, contract_transient_def]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in
    if null axioms andalso null (Thm.hyp th) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail "Copy observations have unproved dependencies"
  end) [copy_static_contract_storage, copy_static_contract_transient];

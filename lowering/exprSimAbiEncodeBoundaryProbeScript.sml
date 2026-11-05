(* Checked interfaces for relabeled ABI-encoder execution. *)
Theory exprSimAbiEncodeBoundaryProbe
Ancestors
  exprSimAbiEncodeRegistration

Theorem abi_encode_relabel_registered_room:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) ==>
  alloca_room (ctx with ctx_functions := [obs]) obs s
Proof
  strip_tac >> irule abi_encode_registered_alloca_room >>
  simp[] >> qexists_tac `func` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

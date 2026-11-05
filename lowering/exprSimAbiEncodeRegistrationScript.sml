(* Global registration permits retained calls; execution safety stays regional. *)
Theory exprSimAbiEncodeRegistration
Ancestors
  exprSimAbiEncodeCompatibility exprSimAbiEncodeResources
  exprLoweringProps fcgDefs venomInst venomExecSemantics relation pred_set list rich_list

Theorem abi_encode_singleton_edge:
  fn_directly_calls (ctx with ctx_functions := [obs]) a b <=>
  a = obs.fn_name /\
  ?i rest. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE /\
           i.inst_operands = Label b :: rest
Proof
  simp[fn_directly_calls_def, lookup_function_def, FIND_thm, AllCaseEqs()]
  >> metis_tac[]
QED

Theorem abi_encode_observer_edge_original:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) /\
  fn_directly_calls (ctx with ctx_functions := [obs]) a b ==>
  fn_directly_calls ctx a b
Proof
  simp[abi_encode_singleton_edge, alloca_room_def,
       fn_directly_calls_def] >> metis_tac[]
QED

Theorem abi_encode_original_no_self:
  alloca_room ctx func s ==> ~fn_directly_calls ctx func.fn_name func.fn_name
Proof
  rw[alloca_room_def] >> metis_tac[TC_SUBSET]
QED

Theorem abi_encode_single_source_tc[local]:
  (!a b. R a b ==> a = n /\ b <> n) ==>
  !a b. TC R a b <=> R a b
Proof
  strip_tac >> `!a b. TC R a b ==> R a b` by
    (ho_match_mp_tac TC_INDUCT >> metis_tac[])
  >> metis_tac[TC_SUBSET]
QED

Theorem abi_encode_observer_tc:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) ==>
  !a b. TC (fn_directly_calls (ctx with ctx_functions := [obs])) a b <=>
        fn_directly_calls (ctx with ctx_functions := [obs]) a b
Proof
  strip_tac >> irule abi_encode_single_source_tc
  >> qexists_tac `obs.fn_name` >> rpt strip_tac
  >- gvs[abi_encode_singleton_edge]
  >> drule_all abi_encode_observer_edge_original
  >> metis_tac[abi_encode_original_no_self, abi_encode_singleton_edge]
QED

Theorem abi_encode_observer_reach_subset:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) ==>
  {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g}
  SUBSET {g | TC (fn_directly_calls ctx) func.fn_name g}
Proof
  strip_tac >> drule_all abi_encode_observer_tc >> strip_tac
  >> simp[SUBSET_DEF] >> rpt strip_tac
  >> drule_all abi_encode_observer_edge_original
  >> metis_tac[TC_SUBSET]
QED

Theorem abi_encode_observer_reach_finite:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) ==>
  FINITE {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g}
Proof
  strip_tac >> drule_all abi_encode_observer_reach_subset
  >> fs[alloca_room_def] >> metis_tac[SUBSET_FINITE]
QED

Theorem abi_encode_observer_reach_card:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) ==>
  CARD {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g} <=
  CARD {g | TC (fn_directly_calls ctx) func.fn_name g}
Proof
  strip_tac >> drule_all abi_encode_observer_reach_subset
  >> fs[alloca_room_def] >> metis_tac[CARD_SUBSET]
QED

Theorem abi_encode_observer_reach_acyclic:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
       MEM i (fn_insts func)) ==>
  !g. TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g ==>
      ~TC (fn_directly_calls (ctx with ctx_functions := [obs])) g g
Proof
  strip_tac >> drule_all abi_encode_observer_tc >> strip_tac
  >> simp[] >> rpt strip_tac
  >> drule_all abi_encode_observer_edge_original
  >> metis_tac[abi_encode_original_no_self, abi_encode_singleton_edge]
QED

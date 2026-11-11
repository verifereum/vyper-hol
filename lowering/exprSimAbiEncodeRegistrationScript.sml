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

Theorem abi_encode_observer_unit_credit:
  MEM func ctx.ctx_functions /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  unit_alloca_frame (ctx with ctx_functions := [obs]) <= unit_alloca_frame ctx
Proof
  strip_tac >> simp[unit_alloca_frame_def]
  >> irule abi_encode_weighted_subset >> simp[MEM_FILTER, MEM_FLAT, MEM_MAP]
  >> metis_tac[]
QED

Theorem abi_encode_observer_total_charge:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\
       (i.inst_opcode = ALLOCA \/ i.inst_opcode = INVOKE) ==>
       MEM i (fn_insts func)) ==>
  s.vs_alloca_next + pending_alloca_size obs s +
    CARD {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g} *
      unit_alloca_frame (ctx with ctx_functions := [obs]) <=
  s.vs_alloca_next + pending_alloca_size func s +
    CARD {g | TC (fn_directly_calls ctx) func.fn_name g} * unit_alloca_frame ctx
Proof
  strip_tac
  >> `pending_alloca_size obs s <= pending_alloca_size func s` by
       (irule abi_encode_pending_credit >> metis_tac[])
  >> `unit_alloca_frame (ctx with ctx_functions := [obs]) <= unit_alloca_frame ctx` by
       (irule abi_encode_observer_unit_credit >> simp[]
        >> qexists_tac `func` >> gvs[alloca_room_def]
        >> metis_tac[lookup_function_MEM])
  >> `CARD {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g} <=
      CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` by
       (irule abi_encode_observer_reach_card >> metis_tac[])
  >> `CARD {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g} *
        unit_alloca_frame (ctx with ctx_functions := [obs]) <=
      CARD {g | TC (fn_directly_calls ctx) func.fn_name g} * unit_alloca_frame ctx` by
       (irule arithmeticTheory.LESS_MONO_MULT2 >> simp[])
  >> gvs[]
QED

Theorem abi_encode_registered_alloca_room:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\
       (i.inst_opcode = ALLOCA \/ i.inst_opcode = INVOKE) ==>
       MEM i (fn_insts func)) ==>
  alloca_room (ctx with ctx_functions := [obs]) obs s
Proof
  strip_tac
  >> `FINITE {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g}` by
       (irule abi_encode_observer_reach_finite >> qexistsl_tac [`func`, `s`] >> metis_tac[])
  >> `!g. TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g ==>
          ~TC (fn_directly_calls (ctx with ctx_functions := [obs])) g g` by
       (`!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
             MEM i (fn_insts func)` by metis_tac[]
        >> metis_tac[abi_encode_observer_reach_acyclic])
  >> drule_all abi_encode_observer_total_charge
  >> gvs[alloca_room_def, lookup_function_def, FIND_thm]
QED

Theorem abi_encode_singleton_fmp_trigger:
  (!a b. TC (fn_directly_calls (ctx with ctx_functions := [obs])) a b <=>
          fn_directly_calls (ctx with ctx_functions := [obs]) a b) /\
  ~fn_directly_calls (ctx with ctx_functions := [obs]) obs.fn_name obs.fn_name ==>
  ~(?g f. TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g /\
          MEM f [obs] /\ f.fn_name = g /\
          EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts f))
Proof
  simp[] >> metis_tac[]
QED

Theorem abi_encode_registered_fmp_room:
  obs.fn_name = func.fn_name /\ alloca_room ctx func s /\ fmp_room ctx func s /\
  ALL_DISTINCT (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts obs)) /\
  (!i. MEM i (fn_insts obs) /\
       (i.inst_opcode = ALLOCA \/ i.inst_opcode = INVOKE \/ i.inst_opcode = DALLOCA) ==>
       MEM i (fn_insts func)) ==>
  fmp_room (ctx with ctx_functions := [obs]) obs s
Proof
  strip_tac
  >> `!a b. TC (fn_directly_calls (ctx with ctx_functions := [obs])) a b <=>
            fn_directly_calls (ctx with ctx_functions := [obs]) a b` by
       (irule abi_encode_observer_tc >> qexistsl_tac [`func`, `s`] >> metis_tac[])
  >> `~fn_directly_calls (ctx with ctx_functions := [obs]) obs.fn_name obs.fn_name` by
       (strip_tac
        >> `!i. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
                MEM i (fn_insts func)` by metis_tac[]
        >> drule_all abi_encode_observer_edge_original
        >> metis_tac[abi_encode_original_no_self])
  >> drule_all abi_encode_singleton_fmp_trigger >> strip_tac
  >> `s.vs_alloca_next + pending_alloca_size obs s +
        CARD {g | TC (fn_directly_calls (ctx with ctx_functions := [obs])) obs.fn_name g} *
          unit_alloca_frame (ctx with ctx_functions := [obs]) <=
      s.vs_alloca_next + pending_alloca_size func s +
        CARD {g | TC (fn_directly_calls ctx) func.fn_name g} * unit_alloca_frame ctx` by
       (irule abi_encode_observer_total_charge >> metis_tac[])
  >> gvs[fmp_room_def, EXISTS_MEM] >> strip_tac
  >> `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = DALLOCA` by
       metis_tac[]
  >> qpat_x_assum `_ \/ _ ==> _` mp_tac
  >> (impl_tac >- (disj1_tac >> metis_tac[]))
  >> strip_tac >> gvs[]
QED

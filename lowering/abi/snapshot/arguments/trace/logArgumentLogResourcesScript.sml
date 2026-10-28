(* TOP-LEVEL: the argument evaluator's reservation supplies the two actual
   Log buffers and the encoder's word-sized scratch allocations. *)
Theory logArgumentLogResources
Ancestors
  logArgumentListContract abiRequestCredit abiRequestProfile abiAllocationTrace abiAllocationBudget
  memoryValueSnapshot compileEnv venomState list pair pred_set words arithmetic

Theorem log_ready_suffix_resources:
  !env cx cenv func ids reserved requests final_cut cs es ss credit args tvs values
    data_id data_capacity output_id capacity scratch_ids.
    log_prefix_ready env cx cenv func ids reserved requests final_cut [] cs es ss credit args tvs values /\
    32 <= reserved /\ data_capacity + capacity <= reserved /\
    MEM (data_id,data_capacity) requests /\ MEM (output_id,capacity) requests /\
    (!id. MEM id scratch_ids ==> MEM (id,32) requests) ==>
    abi_alloca_request_ok data_id data_capacity ss /\
    abi_alloca_request_ok output_id capacity ss /\
    (!id. MEM id scratch_ids ==> abi_alloca_request_ok id 32 ss) /\
    abi_alloca_budget 32 scratch_ids ss + data_capacity + capacity < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_request_credit reserved requests credit ss` by fs[log_prefix_ready_def] >>
  `abi_request_reservation reserved requests ss` by (drule_all abi_request_credit_reservation >> simp[]) >>
  `abi_requests_compatible requests ss` by fs[abi_request_reservation_def] >>
  `abi_alloca_request_ok data_id data_capacity ss` by
    (qspecl_then [`requests`, `ss`, `data_id`, `data_capacity`] mp_tac abi_requests_compatible_member >> simp[]) >>
  `abi_alloca_request_ok output_id capacity ss` by
    (qspecl_then [`requests`, `ss`, `output_id`, `capacity`] mp_tac abi_requests_compatible_member >> simp[]) >>
  `!id. MEM id scratch_ids ==> abi_alloca_request_ok id 32 ss` by
    (qx_gen_tac `id` >> DISCH_TAC >>
     `MEM (id,32) requests` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
     qspecl_then [`requests`, `ss`, `id`, `32`] mp_tac abi_requests_compatible_member >> simp[]) >>
  `set scratch_ids SUBSET set (MAP FST requests)` by
    (simp_tac (srw_ss()) [SUBSET_DEF] >> qx_gen_tac `id` >> DISCH_TAC >>
     `MEM (id,32) requests` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
     simp[MEM_MAP] >> qexists_tac `(id,32)` >> simp[]) >>
  `abi_alloca_budget 32 scratch_ids ss <= abi_alloca_budget 32 (MAP FST requests) ss` by
    (irule abi_alloca_budget_subprofile >> first_assum MATCH_ACCEPT_TAC) >>
  `32 * CARD (abi_alloca_pending (MAP FST requests) ss) <=
    reserved * CARD (abi_alloca_pending (MAP FST requests) ss)` by
    (qspecl_then [`32`, `reserved`, `CARD (abi_alloca_pending (MAP FST requests) ss)`]
       mp_tac LESS_MONO_MULT >> simp[]) >>
  `abi_alloca_budget 32 (MAP FST requests) ss <= abi_alloca_budget reserved (MAP FST requests) ss` by
    (simp_tac bool_ss [abi_alloca_budget_def] >> decide_tac) >>
  `abi_alloca_budget reserved (MAP FST requests) ss + reserved < dimword(:256)` by
    fs[abi_request_reservation_def] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed Log suffix resources from argument reservation: " ^ name)
  end) (DB.thms "logArgumentLogResources")

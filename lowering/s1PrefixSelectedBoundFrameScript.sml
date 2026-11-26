Theory s1PrefixSelectedBoundFrame
Ancestors
  s1PrefixBoundDefaultFrame s1PrefixSelectedDefaultGuards

Theorem selected_bound_request_frame:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  external_entry_bound tops am tx os gs mut args dflts es ==>
  es.requests = [] /\ es.storage_trace = []
Proof
  strip_tac >>
  drule_all selected_omitted_default_guards >> strip_tac >>
  irule guarded_external_entry_request_frame >>
  simp[] >> metis_tac[]
QED

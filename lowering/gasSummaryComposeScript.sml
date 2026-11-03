(* Sequential source evaluation concatenates explicit-event markings,
   while target paths account for every generated and explicit read. *)
Theory gasSummaryCompose
Ancestors
  gasSummary fragGasPath gasCount vyperState vyperInterpreter list rich_list

Theorem gas_summary_bind:
  gas_summary (ctx, func) source (es, s0)
    (\res es_mid t.
       ?v. res = INL v /\
           gas_summary (ctx, func) (next v) (es_mid, t) Q R)
    (\res es_end r. ?exc. res = INR exc /\ R (INR exc) es_end r) ==>
  gas_summary (ctx, func) (bind source next) (es, s0) Q R
Proof
  cheat
QED

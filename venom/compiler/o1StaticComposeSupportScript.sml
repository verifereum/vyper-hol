(* One input witness carries both fuel simulation and abort requests. *)
Theory o1StaticComposeSupport
Ancestors
  o1PassContract o1RequestContract

Theorem guarded_ctx_sim_abort_rq_trans:
  dead_wf D /\
  (!a b. gas_variant a b /\ P b ==> P a) /\
  (!b. P b ==>
    ?a. gas_variant a b /\
      (Inv A a ==> ctx_sim_fuel f D A B a b /\
        ctx_abort_rq D A B a b /\ Mid B b)) /\
  (!c. P c ==>
    ?b. gas_variant b c /\
      (Mid B b ==> ctx_sim_fuel g D B C b c /\
        ctx_abort_rq D B C b c /\ Post C c)) /\
  P c ==>
  ?a. gas_variant a c /\
    (Inv A a ==> ctx_sim_fuel (g o f) D A C a c /\
      ctx_abort_rq D A C a c /\ Post C c)
Proof
  strip_tac >>
  qpat_x_assum `!c. P c ==> _` (qspec_then `c` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `middle` strip_assume_tac) >>
  `P middle` by metis_tac[] >>
  qpat_x_assum `!b. P b ==> _` (qspec_then `middle` mp_tac) >>
  simp[] >> disch_then (qx_choose_then `input` strip_assume_tac) >>
  qexists_tac `input` >> conj_tac
  >- metis_tac[gas_variant_trans] >>
  strip_tac >>
  `ctx_sim_fuel f D A B input middle /\
   ctx_abort_rq D A B input middle /\ Mid B middle` by metis_tac[] >>
  `ctx_sim_fuel g D B C middle c /\
   ctx_abort_rq D B C middle c /\ Post C c` by metis_tac[] >>
  metis_tac[ctx_sim_fuel_trans, ctx_abort_rq_trans]
QED

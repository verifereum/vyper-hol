(* Fixed code/data references survive backward gas-oracle choice.
 * Conjoined stage contracts compose directly with
 * o1PipelineComposeTheory.guarded_ctx_sim_trans: instantiate Inv, Mid,
 * Post with conjunctions, retaining the same reference parameter in each.
 * The wrapper below only specializes that existing composition rule. *)
Theory o1CodeEndComposeBoundary
Ancestors
  o1PipelineCompose o1PassContract venomState

Theorem gas_variant_code_data:
  gas_variant s t ==>
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section
Proof
  strip_tac >> fs[gas_variant_def] >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[]
QED

(* The reference v is chosen outside both contracts, not reconstructed
 * independently at each stage. All three rows travel with their extra facts. *)
Theorem code_end_guarded_ctx_sim_trans:
  dead_wf D /\
  (!b. o1_run_state_ok b ==>
    ?a. gas_variant a b /\
      (Inv0 A a /\ P v A a ==>
       ctx_sim D A B a b /\ Mid0 B b /\ Q v B b)) /\
  (!c. o1_run_state_ok c ==>
    ?b. gas_variant b c /\
      (Mid0 B b /\ Q v B b ==>
       ctx_sim D B C b c /\ Post0 C c /\ R v C c)) /\
  o1_run_state_ok c ==>
  ?a. gas_variant a c /\
    (Inv0 A a /\ P v A a ==>
     ctx_sim D A C a c /\ Post0 C c /\ R v C c)
Proof
  MATCH_ACCEPT_TAC (BETA_RULE (Q.INST
    [`Inv` |-> `\ctx s. Inv0 ctx s /\ P v ctx s`,
     `Mid` |-> `\ctx s. Mid0 ctx s /\ Q v ctx s`,
     `Post` |-> `\ctx s. Post0 ctx s /\ R v ctx s`]
    guarded_ctx_sim_trans))
QED

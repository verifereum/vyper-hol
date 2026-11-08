(* State-to-state continuation transfer, including memory safety.
   This does not assert termination or unconditional memory safety. *)
Theory memContinuation
Ancestors
  fragExecMem fragExec memSafeRun arithmetic

Definition mem_cont_sim_def:
  mem_cont_sim ctx fn s t <=>
    !fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
End

Theorem mem_cont_sim_refl:
  mem_cont_sim ctx fn s s
Proof
  simp[mem_cont_sim_def] >> metis_tac[]
QED

Theorem mem_cont_sim_trans:
  mem_cont_sim ctx fn s t /\ mem_cont_sim ctx fn t u ==>
  mem_cont_sim ctx fn s u
Proof
  rw[mem_cont_sim_def] >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem mem_cont_sim_from_fragment:
  frag_exec_mem ctx st st' P Q (K F) /\ fn_has_code st st' fn /\ P s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ mem_cont_sim ctx fn s t
Proof
  simp[frag_exec_mem_def, mem_cont_sim_def] >> metis_tac[]
QED

Theorem mem_cont_sim_finite_iteration:
  !(bound:num) i loop_inv Q ctx fn s.
  i <= bound /\ loop_inv i s /\
  (!j u. loop_inv j u /\ j < bound ==>
    ?v. loop_inv (SUC j) v /\ mem_cont_sim ctx fn u v) /\
  (!u. loop_inv bound u ==> ?v. Q v /\ mem_cont_sim ctx fn u v) ==>
  ?t. Q t /\ mem_cont_sim ctx fn s t
Proof
  completeInduct_on `(bound:num) - i` >> rpt strip_tac >>
  Cases_on `i = bound` >- metis_tac[] >>
  `i < bound` by decide_tac >>
  `?v. loop_inv (SUC i) v /\ mem_cont_sim ctx fn s v` by metis_tac[] >>
  rename1 `loop_inv (SUC i) next` >>
  `?t. Q t /\ mem_cont_sim ctx fn next t` by
    (qpat_x_assum `!m. m < _ ==> _` (qspec_then `bound - SUC i` mp_tac) >>
     (impl_tac >- decide_tac) >>
     disch_then (qspecl_then [`bound`, `SUC i`] mp_tac) >>
     simp[] >> disch_then irule >> simp[] >>
     qexists_tac `loop_inv` >> simp[]) >>
  metis_tac[mem_cont_sim_trans]
QED

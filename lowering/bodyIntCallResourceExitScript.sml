(* A protected terminal witness suffices to attach resources to the counted
   semantic outcome. Normal landing witnesses are never identified. *)
Theory bodyIntCallResourceExit
Ancestors
  bodyIntCallNormalResource bodyIntCallProtectedReturn bodyIntCallOutcomeFrame
  bodyIntCallProducerOrder fragGasPath fragExec arithmetic

Theorem counted_exit_unique:
  gas_path ctx func s n r /\ exit_result r /\
  gas_path ctx func s m q /\ exit_result q ==> r = q
Proof
  strip_tac >>
  `?i. run_from i ctx func s = r` by metis_tac[gas_path_exit] >>
  `?j. run_from j ctx func s = q` by metis_tac[gas_path_exit] >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  `!e. q <> Error e` by metis_tac[exit_result_not_error] >>
  `run_from (MAX i j) ctx func s = r` by
    (irule gas_run_from_fuel_mono >> conj_tac >- simp[] >> qexists_tac `i` >> simp[]) >>
  `run_from (MAX i j) ctx func s = q` by
    (irule gas_run_from_fuel_mono >> conj_tac >- simp[] >> qexists_tac `j` >> simp[]) >>
  metis_tac[]
QED

Theorem gas_outcome_exit_witness_attach:
  gas_outcome F tops (ctx,func) source (es,s) Q R /\
  (?n r. gas_path ctx func s n r /\ exit_result r /\ H r) ==>
  gas_outcome F tops (ctx,func) source (es,s) Q
    (\res ee r. R res ee r /\ H r)
Proof
  strip_tac >> irule gas_outcome_exit_attach >> simp[] >>
  metis_tac[counted_exit_unique]
QED

(* Inv may include protected bytes and reserved operands relative to one
   fixed origin. The terminal producer must establish H at that origin. *)
Theorem normal_resource_exit_attach:
  gas_outcome F tops (ctx,func) source (es,s) Q R /\
  A s /\ Inv s /\
  (!v. A v /\ Inv v ==> ?n u.
    gas_path ctx func v n (OK u) /\ B u /\ Inv u /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts) /\
  (!u. B u /\ Inv u /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts ==> ?m v.
    gas_path ctx func u m (OK v) /\ C v /\ Inv v /\
    v.vs_current_bb = sb.cs_current_bb /\
    v.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  (!v. C v /\ Inv v /\ v.vs_current_bb = sb.cs_current_bb /\
       v.vs_inst_idx = LENGTH sb.cs_current_insts ==> ?k r.
    gas_path ctx func v k r /\ exit_result r /\ H r) ==>
  gas_outcome F tops (ctx,func) source (es,s) Q
    (\res ee r. R res ee r /\ H r)
Proof
  strip_tac >> drule_all normal_resource_sequence >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_exit_witness_attach >> simp[] >>
  qexistsl_tac [`k + k'`, `r`] >> simp[] >>
  irule gas_path_then >> qexists_tac `v` >> simp[] >>
  qexistsl_tac [`k`, `k'`] >> simp[]
QED

Theorem protected_memory_return_outcome_attach:
  compile_internal_return ce (SOME src) rpc 0 ty ty elems (SOME dst) sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  (!x. ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx (es with scopes := []) s /\
  expr_val_rel cx ty v src s /\ eval_operand dst s = SOME bw /\
  (?pc. eval_operand rpc s = SOME pc) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!b sz. P b sz ==> regions_disjoint b sz (w2n bw) (type_memory_size tv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  (!b sz. P b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz origin.vs_memory) /\
  (!op. reserved op ==> eval_operand op s = eval_operand op origin) /\
  gas_outcome F tops (ctx,func) source (ee,s) Q R ==>
  gas_outcome F tops (ctx,func) source (ee,s) Q
    (\res ee r. R res ee r /\ ?ir u. r = IntRet ir u /\
      (!b sz. P b sz ==>
        mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz origin.vs_memory) /\
      (!op. reserved op ==> eval_operand op u = eval_operand op origin) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >>
  `?n ir u. gas_path ctx func s n (IntRet ir u) /\
    intret_mem_q func ce cx tv bw v (es with scopes := []) (IntRet ir u) /\
    (!b sz. P b sz ==> mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (irule protected_internal_memory_return_counted >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac gas_outcome_exit_witness_attach >> simp[] >>
  qexistsl_tac [`n`, `IntRet ir u`] >> simp[exit_result_def] >>
  metis_tac[]
QED

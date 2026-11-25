(* The size query is a common prefix of the successful and reverting code slices. *)
Theory bodySliceCodeQueryLandingMods
Ancestors
  bodyFullBuiltinBytestringQuery bodyPtrBytestringBuiltinsExternalSlice
  emitHelperProps freshWrites venomState list

Theorem slice_code_query_landing_mods:
  emit_op query_op query_ops sa = (limit,sc) /\ fn_has_code sa sc func /\
  MEM query_op [CODESIZE;EXTCODESIZE] /\ LENGTH query_ops <= 1 /\
  (!arg. MEM arg query_ops ==> op_taint tn arg = {}) /\
  step_inst_base
    (mk_inst sa.cs_next_id query_op query_ops
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w cap) s) /\
  allocas_from lo s /\ alloca_inv s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand start s = SOME (n2w i) /\ eval_operand cnt s = SOME (n2w k) /\
  op_prov G start = NONE /\ op_prov G cnt = NONE /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) ==>
  ?zq Gq tq.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
          (OK zq,Gq,tq)) /\
    zq = s with <|vs_vars := zq.vs_vars; vs_inst_idx := LENGTH sc.cs_current_insts|> /\
    zq.vs_current_bb = sc.cs_current_bb /\
    zq.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~zq.vs_halted /\
    alloca_history func zq /\
    tq.t_mem = tn.t_mem /\ tq.t_stor = tn.t_stor /\
    tq.t_trans = tn.t_trans /\ tq.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
       lookup_var x zq = lookup_var x s /\ FLOOKUP Gq x = FLOOKUP G x /\
       op_taint tq (Var x) = op_taint tn (Var x)) /\
    sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op zq = eval_operand op s /\ op_prov Gq op = op_prov G op /\
      op_taint tq op = op_taint tn op) /\
    eval_operand start zq = SOME (n2w i) /\ eval_operand cnt zq = SOME (n2w k) /\
    eval_operand limit zq = SOME (n2w cap) /\
    (!op. MEM op [start;cnt;limit] ==>
       op_prov Gq op = NONE /\ op_taint tq op = {} /\
       (!x. op = Var x ==> not_fresh_at sc x))
Proof
  strip_tac >>
  `MEM query_op [CALLDATASIZE;CODESIZE;EXTCODESIZE]` by fs[MEM] >>
  drule_all bytestring_source_size_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`] mp_tac) >>
  disch_then (qx_choose_then `size_var` (qx_choose_then `zq`
    (qx_choose_then `Gq` (qx_choose_then `tq` strip_assume_tac)))) >>
  `zq.vs_labels = s.vs_labels` by simp[update_var_def] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op zq = eval_operand op s /\ op_prov Gq op = op_prov G op /\
    op_taint tq op = op_taint tn op` by
    (qpat_assum `zq.vs_labels = s.vs_labels` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zq = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[reserved_operand_ghost_frame]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`zq`,`Gq`,`tq`] >>
  `zq = s with <|vs_vars := zq.vs_vars; vs_inst_idx := LENGTH sc.cs_current_insts|>` by
    simp[update_var_def] >>
  `eval_operand limit zq = SOME (n2w cap)` by
    simp[eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `eval_operand start zq = SOME (n2w i) /\ op_prov Gq start = NONE /\
   op_taint tq start = {} /\ eval_operand cnt zq = SOME (n2w k) /\
   op_prov Gq cnt = NONE /\ op_taint tq cnt = {}` by
    (qpat_assum `!op. _ ==> eval_operand op zq = _ /\ _`
       (fn th => map_every (fn tm => qspec_then tm mp_tac th) [`start`,`cnt`]) >>
     simp[]) >>
  simp[] >>
  rpt strip_tac >> gvs[]
QED

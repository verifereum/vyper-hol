(* Resource-preserving observers for counted return-decoder executions. *)
Theory extcallReturnCountedTransport
Ancestors
  extcallReturnObserverIds extcallReturnObserverRun extcallReturnObserver
  exprSimAbiGasBridge exprLoweringProps fragExec abiDecoderLoop compileEnv
  venomExecSemantics venomExecProps venomInst venomInstProps unitShapeDefs list rich_list
  arithmetic finite_map pred_set

Theorem return_observer_context_fmp_room_subset:
  fmp_room ctx func s /\
  pending_alloca_size obs s = pending_alloca_size func s /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = DALLOCA ==>
       MEM i (fn_insts func)) ==>
  fmp_room (return_observer_context ctx obs) obs s
Proof
  strip_tac >>
  `!a b. ~TC (fn_directly_calls (return_observer_context ctx obs)) a b` by
    metis_tac[return_observer_context_reachable] >>
  simp[fmp_room_def] >> strip_tac >>
  `EXISTS (\i. i.inst_opcode = DALLOCA) (fn_insts func)` by
    (fs[EXISTS_MEM] >> metis_tac[]) >>
  fs[fmp_room_def] >> decide_tac
QED

Theorem return_observer_ids_complete_run:
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                 MEM i (fn_insts func)) (fn_insts obs) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
  s.vs_current_bb <> keep /\ ~s.vs_halted ==>
  run_from fuel ctx'
    (return_observer_complete func (return_observer_ids func bound obs) keep) s =
  run_from fuel ctx obs s
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands)
    (fn_insts (return_observer_ids func bound obs))` by
    (fs[return_observer_ids_insts, EVERY_MEM, MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[return_observer_complete_run_from, return_observer_ids_run_from]
QED

Theorem return_observer_ids_complete_sim:
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
                 MEM i (fn_insts func)) (fn_insts obs) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands) (fn_insts obs) /\
  s.vs_current_bb <> keep /\ ~s.vs_halted /\
  t.vs_current_bb <> keep /\ ~t.vs_halted /\
  abi_decode_sim ctx'
    (return_observer_complete func (return_observer_ids func bound obs) keep) s t ==>
  abi_decode_sim ctx obs s t
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\
             ~MEM (Label keep) i.inst_operands)
    (fn_insts (return_observer_ids func bound obs))` by
    (fs[return_observer_ids_insts, EVERY_MEM, MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all return_observer_complete_sim >>
  simp[return_observer_ids_sim]
QED

(* Complete a relabeled observer while preserving both success and abort runs. *)
Theorem return_observer_relabel_completion:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) obs /\
  fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ~s.vs_halted /\ s.vs_current_bb = L ==>
  ?ids' full. LENGTH ids' = LENGTH sa.cs_current_insts /\
    fn_has_code (start_relabel L ids' sa) (start_swap sa L ids' sb) full /\
    fn_inst_ids_distinct full /\ full.fn_name = func.fn_name /\
    (!i. MEM i (fn_insts full) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
    (!i. i.inst_opcode = ALLOCA ==>
       (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
    (!fuel ctx'. run_from fuel ctx' full s = run_from fuel ctx obs s) /\
    (!t ctx'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       abi_decode_sim ctx' full s t ==> abi_decode_sim ctx obs s t)
Proof
  strip_tac >>
  qspecl_then [`func`, `obs`] strip_assume_tac
    (Q.GENL [`func`, `obs`] return_observer_ids_bound) >>
  qspec_then `obs` strip_assume_tac (Q.GEN `obs` return_observer_complete_fresh_label) >>
  qabbrev_tac `norm = return_observer_ids func bound obs` >>
  qabbrev_tac `full = return_observer_complete func norm keep` >>
  `fn_has_code (start_relabel L (return_observer_prefix_ids func bound ids) sa)
     (start_swap sa L (return_observer_prefix_ids func bound ids) sb) full` by
    (simp[Abbr `full`, Abbr `norm`] >> irule return_observer_complete_has_code >>
     irule return_observer_ids_relabel_code >> simp[]) >>
  `fn_inst_ids_distinct full /\
   (!i. i.inst_opcode = ALLOCA ==> (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
   full.fn_name = func.fn_name` by
    simp[Abbr `full`, Abbr `norm`, return_observer_ids_complete_metadata] >>
  `(!i. MEM i (fn_insts full) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
        MEM i (fn_insts func)) /\
   (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE)` by
    (simp[Abbr `full`, return_observer_complete_members, Abbr `norm`,
          return_observer_ids_insts, MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[return_observer_inst_ids_def]) >>
  `cs_extends (start_relabel L ids sa) (start_swap sa L ids sb)` by
    simp[start_relabel_extends] >>
  `L <> keep /\ sb.cs_current_bb <> keep` by
    (drule_all start_swap_fields >> strip_tac >>
     drule_all fn_has_code_start >> strip_tac >>
     fs[fn_has_code_def, start_relabel_def] >>
     imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
     fs[MEM_MAP] >> metis_tac[]) >>
  qexistsl_tac [`return_observer_prefix_ids func bound ids`, `full`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `full`, Abbr `norm`] >>
      irule return_observer_ids_complete_run >> fs[EVERY_MEM]) >>
  rpt strip_tac >> irule return_observer_ids_complete_sim >> simp[] >>
  qexistsl_tac [`bound`, `ctx'`, `func`, `keep`] >>
  fs[Abbr `full`, Abbr `norm`, EVERY_MEM]
QED

Theorem return_observer_relabel_success:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) obs /\
  fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ~s.vs_halted /\ s.vs_current_bb = L /\
  (!ids' fn'. LENGTH ids' = LENGTH sa.cs_current_insts /\
     fn_has_code (start_relabel L ids' sa) (start_swap sa L ids' sb) fn' /\
     fn_inst_ids_distinct fn' /\ fn'.fn_name = func.fn_name /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
     (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
     (!i. i.inst_opcode = ALLOCA ==>
        (MEM i (fn_insts fn') <=> MEM i (fn_insts func))) ==>
     ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         abi_decode_sim (return_observer_context ctx fn') fn' s t) ==>
  ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ abi_decode_sim ctx obs s t
Proof
  strip_tac >> drule_all return_observer_relabel_completion >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `!ids' fn'. _` drule_all >> strip_tac >>
  qexists_tac `t` >> simp[] >> first_x_assum irule >> simp[] >>
  metis_tac[]
QED

Theorem return_observer_counted_success_relabel:
  (!L ids fn'. LENGTH ids = LENGTH sa.cs_current_insts /\
     fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
     fn_inst_ids_distinct fn' /\ fn'.fn_name = func.fn_name /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
     (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
     (!i. i.inst_opcode = ALLOCA ==>
        (MEM i (fn_insts fn') <=> MEM i (fn_insts func))) ==>
     ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         abi_decode_sim (return_observer_context ctx fn') fn'
           (s with vs_current_bb := L) t) /\
  sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
  (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule abi_decode_sim_gas_path_relabel >> simp[] >> qexists_tac `sa` >> simp[] >>
  rpt strip_tac >> irule return_observer_relabel_success >> simp[] >>
  qexistsl_tac [`func`, `ids`, `sa`] >> simp[] >>
  qpat_x_assum `!L ids fn'. _` (qspec_then `L` ACCEPT_TAC)
QED

Theorem return_observer_relabel_abort:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  LENGTH ids = LENGTH sa.cs_current_insts /\
  fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) obs /\
  fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ~s.vs_halted /\ s.vs_current_bb = L /\
  (!ids' fn'. LENGTH ids' = LENGTH sa.cs_current_insts /\
     fn_has_code (start_relabel L ids' sa) (start_swap sa L ids' sb) fn' /\
     fn_inst_ids_distinct fn' /\ fn'.fn_name = func.fn_name /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
     (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
     (!i. i.inst_opcode = ALLOCA ==>
        (MEM i (fn_insts fn') <=> MEM i (fn_insts func))) ==>
     ?fuel r. run_from fuel (return_observer_context ctx fn') fn' s = r /\
              exit_result r /\ R r) ==>
  ?fuel r. run_from fuel ctx obs s = r /\ exit_result r /\ R r
Proof
  strip_tac >> drule_all return_observer_relabel_completion >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `!ids' fn'. _` drule_all >> strip_tac >>
  qexistsl_tac [`fuel`, `r`] >> metis_tac[]
QED

Theorem return_observer_counted_abort_relabel:
  (!L ids fn'. LENGTH ids = LENGTH sa.cs_current_insts /\
     fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
     fn_inst_ids_distinct fn' /\ fn'.fn_name = func.fn_name /\
     (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
     (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
     (!i. i.inst_opcode = ALLOCA ==>
        (MEM i (fn_insts fn') <=> MEM i (fn_insts func))) ==>
     ?fuel r. run_from fuel (return_observer_context ctx fn') fn'
                (s with vs_current_bb := L) = r /\ exit_result r /\ R r) /\
  sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
  (!h. ~R (Halt h)) /\
  (!a t b p. R (Abort a t) ==>
     R (Abort a (t with <|vs_current_bb := b; vs_prev_bb := p|>))) /\
  (!v t b p. R (IntRet v t) ==>
     R (IntRet v (t with <|vs_current_bb := b; vs_prev_bb := p|>))) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\ R r
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  mp_tac (Q.SPEC `\t. F` (Q.SPEC `sb` (Q.SPEC `sa`
    (Q.SPEC `ctx` frag_exec_gas_path_relabel)))) >>
  disch_then (qspecl_then [`R`, `func`, `s`] mp_tac) >> simp[] >>
  impl_tac >- (
    rpt strip_tac >> irule (SRULE [] return_observer_relabel_abort) >> simp[] >>
    qexistsl_tac [`func`, `ids`, `sa`] >> simp[] >>
    qexists_tac `sb` >> simp[] >>
    qpat_x_assum `!L ids fn'. _` (qspec_then `L` mp_tac) >> simp[]) >>
  simp[]
QED

(* The unrelabeled interface is also needed by straight-line decoder fragments. *)
Theorem return_observer_completion:
  cs_extends sa sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb obs /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb ==>
  ?full. fn_has_code sa sb full /\ fn_inst_ids_distinct full /\
    (!i. MEM i (fn_insts full) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
         MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
    (!i. i.inst_opcode = ALLOCA ==>
       (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
    (!fuel ctx'. run_from fuel ctx' full s = run_from fuel ctx obs s) /\
    (!t ctx'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       abi_decode_sim ctx' full s t ==> abi_decode_sim ctx obs s t)
Proof
  strip_tac >>
  qspecl_then [`func`, `obs`] strip_assume_tac
    (Q.GENL [`func`, `obs`] return_observer_ids_bound) >>
  qspec_then `obs` strip_assume_tac (Q.GEN `obs` return_observer_complete_fresh_label) >>
  qabbrev_tac `full = return_observer_complete func (return_observer_ids func bound obs) keep` >>
  `fn_has_code sa sb full` by
    (simp[Abbr `full`] >> irule return_observer_complete_has_code >>
     simp[return_observer_ids_code]) >>
  `fn_inst_ids_distinct full /\
   (!i. i.inst_opcode = ALLOCA ==> (MEM i (fn_insts full) <=> MEM i (fn_insts func)))` by
    simp[Abbr `full`, return_observer_ids_complete_metadata] >>
  `(!i. MEM i (fn_insts full) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
        MEM i (fn_insts func)) /\
   (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE)` by
    (simp[Abbr `full`, return_observer_complete_members,
          return_observer_ids_insts, MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[return_observer_inst_ids_def]) >>
  `sa.cs_current_bb <> keep /\ sb.cs_current_bb <> keep` by
    (qspecl_then [`sa`, `sb`, `obs`] mp_tac fn_has_code_start >> simp[] >>
     strip_tac >> fs[fn_has_code_def] >>
     imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
     fs[MEM_MAP] >> metis_tac[]) >>
  qexists_tac `full` >> simp[] >> conj_tac
  >- (rpt gen_tac >> simp[Abbr `full`] >>
      irule return_observer_ids_complete_run >> fs[EVERY_MEM]) >>
  rpt strip_tac >> irule return_observer_ids_complete_sim >> simp[] >>
  qexistsl_tac [`bound`, `ctx'`, `func`, `keep`] >> fs[Abbr `full`, EVERY_MEM]
QED

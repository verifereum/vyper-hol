Theory deployOutcomesFreeRuns
Ancestors
  contextRawReachable ctxLookupAgreeHelpers venomExecSemantics
  livenessTransferProofs venomState contextCodegenRel

Theorem run_blocks_outcomes_replace:
  (!fuel bb s os. MEM bb fn.fn_blocks ==>
    run_block fuel ctx bb (s with vs_outcomes := os) =
      case run_block fuel ctx bb s of
        OK t => OK (t with vs_outcomes := os)
      | Halt t => Halt (t with vs_outcomes := os)
      | Abort a t => Abort a (t with vs_outcomes := os)
      | IntRet vals t => IntRet vals (t with vs_outcomes := os)
      | Error e => Error e) ==>
  !fuel s os.
    run_blocks fuel ctx fn (s with vs_outcomes := os) =
      case run_blocks fuel ctx fn s of
        OK t => OK (t with vs_outcomes := os)
      | Halt t => Halt (t with vs_outcomes := os)
      | Abort a t => Abort a (t with vs_outcomes := os)
      | IntRet vals t => IntRet vals (t with vs_outcomes := os)
      | Error e => Error e
Proof
  strip_tac >> Induct >> rpt gen_tac
  >- simp[run_blocks_def] >>
  simp[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  simp[] >> Cases_on `run_block fuel ctx bb s` >> simp[] >>
  rename1 `v.vs_halted` >> Cases_on `v.vs_halted` >> simp[]
QED

Theorem run_context_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  (!fuel bb s os. MEM bb fn.fn_blocks ==>
    run_block fuel ctx bb (s with vs_outcomes := os) =
      case run_block fuel ctx bb s of
        OK t => OK (t with vs_outcomes := os)
      | Halt t => Halt (t with vs_outcomes := os)
      | Abort a t => Abort a (t with vs_outcomes := os)
      | IntRet vals t => IntRet vals (t with vs_outcomes := os)
      | Error e => Error e) ==>
  !fuel s os.
    run_context fuel ctx (s with vs_outcomes := os) =
      case run_context fuel ctx s of
        OK t => OK (t with vs_outcomes := os)
      | Halt t => Halt (t with vs_outcomes := os)
      | Abort a t => Abort a (t with vs_outcomes := os)
      | IntRet vals t => IntRet vals (t with vs_outcomes := os)
      | Error e => Error e
Proof
  strip_tac >> drule run_blocks_outcomes_replace >> strip_tac >>
  rpt gen_tac >> simp[run_context_def, run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[] >>
  first_x_assum (qspecl_then
    [`fuel`, `s with <|vs_prev_bb := NONE; vs_current_bb := x; vs_inst_idx := 0|>`,
     `os`] mp_tac) >> simp[]
QED

Theorem active_inst_outcomes_replace[simp]:
  active_inst fn inst (s with vs_outcomes := os) = active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem raw_reachable_outcomes_replace_aux[local]:
  !seed ctx f i t. raw_reachable seed ctx f i t ==>
  !s os name entry.
    seed = (s with vs_outcomes := os) /\
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME entry /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) (fn_insts entry) /\
    (!u os v. enters_block entry (u with vs_outcomes := os) v ==>
      ?v0. enters_block entry u v0 /\ v = (v0 with vs_outcomes := os)) /\
    (!fuel inst u os v. active_inst entry inst u /\
      step_inst fuel ctx inst (u with vs_outcomes := os) = OK v ==>
      ?v0. step_inst fuel ctx inst u = OK v0 /\
            v = (v0 with vs_outcomes := os)) ==>
    f = entry /\
    ?t0. raw_reachable s ctx f i t0 /\ t = (t0 with vs_outcomes := os)
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `!u os v. enters_block _ _ _ ==> _`
        (qspecl_then
          [`s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`,
           `os`, `t`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
      qexists_tac `v0` >> simp[] >>
      irule raw_reachable_entry >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!s os name entry. _`
        (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_assum `!fuel inst u os v. _` (drule_all_then strip_assume_tac) >>
      gvs[] >> qexists_tac `v0 with vs_inst_idx := SUC t0.vs_inst_idx` >>
      simp[] >> irule raw_reachable_next >> conj_tac
      >- (qpat_x_assum `active_inst _ i' _` mp_tac >> simp[active_inst_def]) >>
      qexistsl_tac [`fuel`, `i`] >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!s os name entry. _`
        (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      qpat_assum `!fuel inst u os v. _` (drule_all_then strip_assume_tac) >>
      gvs[] >>
      qpat_assum `!u os v. enters_block _ _ _ ==> _`
        (drule_then strip_assume_tac) >> gvs[] >>
      qexists_tac `v0'` >> simp[] >>
      irule raw_reachable_block >> simp[] >>
      qexistsl_tac [`fuel`, `i`, `t0`, `v0`] >> simp[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s os name entry. _`
    (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all EVERY_active_inst >> simp[]
QED

Theorem raw_reachable_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\inst. inst.inst_opcode <> INVOKE) (fn_insts entry) /\
  (!u os v. enters_block entry (u with vs_outcomes := os) v ==>
    ?v0. enters_block entry u v0 /\ v = (v0 with vs_outcomes := os)) /\
  (!fuel inst u os v. active_inst entry inst u /\
    step_inst fuel ctx inst (u with vs_outcomes := os) = OK v ==>
    ?v0. step_inst fuel ctx inst u = OK v0 /\
          v = (v0 with vs_outcomes := os)) ==>
  !s os f i t.
    raw_reachable (s with vs_outcomes := os) ctx f i t ==>
    f = entry /\
    ?t0. raw_reachable s ctx f i t0 /\ t = (t0 with vs_outcomes := os)
Proof
  rpt strip_tac >> drule raw_reachable_outcomes_replace_aux >>
  disch_then (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >> simp[]
QED

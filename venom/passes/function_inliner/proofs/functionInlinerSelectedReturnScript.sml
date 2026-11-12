(* Selected return execution through fields-only residual adapters. *)
Theory functionInlinerSelectedReturn
Ancestors
  functionInlinerReturnRouting functionInlinerReturnStorage
  functionInlinerRoutedReturnExecution functionInlinerPhiTransport
  functionInlinerParameterExecution venomExecSemantics venomExecProofs
  venomInst list rich_list indexedLists analysisSimDefs pair
  functionInlinerReturnAdapterLayout functionInlinerReturnTransport
  functionInlinerLocation functionInlinerSiteLayout

Theorem inline_assign_fields_run:
  !xs ys s. MAP inline_inst_fields xs = MAP inline_inst_fields ys /\
    EVERY (\i. i.inst_opcode = ASSIGN) ys ==>
    run_insts fuel ctx xs s = run_insts fuel ctx ys s
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  `h.inst_opcode = ASSIGN` by gvs[] >>
  `step_inst fuel ctx h' s = step_inst fuel ctx h s` by
    (irule inline_fields_step >> gvs[]) >>
  simp[Once run_insts_def] >>
  simp[Once run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >> metis_tac[]
QED

Theorem inline_return_interval_execute:
  inline_adapter_interval fn l k
    (MAPi (\j op. (ASSIGN,[op],[EL j dests])) ops) ret /\
  LENGTH dests = LENGTH ops /\ eval_operands ops t = SOME vals /\
  (!x v. MEM x dests /\ MEM (Var v) ops ==> x <> v) /\ ~t.vs_halted ==>
  ?bb. lookup_block l fn.fn_blocks = SOME bb /\
    exec_block fuel ctx bb (t with vs_inst_idx := k) =
      OK (jump_to ret (FOLDL (\s (x,w). update_var x w s) t (ZIP (dests,vals))))
Proof
  strip_tac >>
  gvs[inline_adapter_interval_def] >>
  qabbrev_tac `xs = TAKE (LENGTH ops) (DROP k bb.bb_instructions)` >>
  qabbrev_tac `ys = MAP (\(x,op). <|inst_id := 0; inst_opcode := ASSIGN;
    inst_operands := [op]; inst_outputs := [x]|>) (ZIP (dests,ops))` >>
  `MAP inline_inst_fields xs = MAP inline_inst_fields ys` by
    (qpat_x_assum `MAP inline_inst_fields _ = _`
       (mp_tac o Q.AP_TERM `TAKE (LENGTH ops)`) >>
     simp[Abbr `xs`, Abbr `ys`, GSYM MAP_TAKE, TAKE_TAKE, TAKE_APPEND,
       TAKE_LENGTH_TOO_LONG] >>
     disch_then SUBST1_TAC >> irule LIST_EQ >>
     simp[EL_MAP, EL_MAPi, EL_ZIP, inline_inst_fields_def]) >>
  `EVERY (\i. i.inst_opcode = ASSIGN) ys` by
    (simp[Abbr `ys`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     pairarg_tac >> simp[]) >>
  `run_insts fuel ctx xs t =
     OK (FOLDL (\s (x,w). update_var x w s) t (ZIP (dests,vals)))` by
    (drule_all inline_assign_fields_run >> disch_then (fn th => rewrite_tac[th]) >>
     unabbrev_all_tac >> irule inline_return_routed_zip_execute >> simp[]) >>
  irule inline_return_sequence_exec_block >>
  conj_tac >- simp[functionInlinerOperationalTheory.inline_writes_control] >>
  qexists `xs` >>
  simp[Abbr `xs`, LENGTH_TAKE, LENGTH_DROP, EL_TAKE, EL_DROP] >>
  `inline_inst_fields (EL (k + LENGTH ops) bb.bb_instructions) =
     (JMP,[Label ret],[])` by
    (qpat_x_assum `MAP inline_inst_fields (TAKE (LENGTH ops + 1) _) = _`
       (mp_tac o Q.AP_TERM `EL (LENGTH ops)`) >>
     simp[EL_MAP, EL_TAKE, EL_DROP, EL_APPEND_EQN]) >>
  qexists `(EL (k + LENGTH ops) bb.bb_instructions).inst_id` >>
  conj_tac
  >- (gvs[get_instruction_def, inline_inst_fields_def] >>
      Cases_on `EL (k + LENGTH ops) bb.bb_instructions` >>
      gvs[instruction_component_equality]) >>
  qpat_x_assum `MAP inline_inst_fields (TAKE (LENGTH ops) _) = _` mp_tac >>
  simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (mp_tac o Q.AP_TERM `EL n`) >>
  `LENGTH ys = LENGTH ops` by simp[Abbr `ys`] >>
  gvs[EL_MAP, inline_inst_fields_def, EVERY_EL]
QED

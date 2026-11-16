Theory gasFocusInitialSingletonCut
Ancestors
  gasFocusInitialRowReplay dftPacketNativeSlice dftGasSourcePrefix
  dftGasFromListRestore dftGasPrefixProvider gasEvents venomExecProofs
  dftIndexedExec venomExecSemantics venomInst venomState
  list rich_list arithmetic

Theorem focus_initial_singleton_cut:
  !F C sf entry bb ps xs sp q.
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  phi_prefix_length bb.bb_instructions = LENGTH ps /\
  eval_phis entry bb.bb_instructions = OK sp /\
  q < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
    (TAKE q xs) ==>
  let z = TAKE q xs;
      levels = [(sf,[(bb,1,z)],NONE)];
      E = MAP (\i. (sf.fn_name,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) z);
      K = MAP (\i. ([],1,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) z);
      row_eval = (\F C owner (bb,e,z) s.
        case eval_phis s bb.bb_instructions of
          OK sp =>
           (gas_events_block (F-e) C owner
             (bb with bb_instructions :=
               TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
             (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
            FOLDR (dft_exec_cons (F-e) C) OK z
             (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        | other => ([],other));
      plan_eval = (\F C owner plan entry.
        FOLDL (\(es,r) row.
          case r of
            OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
          | other => (es,other)) ([],OK entry) plan);
      call_setup = (\C c s.
        case decode_invoke c of
          NONE => Error "invoke: bad operand format"
        | SOME (nm,ops) =>
          case lookup_function nm C.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee =>
            case eval_operands ops s of
              NONE => Error "invoke: undefined argument"
            | SOME args =>
              case setup_callee callee args s of
                NONE => Error "invoke: empty function"
              | SOME cs => OK cs);
      rooted_eval = (\F C levels entry.
        FOLDL (\(prior,r) (sf,plan,call).
          case r of
            OK ent =>
             (prior ++ FST (plan_eval F C sf.fn_name plan ent),
              case SND (plan_eval F C sf.fn_name plan ent) of
                OK caller =>
                  (case call of NONE => OK caller | SOME c => call_setup C c caller)
              | other => other)
          | other => (prior,other)) ([],OK entry) levels);
      plan_ok = (\F C sf a plan entry.
        plan <> [] /\
        MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
        (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
          e <= F /\ MEM bb sf.fn_blocks /\
          (if SUC r < LENGTH plan then
            bb.bb_instructions <> [] /\
            EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
            is_terminator (LAST bb.bb_instructions).inst_opcode /\
            ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
            z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
           else
            LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
        (!r bb e z es s.
          r < LENGTH plan /\ EL r plan = (bb,e,z) /\
          plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
          lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
          (0 < r ==> ~s.vs_halted)));
      levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
        levels <> [] /\ LENGTH paths = LENGTH levels /\
        LENGTH incoming = LENGTH levels /\
        HD paths = root_path /\ HD incoming = root_depth /\
        FST (HD levels) = root_fn /\
        (!i sf plan call.
          i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
          plan <> [] /\
          (!prior ent.
            rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
            plan_ok F C sf (EL i incoming) plan ent) /\
          (if SUC i < LENGTH levels then
            ?c nm ops bb e z.
              call = SOME c /\ LAST plan = (bb,e,z) /\
              c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
              c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
              lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
              EL (SUC i) incoming = e /\
              EL (SUC i) paths = (e,c.inst_id)::EL i paths
           else call = NONE)))
  in !gs tail.
    1 <= F /\ LENGTH gs = LENGTH E ==>
    let R = entry with vs_gas_readings := gs ++ tail in
      levels_ok F C levels [[]] [0] sf R [] 0 /\
      (?extra. E = FST (rooted_eval F C levels R) ++ extra) /\
      (!ev u. rooted_eval F C levels R = (ev,OK u) ==>
        ev = E /\ u.vs_gas_readings = tail /\
        (!tail'. rooted_eval F C levels
          (entry with vs_gas_readings := gs ++ tail') =
            (E,OK (u with vs_gas_readings := tail'))) /\
        ?before after.
          dftGasFromListTraceDefs$trace_blocks [] 0 F C sf R =
            before ++ [(([],1,(EL q xs).inst_id),sf,EL q xs,u)] ++ after /\
          dftGasFromListTraceDefs$trace_gas before = ZIP (K,gs)) /\
      (!ev r. rooted_eval F C levels R = (ev,r) /\ ~(?u. r = OK u) ==>
        run_blocks F C sf R = r /\ gas_events_blocks F C sf R = ev)
Proof
  rpt gen_tac >> strip_tac >>
  simp_tac bool_ss [combinTheory.LET_FORALL_ELIM, combinTheory.S_DEF,
    combinTheory.o_DEF, combinTheory.C_DEF] >> BETA_TAC >>
  map_every (fn v => qx_gen_tac v >> disch_tac)
    [`z`,`levels`,`E`,`keys`,`row_eval`,`plan_eval`,`call_setup`,
     `rooted_eval`,`plan_ok`,`levels_ok`] >>
  qx_gen_tac `gs` >> qx_gen_tac `tail` >> strip_tac >>
  qx_gen_tac `R` >> disch_tac >> markerLib.REABBREV_TAC >>
  conj_tac >- suspend "levels" >>
  suspend "execution"
QED

Resume focus_initial_singleton_cut[levels]:
  simp[Abbr `levels_ok`, Abbr `levels`, Abbr `rooted_eval`,
       Abbr `plan_ok`, Abbr `plan_eval`, Abbr `z`,
       DROP_APPEND, LENGTH_TAKE, EVERY_TAKE, EVERY_MEM, Abbr `R`] >>
  gvs[EVERY_MEM] >> metis_tac[lookup_block_MEM]
QED

Resume focus_initial_singleton_cut[execution]:
  rename1 `1 <= fuel` >>
  `!rs. eval_phis (entry with vs_gas_readings := rs) bb.bb_instructions =
     OK (sp with vs_gas_readings := rs)` by
    (gen_tac >> mp_tac (Q.INST [`s` |-> `entry`, `insts` |-> `bb.bb_instructions`,
       `gs` |-> `rs`] eval_phis_restore) >>
     Cases_on `eval_phis (entry with vs_gas_readings := rs) bb.bb_instructions` >>
     simp[restore_rel_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
     i.inst_opcode <> INVOKE /\ ~is_pseudo i.inst_opcode) z` by
    (`EVERY (\i. ~is_pseudo i.inst_opcode) z` by
       (simp[Abbr `z`] >> irule EVERY_TAKE >> simp[]) >>
     qpat_x_assum `EVERY (\i. ~is_terminator i.inst_opcode /\ _) z` mp_tac >>
     qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) z` mp_tac >>
     simp[NoAsms, EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `be = sp with vs_inst_idx := LENGTH ps` >>
  qabbrev_tac `cut = bb with bb_instructions := ps ++ z` >>
  `!rs. rooted_eval fuel C levels (entry with vs_gas_readings := rs) =
    (gas_events_block (fuel-1) C sf.fn_name cut (be with vs_gas_readings := rs),
     FOLDR (dft_exec_cons (fuel-1) C) OK z (be with vs_gas_readings := rs))` by
    (gen_tac >> map_every (fn v => qpat_x_assum v kall_tac)
       [`Abbrev (levels_ok = _)`, `Abbrev (plan_ok = _)`, `Abbrev (call_setup = _)`] >>
     simp[Abbr `rooted_eval`, Abbr `plan_eval`, Abbr `row_eval`,
       Abbr `levels`, Abbr `cut`, Abbr `be`, TAKE_APPEND] >>
     Cases_on `FOLDR (dft_exec_cons (fuel-1) C) OK z
       (sp with <|vs_inst_idx := LENGTH ps; vs_gas_readings := rs|>)` >> gvs[]) >>
  map_every (fn v => qpat_x_assum v kall_tac)
    [`Abbrev (levels_ok = _)`, `Abbrev (plan_ok = _)`,
     `Abbrev (rooted_eval = _)`, `Abbrev (plan_eval = _)`,
     `Abbrev (row_eval = _)`, `Abbrev (call_setup = _)`, `Abbrev (levels = _)`] >>
  simp[Abbr `R`] >>
  `!rs. gas_events_block (fuel-1) C sf.fn_name cut (be with vs_gas_readings := rs) =
    gas_events_block (fuel-1) C sf.fn_name
      <|bb_label := be.vs_current_bb;
        bb_instructions := REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ z|>
      (be with vs_gas_readings := rs)` by
    (gen_tac >> irule gas_events_block_suffix_cong >> qexists_tac `z` >>
     simp[Abbr `be`, Abbr `cut`, DROP_APPEND]) >>
  qspecl_then [`fuel-1`,`C`,`sf.fn_name`,`be`] mp_tac
    focus_initial_unvisited_row_replay >>
  disch_then (qspecl_then [`z`,`gs`] mp_tac) >>
  simp[GSYM EVERY_CONJ, Abbr `E`] >> disch_tac >>
  first_assum (qspec_then `tail` strip_assume_tac) >>
  simp[] >> conj_tac >- suspend "successful" >>
  suspend "stopped"
QED

Finalise focus_initial_singleton_cut

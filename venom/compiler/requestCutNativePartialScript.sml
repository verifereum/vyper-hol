Theory requestCutNativePartial
Ancestors
  requestCutNativeBoundary dftPacketNativeSlice dftNativePlanPrefix
  dftGasFromListTraceDefs dftGasFromListReadings dftIndexedExec
  venomExecSemantics venomInst venomState list rich_list arithmetic

Theorem request_cut_native_partial_row:
  !k s bb keys.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    (?extra. keys = MAP FST (trace_gas (trace_block p d f C sf
      (bb with bb_instructions := TAKE (s.vs_inst_idx+k) bb.bb_instructions) s)) ++ extra) /\
    (!u. FOLDR (dft_exec_cons f C) OK
       (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u ==>
       MAP FST (trace_gas (trace_block p d f C sf
         (bb with bb_instructions := TAKE (s.vs_inst_idx+k) bb.bb_instructions) s)) = keys) ==>
    case FOLDR (dft_exec_cons f C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s of
      OK u => u.vs_inst_idx = s.vs_inst_idx + k /\
        exec_block f C bb s = exec_block f C bb u /\
        MAP FST (trace_gas (trace_block p d f C sf bb s)) =
          keys ++ MAP FST (trace_gas (trace_block p d f C sf bb u))
    | stopped => exec_block f C bb s = stopped /\
        ?extra. keys = MAP FST (trace_gas (trace_block p d f C sf bb s)) ++ extra
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `z = TAKE k (DROP s.vs_inst_idx bb.bb_instructions)` >>
  qabbrev_tac `cut = bb with bb_instructions := TAKE (s.vs_inst_idx+k) bb.bb_instructions` >>
  `DROP s.vs_inst_idx bb.bb_instructions = z ++ DROP k (DROP s.vs_inst_idx bb.bb_instructions) /\
   DROP s.vs_inst_idx cut.bb_instructions = z` by
    simp[Abbr `z`, Abbr `cut`, TAKE_DROP, DROP_TAKE] >>
  mp_tac (Q.SPECL [`z`,`s`,`bb`,`cut`,`DROP k (DROP s.vs_inst_idx bb.bb_instructions)`]
    native_list_prefix_boundary) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `FOLDR (dft_exec_cons f C) OK z s` >> simp[NoAsms] >> strip_tac
  >- suspend "success" >>
  `~(?u. FOLDR (dft_exec_cons f C) OK z s = OK u)` by
    (qpat_assum `FOLDR (dft_exec_cons f C) OK z s = _` SUBST1_TAC >> simp[NoAsms]) >>
  `trace_block p d f C sf bb s = trace_block p d f C sf cut s` by
    (match_mp_tac (Q.SPECL [`z`,`s`,`bb`,`cut`,`DROP k (DROP s.vs_inst_idx bb.bb_instructions)`]
      request_cut_native_trace_stopped) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `extra` >>
  qpat_assum `trace_block p d f C sf bb s = _` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume request_cut_native_partial_row[success]:
  rename1 `FOLDR _ _ z s = OK u` >>
  `u.vs_inst_idx = s.vs_inst_idx+k` by
    (mp_tac (Q.SPECL [`k`,`s`,`u`]
      (Q.INST [`fuel` |-> `f`, `C` |-> `C`, `bb` |-> `bb`]
        native_trace_block_prefix_split)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `Abbrev (z = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       first_assum ACCEPT_TAC) >> simp[]) >>
  conj_tac
  >- (qpat_assum `u.vs_inst_idx = s.vs_inst_idx + k` mp_tac >>
      simp[NoAsms, ADD_COMM]) >>
  qpat_assum `!u'. OK u = OK u' ==> _`
    (ACCEPT_TAC o (fn th => MATCH_MP th (REFL ``OK (u:venom_state)``)) o Q.SPEC `u`)
QED

Finalise request_cut_native_partial_row

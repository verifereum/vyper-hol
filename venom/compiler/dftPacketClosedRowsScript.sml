Theory dftPacketClosedRows
Ancestors
  dftPacketFillingBoundary dftGasFromListTraceDefs dftGasToListReplay
  dftRunRel crossBlockSimProofs gasEvents venomExecSemantics
  passSimulationDefs venomState list rich_list arithmetic sorting

Theorem dft_packet_closed_rows_conservation:
  !mss ess kss entries out.
    0 < LENGTH mss /\ LENGTH ess = LENGTH mss /\
    LENGTH kss = LENGTH mss /\ LENGTH entries = LENGTH mss /\
    (!i. i < LENGTH mss ==>
      EVERY IS_SOME (EL i mss) /\
      LENGTH (EL i mss) = LENGTH (EL i ess) /\
      LENGTH (EL i mss) = LENGTH (EL i kss) /\
      PERM (MAP THE (EL i mss) ++
        (if SUC i < LENGTH mss then (EL (SUC i) entries).vs_gas_readings
         else out.vs_gas_readings)) (EL i entries).vs_gas_readings) ==>
    EVERY IS_SOME (FLAT mss) /\
    LENGTH (FLAT mss) = LENGTH (FLAT ess) /\
    LENGTH (FLAT mss) = LENGTH (FLAT kss) /\
    PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings)
      (HD entries).vs_gas_readings
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `ess` >> Cases_on `kss` >> Cases_on `entries` >> gvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  Cases_on `mss = []`
  >- gvs[] >>
  `EVERY IS_SOME (FLAT mss) /\
   LENGTH (FLAT mss) = LENGTH (FLAT t) /\
   LENGTH (FLAT mss) = LENGTH (FLAT t') /\
   PERM (MAP THE (FLAT mss) ++ out.vs_gas_readings)
      (HD t'').vs_gas_readings` by
    (first_x_assum irule >> simp[] >>
     reverse conj_tac >- (Cases_on `mss` >> gvs[]) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  simp[] >>
  irule PERM_TRANS >>
  qexists_tac `MAP THE h ++ (HD t'').vs_gas_readings` >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >>
      metis_tac[PERM_APPEND_IFF]) >>
  qpat_x_assum `PERM (MAP THE h ++ _) _` mp_tac >>
  Cases_on `mss` >> gvs[]
QED

Theorem dft_packet_closed_rows_target:
  !bbs bts entries N C tf inc ir out.
    0 < LENGTH bbs /\ inc + LENGTH bbs <= N /\
    LENGTH bts = LENGTH bbs /\ LENGTH entries = LENGTH bbs /\
    (!i. i < LENGTH bbs ==>
      lookup_block (EL i entries).vs_current_bb tf.fn_blocks = SOME (EL i bts) /\
      (SUC i < LENGTH bbs ==> ~(EL (SUC i) entries).vs_halted) /\
      (!F. N <= F ==> run_block (F-(inc+SUC i)) C (EL i bts) (EL i entries) =
        (if SUC i < LENGTH bbs then OK (EL (SUC i) entries)
         else IntRet ir out))) ==>
    !F. N <= F ==> run_blocks (F-inc) C tf (HD entries) = IntRet ir out
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `bts` >> Cases_on `entries` >> gvs[] >>
  qpat_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  rpt strip_tac >> rename1 `run_blocks (fuel-inc) C tf _ = _` >>
  `fuel-inc = SUC (fuel-(inc+1))` by decide_tac >>
  asm_rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `bbs = []` >- gvs[] >>
  `run_blocks (fuel-(inc+1)) C tf (HD t') = IntRet ir out` suffices_by
    (Cases_on `t'` >> gvs[]) >>
  `0 < LENGTH bbs` by (Cases_on `bbs` >> gvs[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`N`,`t`] >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
  simp[]
  >> (simp [SUC_ONE_ADD])
QED

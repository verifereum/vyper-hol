Theory dftGasInvFuel
Ancestors
  dftGasOracleDefs

Theorem ev_fuel_extend:
  (!orc p d fuel ctx inst s. !r extra.
    ev_step orc p d fuel ctx inst s = r /\ (!msg. r <> Error msg) ==>
    ev_step orc p d (fuel + extra) ctx inst s = r) /\
  (!orc p d fuel ctx bb s. !r extra.
    ev_block orc p d fuel ctx bb s = r /\ (!msg. r <> Error msg) ==>
    ev_block orc p d (fuel + extra) ctx bb s = r) /\
  (!orc p d fuel ctx fn s. !r extra.
    ev_blocks orc p d fuel ctx fn s = r /\ (!msg. r <> Error msg) ==>
    ev_blocks orc p d (fuel + extra) ctx fn s = r)
Proof
  ho_match_mp_tac ev_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[ev_step_def] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      once_rewrite_tac[ev_block_def] >>
      strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `fuel` >> simp[arithmeticTheory.ADD_CLAUSES] >>
  once_rewrite_tac[ev_blocks_def] >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem ev_step_fuel_extend:
  !orc p d fuel ctx inst s r extra.
    ev_step orc p d fuel ctx inst s = r /\ (!msg. r <> Error msg) ==>
    ev_step orc p d (fuel + extra) ctx inst s = r
Proof
  metis_tac[ev_fuel_extend]
QED

Theorem ev_block_fuel_extend:
  !orc p d fuel ctx bb s r extra.
    ev_block orc p d fuel ctx bb s = r /\ (!msg. r <> Error msg) ==>
    ev_block orc p d (fuel + extra) ctx bb s = r
Proof
  metis_tac[ev_fuel_extend]
QED

Theorem ev_blocks_fuel_extend:
  !orc p d fuel ctx fn s r extra.
    ev_blocks orc p d fuel ctx fn s = r /\ (!msg. r <> Error msg) ==>
    ev_blocks orc p d (fuel + extra) ctx fn s = r
Proof
  metis_tac[ev_fuel_extend]
QED

Theorem ev_steps_common_fuel:
  !xs orc p d ctx.
    EVERY (\(i,t,r).
      (?fuel. ev_step orc p d fuel ctx i t = r) /\
      (!msg. r <> Error msg)) xs ==>
    ?fuel. EVERY (\(i,t,r). ev_step orc p d fuel ctx i t = r) xs
Proof
  Induct >> simp[] >> rpt gen_tac >>
  PairCases_on `h` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `ev_step orc p d head_fuel ctx i t = r` >>
  rename1 `EVERY (\(i,t,r). ev_step orc p d tail_fuel ctx i t = r) xs` >>
  qexists_tac `head_fuel + tail_fuel` >> conj_tac
  >- (irule ev_step_fuel_extend >> simp[]) >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM item xs` >> PairCases_on `item` >>
  first_x_assum drule >> first_x_assum drule >> simp[] >>
  rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule ev_step_fuel_extend >> simp[]
QED

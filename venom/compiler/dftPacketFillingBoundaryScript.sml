Theory dftPacketFillingBoundary
Ancestors
  dftIndexedExec dftGasToListReplay passSimulationDefs list

Theorem dft_packet_flat_filling_split:
  !mss gs. LIST_REL R (FLAT mss) gs ==>
    ?gss. gs = FLAT gss /\ LIST_REL (LIST_REL R) mss gss
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[LIST_REL_SPLIT1] >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `ys1::gss` >> simp[]
QED

Theorem dft_packet_closed_ok_entry:
  (!gs tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots gs ==>
    ((?f. terminates (FOLDR (dft_exec_cons f C) OK xs
       (be with vs_gas_readings := gs ++ tail))) ==>
     residual_result tail (OK next)
       (FOLDR (dft_exec_cons fuel C) OK xs
         (be with vs_gas_readings := gs ++ tail)))) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots gs /\
  FOLDR (dft_exec_cons fuel C) OK xs
    (be with vs_gas_readings := gs ++ tail) = OK u ==>
  u = next with vs_gas_readings := tail
Proof
  rpt strip_tac >>
  `?f. terminates (FOLDR (dft_exec_cons f C) OK xs
    (be with vs_gas_readings := gs ++ tail))` by
    (qexists_tac `fuel` >> simp[terminates_def]) >>
  first_x_assum (qspecl_then [`gs`, `tail`] mp_tac) >>
  simp[] >> metis_tac[]
QED

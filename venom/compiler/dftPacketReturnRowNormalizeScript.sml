Theory dftPacketReturnRowNormalize
Ancestors
  dftPacketReturnActivation dftGasFromListTraceDefs dftIndexedExec
  gasEvents venomExecSemantics venomState list rich_list sorting

Theorem dft_packet_return_successful_row_normalize:
  (r8 = OK v \/ ?ir. r8 = IntRet ir v) /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  terminates r8 /\
  PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ rest) be.vs_gas_readings /\
  (!u. (r8 = OK u \/ ?ir. r8 = IntRet ir u) ==>
    EVERY IS_SOME (FLAT ms) /\ rest = u.vs_gas_readings) /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-f) C8) OK ys be = r8 /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      (?extra. FLAT ess =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) ==>
        terminates (FOLDR (dft_exec_cons (F-f) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (FOLDR (dft_exec_cons (F-f) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)))
          (restore_result [] r8) /\
        (((?u. r8 = OK u) \/ (?ir u. r8 = IntRet ir u)) ==>
          gas_events_block (F-f) C7 sf.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
            (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
          residual_result tail r8
            (FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
      (!u. (FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = OK u \/
            ?ir. FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = IntRet ir u) ==>
        trace_gas (trace_block b f (F-f) C7 sf
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs)))) ==>
  rest = v.vs_gas_readings /\ EVERY IS_SOME (FLAT ms) /\
  LENGTH (FLAT ms) = LENGTH (FLAT ess) /\
  LENGTH (FLAT ms) = LENGTH (FLAT ks) /\
  PERM (MAP THE (FLAT ms) ++ rest) be.vs_gas_readings /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons (F-f) C8) OK ys be = r8 /\
    (!gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      (?extra. FLAT ess =
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?g. terminates (FOLDR (dft_exec_cons g C7) OK xs
          (be with vs_gas_readings := gs ++ tail))) ==>
        terminates (FOLDR (dft_exec_cons (F-f) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (FOLDR (dft_exec_cons (F-f) C7) OK xs
            (be with vs_gas_readings := gs ++ tail)))
          (restore_result [] r8) /\
        gas_events_block (F-f) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
        residual_result tail r8
          (FOLDR (dft_exec_cons (F-f) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) /\
      (!u. (FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = OK u \/
            ?ir. FOLDR (dft_exec_cons (F-f) C7) OK xs
              (be with vs_gas_readings := gs ++ tail) = IntRet ir u) ==>
        trace_gas (trace_block b f (F-f) C7 sf
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT ks,gs))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY IS_SOME (FLAT ms) /\ rest = v.vs_gas_readings` by metis_tac[] >>
  `FILTER IS_SOME (FLAT ms) = FLAT ms` by metis_tac[FILTER_EQ_ID] >>
  `LENGTH (FLAT ms) = LENGTH (FLAT ess) /\
   LENGTH (FLAT ms) = LENGTH (FLAT ks)` by
    metis_tac[LENGTH_FLAT,MAP_EQ_LIST_REL,LIST_REL_LENGTH] >>
  simp[] >>
  conj_tac >- gvs[] >>
  qx_gen_tac `fuel` >> strip_tac >>
  qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >>
  simp[] >> metis_tac[]
QED

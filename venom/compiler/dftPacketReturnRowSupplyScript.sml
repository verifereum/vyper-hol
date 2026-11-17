Theory dftPacketReturnRowSupply
Ancestors
  dftPacketReturnReplay dftGasFromListTraceDefs dftIndexedExec
  dftRunRel gasOracleReplay gasEvents finite_map
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem dft_packet_return_row_supply:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  k <= LENGTH xs /\ LENGTH ms = LENGTH xs /\
  LENGTH ess = LENGTH xs /\ LENGTH ks = LENGTH xs /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  (!q c. q < k /\ c = EL q xs /\ c.inst_opcode = INVOKE ==>
    ?h b0 done entry ir out post nm ops ctf args.
      FLOOKUP (calls : (gas_event,
        num # num # venom_state # num list # venom_state #
        (internal_return # venom_state # venom_state) option) fmap)
        (a,e,c.inst_id) = SOME (q,h,b0,done,entry,SOME (ir,out,post)) /\
      decode_invoke c = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\
      setup_callee ctf args b0 = SOME entry /\
      (!pg rest u.
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pg /\
        FOLDR (dft_exec_cons f C7) OK (TAKE q xs)
          (be with vs_gas_readings := FLAT pg ++ rest) = OK u ==>
        (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
        (!callee argv.
          setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
          setup_callee callee argv b0)) /\
      (!csf ws.
        lookup_function nm C7.ctx_functions = SOME csf /\
        ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) ws ==>
        !tail.
          (?extra. EL q ess = gas_events_blocks f C7 csf
            (entry with vs_gas_readings := ws ++ tail) ++ extra) /\
          (terminates (run_blocks f C7 csf (entry with vs_gas_readings := ws ++ tail)) ==>
            residual_result tail (IntRet ir out)
              (run_blocks f C7 csf (entry with vs_gas_readings := ws ++ tail)) /\
            gas_events_blocks f C7 csf (entry with vs_gas_readings := ws ++ tail) = EL q ess) /\
          (!ret v.
            run_blocks f C7 csf (entry with vs_gas_readings := ws ++ tail) = IntRet ret v ==>
            trace_gas (trace_blocks ((e,c.inst_id)::a) e f C7 csf
              (entry with vs_gas_readings := ws ++ tail)) = ZIP (EL q ks,ws)))) ==>
  !q pg rest u ws.
    q < k /\ (EL q xs).inst_opcode = INVOKE /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) pg /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (EL q ms) ws /\
    FOLDR (dft_exec_cons f C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT pg ++ rest) = OK u ==>
    (!tail. ?extra. EL q ess = gas_events_step f C7 sf.fn_name (EL q xs)
      (u with vs_gas_readings := ws ++ tail) ++ extra) /\
    (!tail v.
      step_inst f C7 (EL q xs) (u with vs_gas_readings := ws ++ tail) = OK v ==>
      gas_events_step f C7 sf.fn_name (EL q xs)
        (u with vs_gas_readings := ws ++ tail) = EL q ess /\
      v.vs_gas_readings = tail /\
      trace_gas (trace_step a e f C7 sf (EL q xs)
        (u with vs_gas_readings := ws ++ tail)) = ZIP (EL q ks,ws) /\
      (!tail'. step_inst f C7 (EL q xs) (u with vs_gas_readings := ws ++ tail') =
        OK (v with vs_gas_readings := tail') /\
        gas_events_step f C7 sf.fn_name (EL q xs)
          (u with vs_gas_readings := ws ++ tail') = EL q ess))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!q c. _` (qspecl_then [`q`, `EL q xs`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!pg rest u. _` (qspecl_then [`pg`, `rest`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  `q < LENGTH ms` by decide_tac >>
  `LENGTH (EL q ks) = LENGTH ws` by
    (imp_res_tac LIST_REL_LENGTH >> fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  irule dft_packet_return_invoke_replay >>
  simp[] >> rpt (goal_assum $ drule_at Any) >>
  simp[] >> metis_tac[]
QED

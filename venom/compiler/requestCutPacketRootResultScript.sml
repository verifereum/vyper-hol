Theory requestCutPacketRootResult
Ancestors
  requestCutPacketExecution dftFinitePacket dftIndexedExec gasEvents
  venomExecSemantics venomState list pair

(* The packet's event accumulation leaves its execution result unchanged. *)
Theorem request_cut_packet_root_result:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  !fuel C levels entry.
    SND (rooted_eval fuel C levels entry) =
    FOLDL (\r (sf,plan,call). case r of
      OK ent =>
        (case FOLDL (\v (bb,e,z). case v of
          OK s =>
            (case eval_phis s bb.bb_instructions of
             OK sp => FOLDR (dft_exec_cons (fuel-e) C) OK z
                        (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
             | other => other)
          | other => other) (OK ent) plan of
          OK caller => (case call of NONE => OK caller | SOME c =>
            (case decode_invoke c of
              NONE => Error "invoke: bad operand format"
            | SOME (nm,ops) =>
              (case lookup_function nm C.ctx_functions of
                NONE => Error "invoke: function not found"
              | SOME callee =>
                (case eval_operands ops caller of
                  NONE => Error "invoke: undefined argument"
                | SOME args =>
                  (case setup_callee callee args caller of
                    NONE => Error "invoke: empty function" | SOME cs => OK cs)))))
        | other => other)
     | other => other) (OK entry) levels
Proof
  rewrite_tac[dft_focus_packet_rel_def] >> strip_tac >>
  rpt gen_tac >>
  `!owner plan ent.
    SND (plan_eval fuel C owner plan ent) =
    FOLDL (\v (bb,e,z). case v of
      OK s =>
        (case eval_phis s bb.bb_instructions of
         OK sp => FOLDR (dft_exec_cons (fuel-e) C) OK z
                    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
         | other => other)
      | other => other) (OK ent) plan` by
    suspend "plan_result" >>
  suspend "level_result"
QED

Resume request_cut_packet_root_result[plan_result]:
  rpt gen_tac >>
  qpat_assum `plan_eval = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  `(\v row. case v of OK s => SND (row_eval fuel C owner row s) | other => other) =
    (\v (bb,e,z). case v of OK s =>
      (case eval_phis s bb.bb_instructions of
       OK sp => FOLDR (dft_exec_cons (fuel-e) C) OK z
                 (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
       | other => other)
     | other => other)` by
    (simp[Once FUN_EQ_THM] >> gen_tac >>
     simp[Once FUN_EQ_THM] >> qx_gen_tac `row` >> PairCases_on `row` >>
     qpat_assum `row_eval = _` (fn th => simp[NoAsms,th]) >>
     Cases_on `v` >> simp[NoAsms] >>
     BasicProvers.TOP_CASE_TAC >> simp[NoAsms]) >>
  qpat_assum `(\v row. case v of OK s => SND (row_eval fuel C owner row s) | _ => _) = _`
    (fn th => simp_tac bool_ss [GSYM th]) >>
  MATCH_ACCEPT_TAC (BETA_RULE (Q.ISPEC `row_eval fuel C owner :
    (basic_block # num # instruction list) -> venom_state -> (string # num) list # exec_result`
    request_cut_plan_fold_result))
QED

Resume request_cut_packet_root_result[level_result]:
  rename1 `SND (rooted_eval fuel C levels init) = _` >>
  qabbrev_tac `level_eval = (\(sf,plan,call) ent.
    (FST (plan_eval fuel C sf.fn_name plan ent),
      case SND (plan_eval fuel C sf.fn_name plan ent) of
        OK caller => (case call of NONE => OK caller | SOME c => call_setup C c caller)
      | other => other))` >>
  `SND (rooted_eval fuel C levels init) =
    SND (FOLDL (\(prior,r) level. case r of
      OK ent => (prior ++ FST (level_eval level ent), SND (level_eval level ent))
      | other => (prior,other)) ([],OK init) levels)` by
    (qpat_assum `rooted_eval = _` (fn th => simp[NoAsms,th]) >>
     AP_TERM_TAC >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
     once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `input` >> PairCases_on `input` >>
     once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `level` >> PairCases_on `level` >>
     Cases_on `input1` >> simp[Abbr `level_eval`]) >>
  qpat_assum `SND (rooted_eval fuel C levels init) = _` SUBST1_TAC >>
  `SND (FOLDL (\(prior,r) level. case r of
      OK ent => (prior ++ FST (level_eval level ent), SND (level_eval level ent))
      | other => (prior,other)) ([],OK init) levels) =
    FOLDL (\r level. case r of OK ent => SND (level_eval level ent)
      | other => other) (OK init) levels` by
    MATCH_ACCEPT_TAC (Q.ISPEC `level_eval :
      (ir_function # (basic_block # num # instruction list) list # instruction option) ->
      venom_state -> (string # num) list # exec_result` request_cut_plan_fold_result) >>
  pop_assum SUBST1_TAC >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
  simp[Once FUN_EQ_THM] >> gen_tac >>
  once_rewrite_tac[FUN_EQ_THM] >> qx_gen_tac `level` >> PairCases_on `level` >>
  simp[NoAsms,Abbr `level_eval`] >>
  qpat_assum `call_setup = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!owner plan ent. SND (plan_eval fuel C owner plan ent) = _`
    (fn th => rewrite_tac[th]) >>
  BasicProvers.TOP_CASE_TAC >> simp[NoAsms]
QED

Finalise request_cut_packet_root_result

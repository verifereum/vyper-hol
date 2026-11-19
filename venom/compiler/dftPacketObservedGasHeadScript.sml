Theory dftPacketObservedGasHead
Ancestors
  dftGasFromListTraceDefs dftGasFromListReadings gasCount gasOracleReplay
  venomState venomExecSemantics venomInst list rich_list arithmetic

(* A later visit starts after the events of the whole first segment. *)
Theorem visit_readings_append[local]:
  !xs ys rs.
    (!n. n < LENGTH xs ==>
      (SND (SND (SND (EL n xs)))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n xs))) rs) /\
    (!n. n < LENGTH ys ==>
      (SND (SND (SND (EL n ys)))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n ys)))
        (DROP (LENGTH (trace_gas xs)) rs)) ==>
    !n. n < LENGTH (xs ++ ys) ==>
      (SND (SND (SND (EL n (xs ++ ys))))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n (xs ++ ys)))) rs
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `n < LENGTH xs`
  >- simp[EL_APPEND_EQN, listTheory.TAKE_APPEND1] >>
  `LENGTH xs <= n /\ n - LENGTH xs < LENGTH ys` by (fs[] >> decide_tac) >>
  simp[EL_APPEND_EQN, rich_listTheory.TAKE_APPEND2, DROP_DROP_T, ADD_COMM]
QED

Theorem trace_visit_readings[local]:
  (!p d fuel ctx fn inst s.
    !n. n < LENGTH (((p,d,inst.inst_id),fn,inst,s)::
                     trace_step p d fuel ctx fn inst s) ==>
      (SND (SND (SND (EL n (((p,d,inst.inst_id),fn,inst,s)::
                            trace_step p d fuel ctx fn inst s))))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n (((p,d,inst.inst_id),fn,inst,s)::
                                       trace_step p d fuel ctx fn inst s)))) s.vs_gas_readings) /\
  (!p d fuel ctx fn bb s.
    !n. n < LENGTH (trace_block p d fuel ctx fn bb s) ==>
      (SND (SND (SND (EL n (trace_block p d fuel ctx fn bb s))))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n (trace_block p d fuel ctx fn bb s)))) s.vs_gas_readings) /\
  (!p d fuel ctx fn s.
    !n. n < LENGTH (trace_blocks p d fuel ctx fn s) ==>
      (SND (SND (SND (EL n (trace_blocks p d fuel ctx fn s))))).vs_gas_readings =
      DROP (LENGTH (trace_gas (TAKE n (trace_blocks p d fuel ctx fn s)))) s.vs_gas_readings)
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_visit_readings[step]:
  rpt gen_tac >> strip_tac >> Cases >>
  simp[Once (cj 1 trace_defs), visit_gas_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 ctx.ctx_functions` >> simp[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> simp[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> simp[] >>
  drule_all_then assume_tac trace_step_invoke >>
  drule gas_setup_callee_readings >> simp[] >> metis_tac[]
QED

Resume trace_visit_readings[block]:
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once (cj 2 trace_defs)] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  `trace_block p d fuel ctx fn bb s =
     (((p,d,inst.inst_id),fn,inst,s)::trace_step p d fuel ctx fn inst s) ++
     (case step_inst fuel ctx inst s of
        OK t => if is_terminator inst.inst_opcode then []
                else trace_block p d fuel ctx fn bb
                      (t with vs_inst_idx := SUC s.vs_inst_idx)
      | _ => [])` by simp[Once (cj 2 trace_defs)] >>
  once_asm_rewrite_tac[] >> match_mp_tac visit_readings_append >>
  conj_tac >- metis_tac[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK t` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  `t.vs_gas_readings = DROP (gas_count_step fuel ctx inst s) s.vs_gas_readings` by
    (mp_tac (Q.SPECL [`fuel`,`ctx`,`inst`,`s`] (cj 1 gas_count_suffix)) >>
     simp[gas_count_suffix_def]) >>
  mp_tac (Q.SPECL [`p`,`d`,`fuel`,`ctx`,`fn`,`inst`,`s`] (cj 1 trace_gas_lengths)) >>
  simp[ADD_COMM]
QED

Resume trace_visit_readings[blocks]:
  rpt gen_tac >> strip_tac >> Cases_on `fuel` >- simp[] >>
  rename1 `SUC k` >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs)] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  reverse (Cases_on `eval_phis s bb.bb_instructions`)
  >- simp[Once (cj 3 trace_defs)]
  >- simp[Once (cj 3 trace_defs)]
  >- simp[Once (cj 3 trace_defs)]
  >- simp[Once (cj 3 trace_defs)] >>
  rename1 `eval_phis _ _ = OK sp` >>
  `sp.vs_gas_readings = s.vs_gas_readings` by metis_tac[gas_count_phis_ok] >>
  `trace_blocks p d (SUC k) ctx fn s =
     trace_block p (SUC d) k ctx fn bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++
     (case run_block_non_phis k ctx bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) of
        OK t => if t.vs_halted then [] else trace_blocks p (SUC d) k ctx fn t
      | _ => [])` by simp[Once (cj 3 trace_defs)] >>
  once_asm_rewrite_tac[] >> match_mp_tac visit_readings_append >>
  conj_tac >- gvs[] >>
  Cases_on `run_block_non_phis k ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  rename1 `run_block_non_phis _ _ _ _ = OK t` >>
  Cases_on `t.vs_halted` >> simp[] >>
  `t.vs_gas_readings = DROP
     (gas_count_block k ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
     s.vs_gas_readings` by
    (mp_tac (Q.SPECL [`k`,`ctx`,`bb`,
       `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] (cj 2 gas_count_suffix)) >>
     simp[gas_count_suffix_def]) >>
  simp[cj 2 trace_gas_lengths] >> metis_tac[]
QED

Finalise trace_visit_readings

Theorem dft_packet_observed_gas_head:
  R = trace_blocks [] 0 N C8 root_tf root_entry /\
  obs = trace_gas (TAKE j R) /\
  LENGTH obs <= LENGTH root_entry.vs_gas_readings /\
  MEM (key,tf,i,u) (TAKE j R) /\ i.inst_opcode = GAS ==>
  u.vs_gas_readings <> [] /\ MEM (key,HD u.vs_gas_readings) obs
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qpat_x_assum `MEM _ (TAKE j R)` (mp_tac o REWRITE_RULE[MEM_EL]) >>
  disch_then (qx_choose_then `k` strip_assume_tac) >>
  `k < j /\ k < LENGTH R` by
    (Cases_on `j <= LENGTH R` >> fs[listTheory.LENGTH_TAKE_EQ] >> (gvs[])) >>
  `EL k R = (key,tf,i,u)` by metis_tac[listTheory.EL_TAKE] >>
  `u.vs_gas_readings = DROP (LENGTH (trace_gas (TAKE k R))) root_entry.vs_gas_readings` by
    (qpat_x_assum `(_,_,_,_) = EL k (TAKE j R)` kall_tac >>
     mp_tac (Q.SPECL [`[]`,`0`,`N`,`C8`,`root_tf`,`root_entry`,`k`]
               (cj 3 trace_visit_readings)) >> gvs[]) >>
  `TAKE j R = TAKE k R ++ (key,tf,i,u)::DROP (SUC k) (TAKE j R)` by
    (`k <= j` by decide_tac >>
     qspecl_then [`k`,`TAKE j R`] mp_tac TAKE_DROP >>
     metis_tac[TAKE_TAKE_T,DROP_CONS_EL,listTheory.EL_TAKE]) >>
  `obs = trace_gas (TAKE k R) ++ visit_gas (key,tf,i,u) ++
         trace_gas (DROP (SUC k) (TAKE j R))` by
    (qpat_assum `obs = _` SUBST1_TAC >>
     qpat_assum `TAKE j R = _` (fn th =>
       CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[trace_gas_def]) >>
  Cases_on `u.vs_gas_readings` >> fs[visit_gas_def,DROP_EQ_NIL]
QED

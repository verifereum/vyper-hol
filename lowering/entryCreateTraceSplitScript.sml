(* A completed origin prefix identifies a suffix of the same native run. *)
Theory entryCreateTraceSplit
Ancestors
  entryCreateNativeResume fragGasOrigin fragExec venomExecProofs
  venomInstProofs venomExecSemantics venomInst venomState
  dftGasFromListTraceDefs list arithmetic

Theorem create_trace_from_jump[local]:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  is_terminator i.inst_opcode /\ step_inst (SUC k) C i s = OK u /\
  ~u.vs_halted /\ lookup_block u.vs_current_bb f.fn_blocks = SOME dest /\
  eval_phis u dest.bb_instructions = OK t ==>
  create_trace_from p d (SUC k) C f s =
    ((p,d,i.inst_id),f,i,s) ::
      (trace_step p d (SUC k) C f i s ++
       create_trace_from p (SUC d) k C f
         (t with vs_inst_idx := phi_prefix_length dest.bb_instructions))
Proof
  strip_tac >>
  `t.vs_current_bb = u.vs_current_bb` by metis_tac[eval_phis_preserves_current_bb] >>
  simp[create_trace_from_def] >>
  drule_all_then (fn th => ONCE_REWRITE_TAC[th]) trace_block_visit >>
  simp[Once exec_block_def] >>
  drule_all_then (fn th => ONCE_REWRITE_TAC[th]) trace_blocks_enter >>
  simp[]
QED

Theorem create_trace_from_edge[local]:
  gas_origin_edge mem E C f s marks (OK t) /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) ==>
  ?bound. !k p d. bound <= k ==>
    ?left dd kk. create_trace_from p d k C f s =
      left ++ create_trace_from p dd kk C f t /\ k <= SUC kk /\ kk <= k
Proof
  rw[gas_origin_edge_def] >> gvs[exit_result_def]
  >- suspend "next"
  >- suspend "entered"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel C inst s` >> gvs[exit_result_def])
QED

Resume create_trace_from_edge[next]:
  qexists_tac `fuel` >> rpt strip_tac >>
  `step_inst k C inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> metis_tac[]) >>
  `t'.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  drule_all create_trace_from_next >> strip_tac >>
  qexistsl_tac [`((p,d,inst.inst_id),f,inst,s)::trace_step p d k C f inst s`, `d`, `k`] >> simp[]
QED

Resume create_trace_from_edge[entered]:
  qexists_tac `SUC fuel` >> rpt strip_tac >> Cases_on `k` >> gvs[] >>
  rename1 `fuel <= k` >>
  `step_inst (SUC k) C inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  drule_all create_trace_from_jump >> strip_tac >>
  qexistsl_tac [`((p,d,inst.inst_id),f,inst,s)::trace_step p d (SUC k) C f inst s`, `SUC d`, `k`] >> simp[]
QED

Resume create_trace_from_edge[jump]:
  qexists_tac `1` >> rpt strip_tac >> Cases_on `k` >> gvs[] >>
  qmatch_goalsub_rename_tac `create_trace_from p d (SUC k) C f s` >>
  Cases_on `lookup_block lbl f.fn_blocks` >> gvs[]
  >- (qexistsl_tac [`create_trace_from p d (SUC k) C f s`, `d`, `SUC k`] >>
      simp[create_trace_from_def, jump_to_def]) >>
  rename1 `lookup_block lbl f.fn_blocks = SOME dest` >>
  `phi_prefix_length dest.bb_instructions = 0` by metis_tac[lookup_block_MEM] >>
  `eval_phis (jump_to lbl s) dest.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  `step_inst (SUC k) C inst s = OK (jump_to lbl s)` by gvs[step_inst_non_invoke] >>
  `((jump_to lbl s) with vs_inst_idx := 0) = jump_to lbl s` by simp[jump_to_def] >>
  `lookup_block (jump_to lbl s).vs_current_bb f.fn_blocks = SOME dest /\
    ~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  drule_all create_trace_from_jump >> strip_tac >>
  qexistsl_tac [`[((p,d,inst.inst_id),f,inst,s)]`, `SUC d`, `k`] >>
  simp[trace_step_noninvoke]
QED
Finalise create_trace_from_edge

(* Increasing the initial fuel to cover the completed prefix does not
   reselect any instruction: each edge agrees at every larger fuel. *)
Theorem create_trace_from_completed_min:
  !m. gas_origin_path mem E C f s marks (OK t) /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) ==>
  ?bound. !k p d. bound <= k ==>
    ?left dd kk. create_trace_from p d k C f s =
      left ++ create_trace_from p dd kk C f t /\ m <= kk /\ kk <= k
Proof
  gen_tac >>
  `!mem E C f s marks res. gas_origin_path mem E C f s marks res ==>
    !t. res = OK t /\
    (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) ==>
    ?bound. !k p d. bound <= k ==>
      ?left dd kk. create_trace_from p d k C f s =
        left ++ create_trace_from p dd kk C f t /\ m <= kk /\ kk <= k`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> qexists_tac `m` >>
      rpt strip_tac >> qexistsl_tac [`[]`, `d`, `k`] >> simp[])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> gvs[] >>
      drule_all create_trace_from_edge >>
      disch_then (qx_choose_then `b1` (mk_asm "edge")) >>
      qexists_tac `MAX b1 (SUC bound)` >> rpt strip_tac >>
      `b1 <= k /\ SUC bound <= k` by fs[MAX_LE] >>
      asm "edge" (qspecl_then [`k`, `p`, `d`] mp_tac) >> simp[] >>
      disch_then (qx_choosel_then [`l1`, `d1`, `k1`] strip_assume_tac) >>
      `bound <= k1` by decide_tac >>
      qpat_x_assum `!k p d. bound <= k ==> _`
        (qspecl_then [`k1`, `p`, `d1`] mp_tac) >> simp[] >>
      disch_then (qx_choosel_then [`l2`, `d2`, `k2`] strip_assume_tac) >>
      qexistsl_tac [`l1 ++ l2`, `d2`, `k2`] >> simp[APPEND_ASSOC] >> decide_tac) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem create_trace_from_completed:
  gas_origin_path mem E C f s marks (OK t) /\
  (!b. MEM b f.fn_blocks ==> phi_prefix_length b.bb_instructions = 0) ==>
  ?bound. !k p d. bound <= k ==>
    ?left dd kk. create_trace_from p d k C f s =
      left ++ create_trace_from p dd kk C f t /\ kk <= k
Proof
  metis_tac[Q.SPEC `0` create_trace_from_completed_min]
QED

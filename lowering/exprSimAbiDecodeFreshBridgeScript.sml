Theory exprSimAbiDecodeFreshBridge
Ancestors
  exprSimAbiDecodeFreshTransfer exprSimAbiDecodeFreshEdgeProbe
  exprSimAbiDecodeFreshBoundary exprSimAbiGasBridge fragExec fragGasPath
  gasCount fragGasMode abiEncoderObserver instIdxIndep venomExecSemantics venomState
  venomInst list

Theorem abi_decode_fresh_frag_exec_gas_path_edge:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       L <> sb.cs_current_bb /\
       ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
       EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
       frag_gas_free (start_relabel L ids sa) (start_swap sa L ids sb) /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <|vs_current_bb := b; vs_prev_bb := p|>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <|vs_current_bb := b; vs_prev_bb := p|>))) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `abi_decode_fresh_context sa sb L ids fn` by simp[abi_decode_fresh_context_def] >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `((s with vs_current_bb := L).vs_current_bb,
     (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume abi_decode_fresh_frag_exec_gas_path_edge[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_relabel_observer sa sb L ids fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule abi_decode_fresh_halt_prefix >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule abi_decode_fresh_prefix_path >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  disj1_tac >> qexists_tac `v` >>
  gvs[gas_marked_path_def, frag_observer_cut_def]
QED

Resume abi_decode_fresh_frag_exec_gas_path_edge[exit]:
  qmatch_asmsub_abbrev_tac `R r` >>
  `!h. r <> Halt h` by metis_tac[] >>
  `?b p. gas_path ctx fn s 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)` by
    (irule abi_decode_fresh_exit_path >>
     simp[Abbr `r`] >>
     qpat_assum `abi_decode_fresh_context _ _ _ _ _`
       (irule_at (Pat `abi_decode_fresh_context _ _ _ _ _`)) >>
     qexistsl_tac [`s with vs_current_bb := L`, `id`, `fuel`] >> gvs[]) >>
  disj2_tac >>
  qexists_tac `exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r` >>
  simp[gas_marked_path_def] >>
  Cases_on `r` >> gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  metis_tac[]
QED

Finalise abi_decode_fresh_frag_exec_gas_path_edge

Theory exprSimAbiDecodeRestrictedBridge
Ancestors
  exprSimAbiGasBridge fragExec fragGasPath venomExecSemantics venomState
  venomInst compileEnv list gasCount abiEncoderObserver fragGasMode

(* Only observer functions contained in the counted function need execute the
   fragment.  The extra NOP exclusion matches lower_abi_decode_outcome. *)
Theorem abi_decode_restricted_gas_path:
  !ctx sa sb P Q R fn s.
    (!fn' u. fn_has_code sa sb fn' /\ fn_inst_ids_distinct fn' /\
       fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) /\
       P u /\ ~u.vs_halted /\ u.vs_current_bb = sa.cs_current_bb /\
       u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' u = r) \/
       (?fuel r. run_from fuel ctx fn' u = r /\ exit_result r /\ R r)) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
     !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
    P s /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?id. !inst. MEM inst (fn_insts fn) ==> inst.inst_id <> id` by
    metis_tac[frag_observer_fresh_id] >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  qpat_x_assum `!fn' u. _`
    (qspecl_then [`frag_observer sa sb fn id`, `s`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac
      >- metis_tac[frag_observer_has_code]
      >- metis_tac[frag_observer_ids_distinct]
      >- simp[frag_observer_def]
      >- metis_tac[frag_observer_nonstop_inclusion]
      >- metis_tac[frag_observer_end_phi_zero] >> simp[]) >>
  strip_tac >- suspend "normal" >> suspend "exit"
QED

Resume abi_decode_restricted_gas_path[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_observer sa sb fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `gas_path ctx fn s 0 (OK u)` by
    (drule frag_observer_prefix_zero_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  disj1_tac >> qexists_tac `u` >>
  simp[gas_marked_path_def] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED

Resume abi_decode_restricted_gas_path[exit]:
  disj2_tac >> qexists_tac `run_from fuel ctx (frag_observer sa sb fn id) s` >>
  simp[gas_marked_path_def] >>
  irule frag_observer_exit_path >> metis_tac[]
QED

Finalise abi_decode_restricted_gas_path

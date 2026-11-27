(* Compose observations of the selected decoder run at a colliding caller cut. *)
Theory bodyAbiDecodeLinkedCollisionMods
Ancestors
  bodyFullAbiDecodeCutPath exprSimAbiGasBridge abiEncoderObserver fragExec
  venomExecSemantics

(* A prefix may end at the temporary setup cursor or at the final cursor.
   In both cases, only the continuation observes the terminal instruction. *)
Theorem prepend_decode_observation[local]:
  local_prefix ctx obs cut s u /\ run_from fuel ctx obs u = r /\
  (!e. r <> Error e) ==>
  ?k. run_from k ctx obs s = r
Proof
  metis_tac[abi_decode_cut_prefix_run]
QED

Theorem abi_decode_linked_collision_certificate_mods:
  let obs = frag_relabel_observer start final L ids func id;
      sL = s with vs_current_bb := L
  in
    start.cs_blocks <> final.cs_blocks /\ start.cs_current_bb = final.cs_current_bb /\
    LENGTH ids = LENGTH start.cs_current_insts /\ L <> final.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
    frag_gas_free (start_relabel L ids start) (start_swap start L ids final) /\
    fn_has_code (start_relabel L ids start) (start_swap start L ids final) obs /\
    fn_inst_ids_distinct obs /\
    (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
      MEM i (fn_insts func)) /\
    (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
    (!bb. lookup_block final.cs_current_bb obs.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    ((r = r0 /\
      (?z w k. r0 = Abort Revert_abort z /\
        frag_relabel_state L start.cs_current_bb w z /\
        run_from k ctx obs sL = Abort Revert_abort w)) \/
     (r0 = OK u /\ frag_relabel_state L start.cs_current_bb u_shadow u /\
      local_prefix ctx obs (L,LENGTH ready.cs_current_insts) sL u_shadow /\
      ((?t w. r = OK t /\ ~w.vs_halted /\
          (w.vs_current_bb,w.vs_inst_idx) = frag_observer_cut final /\
          frag_relabel_state L start.cs_current_bb w t /\
          local_prefix ctx obs (frag_observer_cut final) u_shadow w) \/
       (?z w k. r = Abort Revert_abort z /\
          frag_relabel_state L start.cs_current_bb w z /\
          run_from k ctx obs u_shadow = Abort Revert_abort w)))) ==>
    ?L ids id.
      let obs = frag_relabel_observer start final L ids func id;
          sL = s with vs_current_bb := L
      in
        LENGTH ids = LENGTH start.cs_current_insts /\ L <> final.cs_current_bb /\
        ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
        EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
        frag_gas_free (start_relabel L ids start) (start_swap start L ids final) /\
        fn_has_code (start_relabel L ids start) (start_swap start L ids final) obs /\
        fn_inst_ids_distinct obs /\
        (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
        (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
        (!bb. lookup_block final.cs_current_bb obs.fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
        ((?t w k. r = OK t /\ ~w.vs_halted /\
           (w.vs_current_bb,w.vs_inst_idx) = frag_observer_cut final /\
           frag_relabel_state L start.cs_current_bb w t /\
           run_from k ctx obs sL = Halt (stop_view w)) \/
         (?z w k. r = Abort Revert_abort z /\
           frag_relabel_state L start.cs_current_bb w z /\
           run_from k ctx obs sL = Abort Revert_abort w))
Proof
  simp_tac pure_ss [LET_THM, BETA_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`L`,`ids`,`id`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `(_ /\ (?z w k. r0 = Abort Revert_abort z /\ _)) \/ _`
    (DISJ_CASES_THEN2
      (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `z` (qx_choose_then `w` (qx_choose_then `k` strip_assume_tac))))
      (map_every assume_tac o CONJUNCTS))
  >- (disj2_tac >> qexistsl [`z`,`w`,`k`] >> simp[]) >>
  qpat_x_assum `(?t w. r = OK t /\ _) \/ _`
    (DISJ_CASES_THEN2
       (qx_choose_then `t` (qx_choose_then `w` strip_assume_tac))
       (qx_choose_then `z` (qx_choose_then `w` (qx_choose_then `k` strip_assume_tac))))
  >- (disj1_tac >> qexistsl [`t`,`w`] >>
      `run_from 0 ctx (frag_relabel_observer start final L ids func id) w =
       Halt (stop_view w)` by
        (irule run_from_stop_view >>
         qexistsl [`<|bb_label := final.cs_current_bb;
                      bb_instructions := final.cs_current_insts ++ [mk_inst id STOP [] []]|>`,
                   `id`] >>
         qpat_assum `(w.vs_current_bb,w.vs_inst_idx) = frag_observer_cut final` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[frag_observer_cut_def] >> strip_tac >>
         simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
      `?k. run_from k ctx (frag_relabel_observer start final L ids func id) u_shadow =
           Halt (stop_view w)` by
        (qpat_assum `local_prefix _ _ (frag_observer_cut final) u_shadow w` mp_tac >>
         qpat_assum `run_from 0 _ _ w = Halt _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[prepend_decode_observation, exec_result_distinct]) >>
      `?k. run_from k ctx (frag_relabel_observer start final L ids func id)
          (s with vs_current_bb := L) = Halt (stop_view w)` by
        (qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u_shadow` mp_tac >>
         qpat_assum `run_from _ _ _ u_shadow = Halt _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[prepend_decode_observation, exec_result_distinct]) >>
      rename1 `run_from fuel_all _ _ (s with vs_current_bb := L) = Halt _` >>
      qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`z`,`w`] >>
  `?k. run_from k ctx (frag_relabel_observer start final L ids func id)
       (s with vs_current_bb := L) = Abort Revert_abort w` by
    (qpat_assum `local_prefix _ _ (L,LENGTH ready.cs_current_insts) _ u_shadow` mp_tac >>
     qpat_assum `run_from k _ _ u_shadow = Abort Revert_abort w` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[prepend_decode_observation, exec_result_distinct]) >>
  rename1 `run_from fuel_all _ _ (s with vs_current_bb := L) = Abort Revert_abort _` >>
  qexists `fuel_all` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

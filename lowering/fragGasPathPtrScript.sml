(* Counted fragment paths carrying the ghost and the pointer check of each
 * step: gas_path_mem with ptrSafeRun's ptr_safe_step in place of the
 * memory check, and no revert-forward exemption.  The ghost follows each
 * edge as ghost_block threads it: ghost_step past an instruction, the
 * block-entry ghost past a terminator that enters a block, and unchanged
 * where the run stops or jumps to a block start (a run that goes on from
 * there finds no PHIs, where the entry ghost is the ghost).
 *
 * TOP-LEVEL:
 *   gas_path_ptr_edge, gas_path_ptr -- the edges and paths, with the ghost
 *     before and after
 *   gas_summary_ptr_at, gas_outcome_ptr -- gas_summary_at and gas_outcome
 *     over gas_path_ptr; Q and R see the ghost where the path stops
 *   gas_path_ptr_erase, gas_path_ptr_then -- dropping the check, and
 *     sequencing
 *)
Theory fragGasPathPtr
Ancestors
  gasExemptCert gasSummary fragGasPath gasCount fragExec ptrSafeRun
  ptrDiscipline venomExecSemantics venomExecProofs venomInstProofs
  venomState vyperState arithmetic list

Definition gas_path_ptr_edge_def:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
      ptr_safe_step D lo fuel ctx fn PG G tn inst s /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx) /\
            (G', tn') = ghost_step fuel ctx PG G tn inst s) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t /\ G' = G /\ tn' = tn) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions) /\
          G' = entry_prov fn t G /\ tn' = entry_taint_vars fn t tn) \/
       (?lbl. is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
              middle = OK (jump_to lbl s) /\ r = middle /\
              G' = G /\ tn' = tn) \/
       (exit_result middle /\ r = middle /\ G' = G /\ tn' = tn))
End

Inductive gas_path_ptr:
  (!D lo ctx fn PG G tn s.
     ~s.vs_halted ==> gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK s)) /\
  (!D lo ctx fn PG G tn s n G1 tn1 t m G' tn' r.
     gas_path_ptr_edge D lo ctx fn PG G tn s n G1 tn1 (OK t) /\
     gas_path_ptr D lo ctx fn PG G1 tn1 t m G' tn' r ==>
     gas_path_ptr D lo ctx fn PG G tn s (n + m) G' tn' r) /\
  (!D lo ctx fn PG G tn s n G' tn' r.
     gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r /\ exit_result r ==>
     gas_path_ptr D lo ctx fn PG G tn s n G' tn' r)
End

(* gas_summary_at over gas_path_ptr from the ghost (G0, tn0) at s0: Q sees
   the ghost where the path continues, R the ghost where it stops. *)
Definition gas_summary_ptr_at_def:
  gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q R <=>
    ?res es_end G tn r.
      (!tail.
         source (es with gas_obs :=
                   gas_explicit marks s0.vs_gas_readings ++ tail) =
           (res, es_end with gas_obs := tail)) /\
      gas_path_ptr D 0 ctx func PG G0 tn0 s0 (LENGTH marks) G tn r /\
      ((?t. r = OK t /\ Q res (es_end with gas_obs := []) G tn t) \/
       (exit_result r /\ R res (es_end with gas_obs := []) (G, tn) r))
End

(* gas_outcome with the pointer check on the completed path.  An exempt
   execution claims nothing about pointers: the entry's composition rules
   it out with ~source_exempt. *)
Definition gas_outcome_ptr_def:
  gas_outcome_ptr D tops (ctx, func) PG source (es, s0, G0, tn0) Q R <=>
    ?marks.
      gas_summary_ptr_at D (ctx, func) PG marks source (es, s0, G0, tn0) Q R \/
      ?err ee leaf finish.
        gas_exempt_cert F tops (ctx, func) (ignore_bind source (return ()))
          (es, s0) marks (err, ee) (leaf, finish)
End

Theorem gas_path_ptr_edge_erase:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  gas_path_edge ctx fn s n r
Proof
  rw[gas_path_ptr_edge_def, gas_path_edge_def] >>
  metis_tac[]
QED

Theorem gas_path_ptr_erase:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    gas_path ctx fn s n r
Proof
  ho_match_mp_tac gas_path_ptr_ind >>
  metis_tac[gas_path_rules, gas_path_ptr_edge_erase]
QED

Theorem gas_path_ptr_then:
  gas_path_ptr D lo ctx fn PG G tn s n G1 tn1 (OK t) /\
  gas_path_ptr D lo ctx fn PG G1 tn1 t m G' tn' r ==>
  gas_path_ptr D lo ctx fn PG G tn s (n + m) G' tn' r
Proof
  `!D lo ctx fn PG G tn s n G1 tn1 res.
     gas_path_ptr D lo ctx fn PG G tn s n G1 tn1 res ==>
     !t m G' tn' r.
       res = OK t /\ gas_path_ptr D lo ctx fn PG G1 tn1 t m G' tn' r ==>
       gas_path_ptr D lo ctx fn PG G tn s (n + m) G' tn' r`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      drule (cj 2 gas_path_ptr_rules) >>
      disch_then drule >> simp[AC ADD_ASSOC ADD_COMM])
  >> rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

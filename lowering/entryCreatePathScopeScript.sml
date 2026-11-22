(* Confinement on the caller spine. No lemma extends a prefix through the
   enclosing exit: at that PC the fetch must be outside the lifted band. *)
Theory entryCreatePathScope
Ancestors
  entryCreateCompletedCut entryCreateOperandReplay createSizePrefixReplay
  createMarkedPath createSizeCutRegion createSizeCutCode bodySim
  abiEncoderProps fragExec fragGasOrigin compileEnv venomState
  venomExecSemantics venomInst relation pair list pred_set arithmetic

Theorem create_prefix_step_lift:
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids x y) /\
  create_prefix_step x y explicit ctx fn s ms t ==>
  create_prefix_step a b explicit ctx fn s ms t
Proof
  rewrite_tac[create_prefix_step_def] >> strip_tac >>
  rename1 `get_instruction _ s.vs_inst_idx = SOME i` >>
  `s.vs_current_bb <> b.cs_current_bb \/
   s.vs_inst_idx <> LENGTH b.cs_current_insts` by
    (CCONTR_TAC >> gvs[] >> metis_tac[]) >>
  `i.inst_id IN frag_ids a b` by (fs[frag_ids_def] >> decide_tac) >>
  metis_tac[]
QED

(* Reuse the generic monotonicity law on the marked RTC, so the same marks
   are retained even when one caller edge records events in a callee. *)
Theorem create_expr_prefix_mono:
  create_expr_prefix x y explicit ctx fn s ms t /\
  (!p chunk q. create_prefix_step x y explicit ctx fn p chunk q ==>
               create_prefix_step a b explicit ctx fn p chunk q) ==>
  create_expr_prefix a b explicit ctx fn s ms t
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  irule RTC_MONOTONE >>
  first_assum (irule_at Any) >>
  simp[FORALL_PROD,create_marked_edge_def] >> metis_tac[]
QED

Theorem create_expr_prefix_lift:
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  (!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids x y) /\
  create_expr_prefix x y explicit ctx fn s ms t ==>
  create_expr_prefix a b explicit ctx fn s ms t
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >> metis_tac[create_prefix_step_lift]
QED

Theorem create_expr_prefix_nil[simp]:
  create_expr_prefix a b explicit ctx fn s [] s
Proof
  simp[create_expr_prefix_marked]
QED

Theorem create_expr_prefix_append:
  create_expr_prefix a b explicit ctx fn s left u /\
  create_expr_prefix a b explicit ctx fn u right t ==>
  create_expr_prefix a b explicit ctx fn s (left ++ right) t
Proof
  simp[create_expr_prefix_marked] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (mp_tac o MATCH_MP create_marked_rtc_rebase)) >>
  disch_then (qspec_then `left` mp_tac) >> simp[] >> metis_tac[RTC_TRANS]
QED

Theorem create_expr_prefix_join:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  (!bb i. lookup_block c.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH c.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) /\
  create_expr_prefix a b explicit ctx fn s left u /\
  create_expr_prefix b c explicit ctx fn u right t ==>
  create_expr_prefix a c explicit ctx fn s (left ++ right) t
Proof
  strip_tac >>
  `create_expr_prefix a c explicit ctx fn s left u` by
    metis_tac[create_expr_prefix_lift,LESS_EQ_REFL] >>
  `create_expr_prefix a c explicit ctx fn u right t` by
    (irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
     simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]) >>
  metis_tac[create_expr_prefix_append]
QED

Theorem create_operand_full_scope_terminal:
  exit_result r /\ create_expr_prefix a b explicit ctx fn s left u /\
  (u.vs_current_bb <> b.cs_current_bb \/
   u.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  gas_origin_edge T explicit ctx fn u last r ==>
  create_operand_full_scope a b explicit ctx fn s (left ++ last) r
Proof
  Cases_on `r` >>
  simp[create_operand_full_scope_def,exit_result_def] >> metis_tac[]
QED

(* In the successful branch the right segment ends at c. In each terminal
   branch we join only the successful spine; the final edge stays separate. *)
Theorem create_operand_full_scope_prepend:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  (!bb i. lookup_block c.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH c.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) /\
  create_operand_full_scope a b explicit ctx fn s left (OK u) /\
  create_operand_full_scope b c explicit ctx fn u right r ==>
  create_operand_full_scope a c explicit ctx fn s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac
  >- metis_tac[create_expr_prefix_join] >>
  rename1 `right = front ++ last` >>
  rename1 `create_expr_prefix b c explicit ctx fn u front stop` >>
  `create_expr_prefix a c explicit ctx fn s (left ++ front) stop` by
    metis_tac[create_expr_prefix_join] >>
  metis_tac[APPEND_ASSOC]
QED

(* Region preservation is for the actual confined spine. It supplies the
   region premise at the terminal instruction without running that edge. *)
Theorem create_expr_prefix_cut_region:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b fn /\
  create_cut_region a b s /\ create_expr_prefix a b explicit ctx fn s ms t ==>
  create_cut_region a b t
Proof
  strip_tac >> irule RTC_lifts_invariants >>
  qexists_tac `\p q. ?chunk. create_prefix_step a b explicit ctx fn p chunk q` >>
  qexists_tac `s` >> simp[] >> conj_tac
  >- (simp[PULL_EXISTS] >> rpt strip_tac >>
      qpat_assum `create_prefix_step _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[create_prefix_step_def]) >>
      metis_tac[operand_cut_region_edge]) >>
  drule create_expr_prefix_rtc_project >>
  disch_then irule >> metis_tac[]
QED

(* When the left segment terminates, no right segment is executed. Besides
   the embedding of successful edges, check its stop against the outer cut. *)
Theorem create_operand_full_scope_lift_terminal:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} x y /\ fn_has_code x y fn /\ create_cut_region x y s /\
  (!p chunk q. create_prefix_step x y explicit ctx fn p chunk q ==>
               create_prefix_step a b explicit ctx fn p chunk q) /\
  (!u. create_cut_region x y u /\
       (u.vs_current_bb <> y.cs_current_bb \/
        u.vs_inst_idx <> LENGTH y.cs_current_insts) ==>
       u.vs_current_bb <> b.cs_current_bb \/
       u.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  exit_result r /\ create_operand_full_scope x y explicit ctx fn s ms r ==>
  create_operand_full_scope a b explicit ctx fn s ms r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def,exit_result_def] >>
  strip_tac >>
  rename1 `create_expr_prefix x y explicit ctx fn s left stop` >>
  `create_cut_region x y stop` by metis_tac[create_expr_prefix_cut_region] >>
  `create_expr_prefix a b explicit ctx fn s left stop` by
    metis_tac[create_expr_prefix_mono] >>
  metis_tac[]
QED

(* A nonempty continuation at the cut provides a fetch outside the earlier
   band. When there is no instruction there, the lift premise is vacuous. *)
Theorem create_cut_continuation_fetch:
  create_cut_code {} b c /\ fn_has_code b c fn /\
  (b.cs_current_bb <> c.cs_current_bb \/
   LENGTH b.cs_current_insts <> LENGTH c.cs_current_insts) /\
  lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
  b.cs_next_id <= i.inst_id
Proof
  strip_tac >> drule_all create_cut_region_rules >> strip_tac >>
  `?u. u.vs_current_bb = b.cs_current_bb /\
       u.vs_inst_idx = LENGTH b.cs_current_insts` by
    (qexists_tac `ARB with <| vs_current_bb := b.cs_current_bb;
                             vs_inst_idx := LENGTH b.cs_current_insts |>` >> simp[]) >>
  `i.inst_id IN frag_ids b c` by metis_tac[] >>
  fs[frag_ids_def]
QED

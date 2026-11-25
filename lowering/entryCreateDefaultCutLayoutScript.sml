(* The common-entry JMP separates strict stops of each initializer row
   from the enclosing exit, even when a stop has no returning step. *)
Theory entryCreateDefaultCutLayout
Ancestors
  entryCreatePathScope entryCreatePendingScope createSizeCutRegion
  placeTypedCopyPath abiEncoderProps arithmetic pred_set

Theorem grouped_initializer_exit_fetch:
  emit_inst JMP [Label common] [] b = ((),term) /\ fn_has_code b term fn ==>
  ?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH b.cs_current_insts) = SOME i /\
         b.cs_next_id <= i.inst_id
Proof
  strip_tac >> drule_all place_copy_emit_instruction >> strip_tac >>
  first_assum (irule_at Any) >> simp[venomInstTheory.mk_inst_def]
QED

Theorem grouped_initializer_inner_lifts:
  (?bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i /\
          b.cs_next_id <= i.inst_id) /\
  a.cs_next_id <= x.cs_next_id /\ y.cs_next_id <= b.cs_next_id /\
  create_cut_code {} x y /\ fn_has_code x y fn ==>
  (!u. create_cut_region x y u /\
       (u.vs_current_bb <> y.cs_current_bb \/
        u.vs_inst_idx <> LENGTH y.cs_current_insts) ==>
       u.vs_current_bb <> b.cs_current_bb \/
       u.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  (!p chunk q. create_prefix_step x y explicit ctx fn p chunk q ==>
               create_prefix_step a b explicit ctx fn p chunk q) /\
  (!s ms t. create_expr_prefix x y explicit ctx fn s ms t ==>
            create_expr_prefix a b explicit ctx fn s ms t) /\
  (!tops ce cx s. body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
                  create_cut_region x y s ==>
    (!ms. create_operand_focus_scope x y explicit ctx fn s ms ==>
          create_operand_focus_scope a b explicit ctx fn s ms) /\
    (!ms r. exit_result r /\ create_operand_full_scope x y explicit ctx fn s ms r ==>
            create_operand_full_scope a b explicit ctx fn s ms r))
Proof
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `!bb i. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids x y` by
    (rpt strip_tac >> gvs[frag_ids_def] >> decide_tac) >>
  conj_asm1_tac
  >- (gen_tac >> strip_tac >> CCONTR_TAC >> gvs[] >>
      drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
      `i.inst_id IN frag_ids x y` by metis_tac[] >> metis_tac[]) >>
  conj_asm1_tac >- metis_tac[create_prefix_step_lift] >>
  conj_tac >- metis_tac[create_expr_prefix_mono] >>
  rpt gen_tac >> strip_tac >> conj_tac >> rpt strip_tac
  >- metis_tac[create_operand_focus_scope_lift]
  >> metis_tac[create_operand_full_scope_lift_terminal]
QED

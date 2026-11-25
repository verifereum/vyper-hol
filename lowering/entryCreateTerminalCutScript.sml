Theory entryCreateTerminalCut
Ancestors
  entryCreateEffectFocus entryCreateFocusSpec entryCreatePathScope
  entryCreateBodyCut createSizeCutCode createSizeOperandCode createSizeCutRegion
  list pair fragExec venomRunBounded

(* Safety of the fetched suffix instruction is independent of the source
   and of the prefix preceding the suffix. *)
Theorem terminal_suffix_visit_safe[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  fn_has_code m b f /\ create_cut_code {} m b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code m b) /\
  create_interior_visit m b E ctx f (p,d,k) t (back,hit,after) ==>
  create_body_cut E tops cx st0 source (es,s) (before,hit)
Proof
  strip_tac >> drule_all create_cut_region_rules >> strip_tac >>
  `create_cut_region m b t` by
    fs[create_interior_visit_def, create_operand_at_def] >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region m b u` by metis_tac[create_expr_prefix_cut_region] >>
  fs[create_operand_fetch_def, create_operand_at_def, EVERY_MEM] >>
  `MEM inst (frag_code m b)` by metis_tac[] >>
  gvs[create_body_cut_def, venomRunBoundedTheory.inst_create_size_ok_def]
QED

Theorem terminal_child_suffix_cut:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  lower_value compile_expr ce ty e a = (op,m) /\ fn_has_code a b f /\
  (compile_raw_revert op m = ((),b) \/ compile_selfdestruct op m = ((),b)) /\
  (cs_extends a m /\ cs_extends m b /\ fn_has_code a b f ==>
     fn_has_code a m f /\ fn_has_code m b f) /\
  (!p d k before hit after.
    body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
    create_cut_code {} a m /\ fn_has_code a m f /\
    create_cut_code {} m b /\ fn_has_code m b f /\
    create_interior_visit a b E ctx f (p,d,k) s (before,hit,after) ==>
    create_interior_visit a m E ctx f (p,d,k) s (before,hit,after) \/
    ?t d1 k1 front back.
      before = front ++ back /\ create_operand_at m t /\
      RTC (create_operand_native_step a m E ctx f p) (d,k,s,[]) (d1,k1,t,front) /\
      create_expr_prefix a m E ctx f s (create_cut_marks E front) t /\
      create_interior_visit m b E ctx f (p,d1,k1) t (back,hit,after)) /\
  create_operand_cut a m E ctx f tops cx st0 child (es,s) /\
  (!v. storage_trace_frame (next v)) ==>
  create_operand_cut a b E ctx f tops cx st0 (bind child next) (es,s)
Proof
  rpt (disch_then (CONJUNCTS_THEN2 assume_tac mp_tac)) >> strip_tac >>
  `create_cut_code {} a m` by metis_tac[create_operand_cut_code, SND] >>
  `create_cut_code {} m b /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code m b)` by
    metis_tac[raw_revert_effect_code, selfdestruct_effect_code] >>
  `fn_has_code a m f /\ fn_has_code m b f` by
    metis_tac[create_cut_code_def] >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p d k before hit after. _ ==> _` (fn th => drule_all th) >>
  strip_tac
  >- (irule create_cut_bind_left >> fs[create_operand_cut_def] >> metis_tac[]) >>
  irule terminal_suffix_visit_safe >> metis_tac[]
QED

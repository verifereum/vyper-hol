(* A focused operand can stop at a caller cursor or inside a pending INVOKE. *)
Theory entryCreatePendingScope
Ancestors
  entryCreatePathScope entryCreateCompletedCut createSizePrefixReplay
  createSizeCutRegion createSizeCutCode bodySim abiEncoderProps
  fragGasOriginPtr fragGasOriginEvents fragGasOrigin fragGasFocus fragExec
  gasEvents gasEventsFuel venomExecSemantics venomInst venomState
  list rich_list arithmetic

Theorem create_operand_focus_scope_caller:
  create_expr_prefix sa sb explicit ctx func s left u ==>
  create_operand_focus_scope sa sb explicit ctx func s left
Proof
  rw[create_operand_focus_scope_def] >> qexistsl [`left`, `u`, `[]`] >> simp[]
QED

(* The terminating instruction fuel is a ceiling on observations, even
   when the focused path itself can be witnessed with more fuel. *)
Theorem completed_step_extends_events[local]:
  (!err. step_inst fuel ctx inst s <> Error err) ==>
  isPREFIX (gas_events_step n ctx owner inst s)
           (gas_events_step fuel ctx owner inst s)
Proof
  strip_tac >> Cases_on `n <= fuel` >>
  metis_tac[cj 1 gas_events_fuel_extension, IS_PREFIX_APPEND, LESS_EQ_CASES]
QED

Theorem completed_edge_events[local]:
  gas_origin_edge mode explicit ctx func u right (OK v) ==>
  ?fuel bb inst.
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    (!err. step_inst fuel ctx inst u <> Error err) /\
    right = MAP (\key. key IN explicit) (gas_events_step fuel ctx func.fn_name inst u)
Proof
  rw[gas_origin_edge_def] >> qexistsl [`fuel`,`bb`,`inst`] >>
  metis_tac[exit_result_not_error, exec_result_distinct]
QED

Theorem invoke_focus_events[local]:
  gas_invoke_entry (ctx,func) u callee entered /\
  gas_origin_focus memory explicit (ctx,callee) entered pending (leaf,stop_state) ==>
  ?n bb inst.
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME inst /\
    isPREFIX pending (MAP (\key. key IN explicit) (gas_events_step n ctx func.fn_name inst u))
Proof
  strip_tac >> drule gas_origin_focus_events_prefix >>
  disch_then (qx_choosel_then [`n`,`extra`] assume_tac) >>
  qpat_x_assum `gas_invoke_entry _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[gas_invoke_entry_def]) >>
  drule_all gas_events_blocks_current_entry >>
  disch_then (qspecl_then [`n`,`ctx`] assume_tac) >>
  qexistsl [`SUC n`,`bb`,`inst`] >>
  fs[gas_events_step_def, IS_PREFIX_APPEND]
QED

Theorem invoke_focus_prefix_completed_edge[local]:
  gas_invoke_entry (ctx,func) u callee entered /\
  gas_origin_focus memory explicit (ctx,callee) entered pending (leaf,stop_state) /\
  gas_origin_edge mode explicit ctx func u right (OK v) ==>
  isPREFIX pending right
Proof
  strip_tac >> drule_all invoke_focus_events >>
  disch_then (qx_choosel_then [`n`,`bb`,`inst`] strip_assume_tac) >>
  drule completed_edge_events >> strip_tac >> gvs[] >>
  drule completed_step_extends_events >>
  disch_then (qspecl_then [`func.fn_name`,`n`] assume_tac) >>
  fs[IS_PREFIX_APPEND, MAP_APPEND] >> metis_tac[APPEND_ASSOC]
QED

Theorem create_operand_focus_scope_pending:
  create_expr_prefix sa sb explicit ctx func s left u /\
  (u.vs_current_bb <> sb.cs_current_bb \/
   u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  gas_invoke_entry (ctx,func) u callee entered /\
  gas_origin_ptr_focus (D,lo,explicit,ctx,callee,PG)
    (entered,G,tn) pending (leaf,leaf_pg,leaf_g,leaf_tn,stop_state) ==>
  create_operand_focus_scope sa sb explicit ctx func s (left ++ pending)
Proof
  strip_tac >> drule gas_origin_ptr_focus_origin >> strip_tac >>
  simp[create_operand_focus_scope_def] >> qexistsl [`left`,`u`,`pending`] >>
  simp[] >> rpt strip_tac >>
  fs[create_prefix_step_def] >> metis_tac[invoke_focus_prefix_completed_edge]
QED

(* Compose only the returned caller edges, leaving any pending suffix once.
   The right fragment's exit is also the outer exit. *)
Theorem create_operand_focus_scope_join:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  (!bb i. lookup_block c.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH c.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids a b) /\
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} b c /\ fn_has_code b c fn /\ create_cut_region b c u /\
  create_expr_prefix a b explicit ctx fn s first u /\
  create_operand_focus_scope b c explicit ctx fn u focus ==>
  create_operand_focus_scope a c explicit ctx fn s (first ++ focus)
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix b c explicit ctx fn u left stop` >>
  `create_expr_prefix a c explicit ctx fn s (first ++ left) stop` by
    metis_tac[create_expr_prefix_join] >>
  qexistsl [`first ++ left`,`stop`,`pending`] >>
  simp[APPEND_ASSOC] >>
  `create_cut_region b c stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> rpt strip_tac >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED

Theorem create_operand_focus_scope_prepend:
  create_expr_prefix sa sb explicit ctx func s first u /\
  create_operand_focus_scope sa sb explicit ctx func u focus ==>
  create_operand_focus_scope sa sb explicit ctx func s (first ++ focus)
Proof
  simp[create_operand_focus_scope_def] >> strip_tac >>
  rename1 `create_expr_prefix sa sb explicit ctx func u left stop` >>
  qexistsl [`first ++ left`, `stop`, `pending`] >>
  simp[APPEND_ASSOC] >> metis_tac[create_expr_prefix_append]
QED

(* When the left fragment focuses there is no right path to append. A
   pending suffix remains pending at the same in-fragment instruction. *)
Theorem create_operand_focus_scope_lift:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} x y /\ fn_has_code x y fn /\ create_cut_region x y s /\
  (!p chunk q. create_prefix_step x y explicit ctx fn p chunk q ==>
               create_prefix_step a b explicit ctx fn p chunk q) /\
  (!u. create_cut_region x y u /\
       (u.vs_current_bb <> y.cs_current_bb \/
        u.vs_inst_idx <> LENGTH y.cs_current_insts) ==>
       u.vs_current_bb <> b.cs_current_bb \/
       u.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  create_operand_focus_scope x y explicit ctx fn s marks ==>
  create_operand_focus_scope a b explicit ctx fn s marks
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix x y explicit ctx fn s left stop` >>
  `create_expr_prefix a b explicit ctx fn s left stop` by
    metis_tac[create_expr_prefix_mono] >>
  qexistsl [`left`,`stop`,`pending`] >> simp[] >>
  `create_cut_region x y stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED

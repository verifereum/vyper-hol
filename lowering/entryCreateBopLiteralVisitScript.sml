(* Native cut at the boundary between the word list and scalar membership. *)
Theory entryCreateBopLiteralVisit
Ancestors
  entryCreateNativeFirstExit entryCreateIntervalLayout entryCreateFocusSpec
  entryCreateBodyCut createSizeCutCode createSizePrefixReplay
  exprSimBopInLiteralWord exprSimHypsDefs fragExec compileEnv
  gasSummaryCompose fragGasPath vyperStorageTrace vyperInterpreter vyperState list

(* The scalar suffix cut is source-independent. Apply it at the actual
   boundary, giving it the enclosing source query with the consumed marks
   prepended. This needs no source success or replay for an administrative hit. *)
Theorem literal_member_visit_from_split:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1; Builtin a (MakeArray ty n) elems]) es /\
  (bop = In \/ bop = NotIn) /\
  ~s.vs_halted /\ create_layout sa sb /\
  cs_extends sa sm /\ cs_extends sm sb /\ fn_has_code sa sb f /\
  create_cut_code {} sa sm /\ create_cut_code {} sm sb /\
  (create_layout sa sm ==>
   create_operand_cut sa sm E ctx f tops cx st0 (eval_exprs cx (e1::elems)) (es,s)) /\
  (!t (source : evaluation_state -> value evaluation_result).
   create_layout sm sb /\ create_operand_at sm t ==>
   create_operand_cut sm sb E ctx f tops cx st0 source (es,t)) ==>
  create_operand_cut sa sb E ctx f tops cx st0
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1; Builtin a (MakeArray ty n) elems]))
      (read_result cx)) (es,s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_has_code sa sm f /\ fn_has_code sm sb f` by metis_tac[fn_has_code_split] >>
  `create_layout sa sm /\ create_layout sm sb` by
    metis_tac[create_layout_subinterval,cs_extends_refl] >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  simp[create_operand_cut_def] >> rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> simp[storage_trace_frame_return] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_all create_prefix_gas_path >> strip_tac >>
  drule gas_explicit_append_path >> strip_tac >>
  qabbrev_tac `src = bind (eval_exprs cx (e1::elems))
    (\vs. return (BoolV (if bop = In then MEM (HD vs) (TL vs) else ~MEM (HD vs) (TL vs))))` >>
  `create_operand_cut sm sb E ctx f tops cx st0
     (\q. src (es with gas_obs :=
       gas_explicit (create_cut_marks E front) s.vs_gas_readings ++ q.gas_obs)) (es,t)` by
    (first_assum irule >> simp[]) >>
  qpat_x_assum `create_operand_cut sm sb _ _ _ _ _ _ _ _`
    (drule_then mp_tac o REWRITE_RULE [create_operand_cut_def]) >>
  simp[create_body_cut_def, APPEND_ASSOC] >> metis_tac[]
QED

(* The calldata flavor evaluates one word list. All code emitted after
   that list is administrative or belongs to the external request. *)
Theory entryCreateRawCallCalldata
Ancestors
  bodyFullRawCallCalldata entryCreateNativeFirstExit entryCreateBodyCut
  entryCreateStmtCases entryCreateFocusSpec entryCreatePathScope createSizeCutRegion
  exprSimAbiDecodeSiteCoverage createSizeCutCode vyperStorageTrace
  entryCreateRawCallWords entryCreateRawCallCalldataInstall entryCreateRawCallCalldataRun
  entryCreateRawCallGeneratedPrefix
  s1PrefixDefs exprSimFullBundleProps bodyFullEmptyLeafData
  vyperInterpreter vyperState list

Theorem raw_call_calldata_suffix_join[local]:
  create_cut_code {} a m /\ create_cut_code {} m b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a m) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code m b) ==>
  create_cut_code {} a b /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b)
Proof
  strip_tac >> conj_tac >- metis_tac[create_cut_code_join] >>
  `cs_extends a m /\ cs_extends m b` by fs[create_cut_code_def] >>
  drule_all abi_decode_frag_code_compose >> disch_then (fn th => simp[EVERY_MEM,th]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem raw_call_calldata_suffix_inventory:
  create_cut_code {} s2 s3 /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s2 s3) /\
  create_cut_code {} s3 s4 /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s3 s4) /\
  create_cut_code {} s4 s5 /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s4 s5) /\
  create_cut_code {} s5 sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s5 sb) ==>
  create_cut_code {} s2 sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s2 sb)
Proof
  strip_tac >>
  `create_cut_code {} s4 sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s4 sb)` by
    (irule raw_call_calldata_suffix_join >> qexists_tac `s5` >> simp[]) >>
  `create_cut_code {} s3 sb /\
   EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code s3 sb)` by
    (irule raw_call_calldata_suffix_join >> qexists_tac `s4` >> simp[]) >>
  irule raw_call_calldata_suffix_join >> qexists_tac `s3` >> simp[]
QED

Theorem raw_call_calldata_suffix_hit[local]:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a b /\ fn_has_code a b fn /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code a b) /\
  create_interior_visit a b E ctx fn (p,d,k) s (before,hit,after) ==>
  ?key u i. hit = (key,fn,i,u) /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2
Proof
  strip_tac >>
  `create_cut_region a b s` by
    (drule_all create_cut_region_rules >> strip_tac >>
     fs[create_interior_visit_def,create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region a b u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >>
  `MEM inst (frag_code a b)` by metis_tac[] >> gvs[]
QED

(* The safety of the right hit is opcode-only: word-list replay is not
   needed there. On the left, propagate the source error through the bind. *)
Theorem raw_call_calldata_word_cut:
  body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m fn /\
  create_cut_code {} m b /\ fn_has_code m b fn /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE;CREATE;CREATE2]) (frag_code m b) /\
  create_operand_cut a m E ctx fn tops cx st0 (eval_exprs cx args) (es,s) ==>
  create_operand_cut a b E ctx fn tops cx st0
    (eval_expr cx (Call ann (RawCallCalldataTarget flags) args NONE)) (es,s)
Proof
  strip_tac >> simp[raw_call_calldata_eval,create_operand_cut_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> rpt conj_tac
      >~ [`storage_trace_frame _`]
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_ignore_bind >>
          simp[storage_trace_frame_checks] >>
          irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
          irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_lifts,storage_trace_frame_raw_call]) >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_all raw_call_calldata_suffix_hit >> strip_tac >>
  gvs[] >> irule create_cut_noncreate_visit >> simp[]
QED

Theorem raw_call_calldata_selected_hypotheses[local]:
  expr_vv_sim_full_hypotheses
    (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) ==>
  compile_expr cenv ty e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
    (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func
Proof
  simp_tac bool_ss [expr_vv_sim_full_hypotheses_def,expr_sim_full_code_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

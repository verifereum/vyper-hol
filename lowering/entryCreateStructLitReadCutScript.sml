(* Native CREATE exclusion for the installed StructLit field read. *)
Theory entryCreateStructLitReadCut
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreateBodyCut
  entryCreatePosSnapshotCode exprSimAbiEncodeObliviousCode
  createSizeLocationCode createSizeCutRegion fragExec
  exprLowering bodySim gasContext compileEnv venomInst venomRunBounded list pair

Theorem structlit_installed_read_cut:
  unwrap_value ce vv sn = (op,su) /\ fn_has_code sn su f /\
  body_inv (cx_tops cx) ctx ce cx /\ MEM f ctx.ctx_functions ==>
  create_operand_cut sn su E ctx f (cx_tops cx) cx st0 source (ee,s)
Proof
  strip_tac >>
  `create_cut_code {} sn su` by metis_tac[create_unwrap_cut_code,SND] >>
  `!i. MEM i (frag_code sn su) ==>
       i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2` by
    (drule (REWRITE_RULE [code_action_def] admin_unwrap_code_action) >>
     simp[code_step_def, EVERY_MEM]) >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  `create_cut_region sn su s` by
    (drule_all create_cut_region_rules >> strip_tac >>
     fs[create_interior_visit_def,create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region sn su u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def,create_operand_at_def] >>
  `MEM inst (frag_code sn su)` by metis_tac[] >>
  gvs[create_body_cut_def,inst_create_size_ok_def]
QED

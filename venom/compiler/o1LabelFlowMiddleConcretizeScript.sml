Theory o1LabelFlowMiddleConcretize
Ancestors
  codegenSymRel concretizeStageShape concretizeStepRetpc concretizeStepShape
  concretizeStepStructure concretizeMemLocDefs passSharedDefs passTransform
  venomInst list rich_list

Theorem concretize_code_end_forward:
  !f x. code_end_var f x ==>
  !p. code_end_var (concretize_function_with_positions p f) x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts (concretize_function_with_positions p f))` by
    (irule concretize_positions_retained_member >> simp[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem concretize_code_end_backward:
  !g x. code_end_var g x ==>
  !f p. g = concretize_function_with_positions p f ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> gvs[] >>
  drule concretize_positions_fn_preimage >> strip_tac >> gvs[]
  >~ [`(concretize_inst_with_positions p oldi).inst_opcode = ADD`]
  >- (`concretize_inst_with_positions p oldi = oldi` by
        (irule concretize_positions_other_opcode >> simp[]) >>
      gvs[] >> metis_tac[code_end_var_rules]) >>
  rename1 `(concretize_inst_with_positions p oldi).inst_operands = [Var y]` >>
  `MEM (Var y) (concretize_inst_with_positions p oldi).inst_operands` by simp[] >>
  drule concretize_positions_var_operand >> strip_tac >> gvs[] >>
  metis_tac[code_end_var_rules]
QED

Theorem concretize_code_end:
  code_end_var (concretize_function_with_positions p f) x <=> code_end_var f x
Proof
  metis_tac[concretize_code_end_forward, concretize_code_end_backward]
QED

Theorem concretize_label_flow:
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [concretize_function_with_positions p f])
Proof
  simp[label_flow_ok_def] >> rpt strip_tac >>
  drule concretize_positions_fn_preimage >> strip_tac >> gvs[] >>
  rpt conj_tac
  >- (Cases_on `(concretize_inst_with_positions p oldi).inst_opcode = CODESIZE` >>
      simp[] >>
      `concretize_inst_with_positions p oldi = oldi` by
        (irule concretize_positions_other_opcode >> simp[]) >>
      gvs[] >> metis_tac[]) 
  >- (rpt strip_tac >> drule concretize_positions_var_operand >> strip_tac >>
      gvs[concretize_code_end] >> metis_tac[]) >>
  `concretize_inst_with_positions p oldi = oldi` by
    (irule concretize_positions_other_opcode >> simp[]) >>
  gvs[concretize_code_end] >> metis_tac[]
QED

Theorem concretize_adjacent:
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode = ADD /\ j.inst_opcode = CODECOPY ==>
  ?pre' post'.
    (clear_nops_block (block_map_transform
       (concretize_inst_with_positions p) bb)).bb_instructions =
    pre' ++ d::j::post'
Proof
  strip_tac >>
  qexistsl [`FILTER (\i. i.inst_opcode <> NOP)
                (MAP (concretize_inst_with_positions p) pre)`,
             `FILTER (\i. i.inst_opcode <> NOP)
                (MAP (concretize_inst_with_positions p) post)`] >>
  simp[clear_nops_block_def, block_map_transform_def, MAP_APPEND,
       FILTER_APPEND, concretize_positions_unchanged]
QED

Theorem concretize_code_end_lifetime:
  MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
  (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
  (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
     MEM (Var x) j.inst_operands ==>
     j.inst_opcode = CODECOPY /\
     (?dst sz. j.inst_operands = [dst; Var x; sz] /\
               dst <> Var x /\ sz <> Var x) /\
     ?pre post. bb.bb_instructions = pre ++ d::j::post) ==>
  MEM d (fn_insts (concretize_function_with_positions p f)) /\
  d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
  (!k. MEM k (fn_insts (concretize_function_with_positions p f)) /\
       MEM x k.inst_outputs ==> k = d) /\
  (!bb j. MEM bb (concretize_function_with_positions p f).fn_blocks /\
     MEM j bb.bb_instructions /\ MEM (Var x) j.inst_operands ==>
     j.inst_opcode = CODECOPY /\
     (?dst sz. j.inst_operands = [dst; Var x; sz] /\
               dst <> Var x /\ sz <> Var x) /\
     ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  strip_tac >> simp[] >> conj_tac
  >- (irule concretize_positions_retained_member >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule concretize_positions_fn_preimage >> strip_tac >>
      `MEM x oldi.inst_outputs` by metis_tac[concretize_positions_outputs] >>
      `oldi = d` by metis_tac[] >>
      gvs[concretize_positions_unchanged]) >>
  rpt strip_tac >>
  gvs[concretize_positions_block_provenance,
      concretize_positions_block_instruction] >>
  drule concretize_positions_var_operand >> strip_tac >> gvs[] >>
  `inst.inst_opcode = CODECOPY /\
   (?dst sz. inst.inst_operands = [dst; Var x; sz] /\
             dst <> Var x /\ sz <> Var x) /\
   ?pre post. bb'.bb_instructions = pre ++ d::inst::post` by
    (first_x_assum drule_all >> simp[] >> metis_tac[]) >>
  simp[] >> drule_all concretize_adjacent >> simp[]
QED

(* The pointwise boundary above keeps the seed witness explicit; this
   quantified form matches the LowerDload lifetime interface directly. *)
Theorem concretize_function_code_end_lifetime:
  (!x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
         MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)) ==>
  !x. code_end_var (concretize_function_with_positions p f) x ==>
    ?d op. MEM d (fn_insts (concretize_function_with_positions p f)) /\
      d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts (concretize_function_with_positions p f)) /\
           MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb (concretize_function_with_positions p f).fn_blocks /\
         MEM j bb.bb_instructions /\ MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  simp[concretize_code_end] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`d`,`op`] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule concretize_code_end_lifetime >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  asm_rewrite_tac[]
QED

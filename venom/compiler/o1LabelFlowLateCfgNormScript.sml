Theory o1LabelFlowLateCfgNorm
Ancestors
  cfgNormSupplySim cfgNormDefs cfgTransform irSupply unitShapeDefs
  venomInst list

(* Exact forwarding shape complements the existing source-only and
   output-membership interfaces. No supply well-formedness is needed. *)
Theorem cfg_forwarding_assign_shape:
  !vars s repls insts t.
  build_forwarding_assigns_supply s vars = (repls,insts,t) ==>
  !i. MEM i insts ==>
  ?v w. MEM (v,w) repls /\ MEM v vars /\
        i.inst_opcode = ASSIGN /\ i.inst_operands = [Var v] /\
        i.inst_outputs = [w]
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >> rename1 `fresh_ir_var s = (nv,s1)` >>
  Cases_on `fresh_inst_id s1` >> rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >> PairCases_on `r` >>
  gvs[build_forwarding_assigns_supply_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

(* Both directions retain all ordinary instructions, not just label-flow
   opcodes. The existing block-image lemmas include the self-loop case. *)
Theorem cfg_split_retains_ordinary:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  MEM i (fn_insts fn) /\ i.inst_opcode <> PHI /\
  ~is_terminator i.inst_opcode ==>
  MEM i (fn_insts out)
Proof
  strip_tac >> drule_all insert_split_supply_old_inst_image >> strip_tac >>
  metis_tac[supply_inst_image_unchanged]
QED

Theorem cfg_split_ordinary_origin:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  MEM i (fn_insts out) /\ i.inst_opcode <> PHI /\
  ~is_terminator i.inst_opcode ==>
  MEM i (fn_insts fn) \/
  ?v w. MEM (v,w) repls /\ i.inst_opcode = ASSIGN /\
        i.inst_operands = [Var v] /\ i.inst_outputs = [w]
Proof
  strip_tac >> drule_all insert_split_supply_inst_image >> strip_tac
  >- metis_tac[supply_split_assign_replacement] >>
  disj1_tac >>
  metis_tac[supply_inst_image_metadata, supply_inst_image_unchanged]
QED

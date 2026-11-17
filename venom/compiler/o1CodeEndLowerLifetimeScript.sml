Theory o1CodeEndLowerLifetime
Ancestors
  o1LabelFlowLowerDload lowerDloadMakeSsaInput o1PassContract
  venomInst codegenSymRel list

(* The pass-step contract supplies freshness for every enumerated function;
   no label-flow assumption on unrelated instructions is needed. *)
Theorem lower_dload_stage_protected_lifetime:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  (!f i. MEM f C.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  EVERY (\f. !x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
         MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >>
  disch_then (qx_choose_then `source_fn` strip_assume_tac) >> gvs[] >>
  drule lower_dload_step_supply >> strip_tac >>
  `!i. MEM i (fn_insts source_fn) ==> ~MEM (Label "code_end") i.inst_operands`
    by metis_tac[] >>
  drule_all lower_dload_function_code_end_lifetime >> simp[]
QED

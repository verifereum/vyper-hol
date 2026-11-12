Theory runtimeSymSrcStatementAssign
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv venomInst stackPlanTypes

(* External boundary ledger: compile_imm_store_word is owned by C1.1.3.2.
   Its concrete safety implication is retained below for the final join. *)
Theorem runtime_sym_store_at_loc:
  (!d v s u s'. ~is_label_operand d /\ ~is_label_operand v /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_imm_store_word imm d v s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) ==>
  !dst value loc s u s'.
    ~is_label_operand dst /\ ~is_label_operand value /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_at_loc imm dst value loc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> Cases_on `loc`
  >- (simp[compile_store_at_loc_def] >> rpt strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
      simp[] ) >>
  Cases_on `x` >> simp[compile_store_at_loc_def] >> rpt strip_tac
  >~ [`compile_imm_store_word imm dst value s = _`]
  >- metis_tac[] >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]
QED

(* compile_load_memory belongs to the C1.1.3.2 memory boundary. *)
Theorem runtime_sym_tuple_load_all:
  (!src prim s op s'. ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_load_memory src prim s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  !tys ce src off s ops s'.
    ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_load_all ce src tys off s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops
Proof
  strip_tac >> Induct >>
  simp[compile_tuple_load_all_def, comp_return_def] >>
  rpt gen_tac >>
  simp[comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[comp_return_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theory createSizePrefixCutsMods
Ancestors
  createSizePrefixCuts createExprSizeExitDefsMods
  abiEncoderProps fragExec venomExecSemantics venomInst relation list words pair
  builtinCreate arithmetic createSizeDispatch exprLowering vfmConstants createSizeCutRegion
  createSizeCutEntry createSizeCutCode compilerInstructionSuffix externalEntryShape
  compileEnv createSizeItinerary exprLoweringProps fragFuel rich_list createSizeOperandCode
  createSizeCtorCutSpine createSizeFixedPreparation createSizeConcreteSnapshots
  createSizeLocationCode createSizeEncodeCode context integer_word bodySim
  createExprSizeExitDefs createSizePrefixReplayMods

Theorem create_size_prefix_cut_walk_mods[local]:
  !mods exps src cuts a u marks.
    cs_extends sa a /\ LAST (a::cuts) = sc /\
    LIST_REL (create_cut_code {}) (FRONT (a::cuts)) cuts /\
    LIST_REL create_cut_first (FRONT (a::cuts)) cuts /\
    cs_extends sc sb /\ fn_has_code sa sb func /\
    lookup_block sc.cs_current_bb func.fn_blocks = SOME db /\
    get_instruction db (LENGTH sc.cs_current_insts) = SOME dispatch /\
    dispatch.inst_id = sc.cs_next_id /\ MEM dispatch.inst_opcode [CREATE;CREATE2] /\
    emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
    compile_check_create_result created rof sd = (result,sb) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    create_expr_prefix sa sb explicit ctx func u marks s ==>
    ?states chunks.
      HD states = u /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
      LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                      v.vs_inst_idx = LENGTH c.cs_current_insts) (a::cuts) states /\
      (!i. i < LENGTH cuts ==>
        create_expr_prefix (EL i (a::cuts)) (EL i cuts) explicit ctx func
          (EL i states) (EL i chunks) (EL (SUC i) states)) /\
      marks = FLAT chunks
Proof
  cheat
QED

Theorem create_size_itinerary_at_emit_mods[local]:
  create_itinerary_code sa cuts sc /\
  emit_op opc ops sc = (created,sd) /\ MEM opc [CREATE;CREATE2] /\
  compile_check_create_result created rof sd = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?out states chunks.
    created = Var out /\ inst = mk_inst sc.cs_next_id opc ops [out] /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks
Proof
  cheat
QED

Theorem create_size_prefix_cuts_from_code_mods:
  create_itinerary_suppliers /\ create_itinerary_rows_supplier /\
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  cheat
QED

Theorem create_size_prefix_cuts_mods:
  compile_create_call compile_expr cenv ck salted rof args sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\ MEM func ctx.ctx_functions /\
  create_expr_prefix sa sb explicit ctx func s0 marks s /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (s.vs_current_bb <> sb.cs_current_bb \/ s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_id IN frag_ids sa sb /\
  MEM inst.inst_opcode [CREATE;CREATE2] /\
  (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
       MEM j.inst_opcode [CREATE;CREATE2] ==> j.inst_id <= inst.inst_id) ==>
  ?cuts value salt bufop len sc sd created out states chunks.
    create_call_itinerary cenv ck salted args sa cuts value salt bufop len /\
    create_size_dispatch_tail rof sc sd created bufop len value salt result sb /\
    created = Var out /\
    inst = (case salt of
             NONE => mk_inst sc.cs_next_id CREATE [value;bufop;len] [out]
           | SOME x => mk_inst sc.cs_next_id CREATE2 [value;bufop;len;x] [out]) /\
    s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    LAST (sa::cuts) = sc /\
    HD states = s0 /\ LAST states = s /\ LENGTH chunks = LENGTH cuts /\
    LIST_REL (\c v. v.vs_current_bb = c.cs_current_bb /\
                    v.vs_inst_idx = LENGTH c.cs_current_insts) (sa::cuts) states /\
    (!i. i < LENGTH cuts ==>
      create_expr_prefix (EL i (sa::cuts)) (EL i cuts) explicit ctx func
        (EL i states) (EL i chunks) (EL (SUC i) states)) /\
    marks = FLAT chunks /\ create_itinerary_code sa cuts sc
Proof
  cheat
QED

Theory runtimeSymSrcOpenPlaces
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv context list supportedExprs supportedExprTraverse
  finite_map venomInst loweringShapeDefs stackPlanTypes

Theorem runtime_sym_target_base:
  !target ce. runtime_sym_env ce ==>
  ~is_label_operand (compile_target_base ce target)
Proof
  gen_tac >> measureInduct_on `vyperAST$base_assignment_target_size target` >>
  Cases_on `target` >> simp[compile_target_base_def, vyperASTTheory.expr_size_def] >> rpt strip_tac
  >- (Cases_on `FLOOKUP ce.ce_vars s` >> gvs[is_label_operand_def] >>
      Cases_on `x` >> gvs[is_label_operand_def] >>
      drule_all runtime_sym_env_local >> simp[runtime_sym_loc_def]) >>
  Cases_on `FLOOKUP ce.ce_module_vars p` >> gvs[is_label_operand_def] >>
  Cases_on `x` >> gvs[is_label_operand_def]
QED

Theorem runtime_sym_attribute:
  runtime_sym_attribute_clause tops
Proof
  rewrite_tac[runtime_sym_attribute_clause_def] >>
  map_every qx_gen_tac [`cfn`,`ce`,`rt`,`ty`,`base_e`,`fld`,`s`,`v`,`s'`] >>
  strip_tac >>
  `supported_expr tops base_e \/ supported_place_expr tops base_e \/
   supported_effect_place_expr tops base_e` by
    (gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def]) >>
  `~supported_expr_exists is_self_code base_e` by
    gvs[supported_expr_exists_def] >>
  qpat_x_assum `compile_attribute _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_attribute_def, comp_bind_def] >>
  Cases_on `cfn ce ty base_e s` >> simp[] >>
  pairarg_tac >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  rewrite_tac[runtime_sym_expr_contract_def] >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule runtime_sym_value_operand >> strip_tac >>
  drule_at (Pos last) runtime_sym_emit_op >> simp[is_label_operand_def] >>
  simp[runtime_sym_value_def, mk_ptr_def]
QED


Theorem runtime_sym_bind_safe:
  (!x t. f s = (x,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ P x) /\
  (!x t y u. EVERY runtime_sym_inst (state_insts t) /\ P x /\
     g x t = (y,u) ==> EVERY runtime_sym_inst (state_insts u) /\ Q y) /\
  comp_bind f g s = (z,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ Q z
Proof
  Cases_on `f s` >> simp[comp_bind_def] >> metis_tac[]
QED

Theorem runtime_sym_optional_hash:
  (!op b s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\ compile_keccak256_key op b s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) ==>
  !b op s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\
     (if b then compile_keccak256_key op F else comp_return op) s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  strip_tac >> Cases_on `b` >> simp[NoAsms, comp_return_def] >>
  metis_tac[]
QED

Theorem runtime_sym_map_sequence:
  (!op b s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand op /\ compile_keccak256_key op b s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!bop key s out s'. EVERY runtime_sym_inst (state_insts s) /\
     ~is_label_operand bop /\ ~is_label_operand key /\
     compile_mapping_subscript bop key s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out) /\
  (!op t. key_comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  ~is_label_operand bop /\
  comp_bind key_comp (\key.
    comp_bind (if hash then compile_keccak256_key key F else comp_return key)
      (\hashed. comp_bind (compile_mapping_subscript bop hashed)
        (\slot. comp_return (LocatedValue rt (mk_ptr slot loc))))) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> Cases_on `key_comp s` >>
  `EVERY runtime_sym_inst (state_insts r) /\ ~is_label_operand q` by metis_tac[] >>
  Cases_on `(if hash then compile_keccak256_key q F else comp_return q) r` >>
  rename1 `(if hash then compile_keccak256_key q F else comp_return q) r = (hop,hs)` >>
  `EVERY runtime_sym_inst (state_insts hs) /\ ~is_label_operand hop` by
    (irule runtime_sym_optional_hash >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`hash`,`q`,`r`] >> asm_rewrite_tac[]) >>
  Cases_on `compile_mapping_subscript bop hop hs` >>
  rename1 `compile_mapping_subscript bop hop hs = (slot,ss)` >>
  `EVERY runtime_sym_inst (state_insts ss) /\ ~is_label_operand slot` by metis_tac[] >>
  qpat_x_assum `!op b s out s'. _` kall_tac >>
  qpat_x_assum `!bop key s out s'. _` kall_tac >>
  gvs[comp_bind_def, comp_return_def, runtime_sym_value_def, mk_ptr_def]
QED

Theorem runtime_sym_locate_sequence:
  (!op t. comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  comp_bind comp (\op. comp_return (LocatedValue rt (mk_ptr op loc))) s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `comp s` >> simp[comp_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> simp[runtime_sym_value_def, mk_ptr_def]
QED

Theorem runtime_sym_operand_sequence:
  (!op t. comp s = (op,t) ==>
     EVERY runtime_sym_inst (state_insts t) /\ ~is_label_operand op) /\
  (!op t out u. EVERY runtime_sym_inst (state_insts t) /\
     ~is_label_operand op /\ next op t = (out,u) ==>
     EVERY runtime_sym_inst (state_insts u) /\ ~is_label_operand out) /\
  comp_bind comp next s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  Cases_on `comp s` >> simp[comp_bind_def] >> metis_tac[]
QED

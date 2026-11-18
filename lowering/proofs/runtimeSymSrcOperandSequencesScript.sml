Theory runtimeSymSrcOperandSequences
Ancestors
  runtimeSymSrcInterfaces exprLowering compileEnv context

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

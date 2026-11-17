Theory o1LabelFlowSimplifyJump
Ancestors
  list option venomWf venomInst unitShapeDefs venomExecProps cfgTransform simplifyCfgDefs codegenSymRel
  simplifyCfgShape simplifyCfgStruct
  o1LabelFlowLateSimplify simplifyCfgInvariant simplifyCfgBypassDataflow

Theorem jump_ordinary_inst_retained:
  wf_function f /\ lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  MEM bb f.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM i bb.bb_instructions /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> PHI ==>
  MEM i (fn_insts g)
Proof
  strip_tac >>
  qpat_x_assum `do_merge_jump _ _ _ _ = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `bb.bb_label = a.bb_label ==> bb = a` by
    metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def, SOME_11] >>
  `bb.bb_label = target_lbl ==> bb = target` by
    metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def, SOME_11] >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff, MEM_MAP, replace_block_def,
      remove_block_def, MEM_FILTER, PULL_EXISTS] >>
  qexists `bb` >> simp[] >>
  Cases_on `bb.bb_label = a.bb_label` >>
  Cases_on `bb.bb_label = target_lbl` >> gvs[] >>
  simp[MEM_MAP, PULL_EXISTS] >>
  qexists `i` >> simp[update_phi_bypass_def]
QED

Theorem jump_producer_retained:
  wf_function f /\ fn_inst_wf f /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') /\
  MEM i (fn_insts f) /\ MEM x i.inst_outputs /\
  (i.inst_opcode = ADD \/ i.inst_opcode = ASSIGN) ==>
  MEM i (fn_insts g)
Proof
  strip_tac >>
  gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
  `bb.bb_label <> b.bb_label` by
    (strip_tac >>
     `bb = b` by metis_tac[MEM_lookup_block, wf_function_def, fn_labels_def, SOME_11] >>
     gvs[] >>
     `MEM b f.fn_blocks` by metis_tac[lookup_block_member_label] >>
     drule_all bypassed_block_no_outputs >> metis_tac[MEM]) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI` by
    simp[is_terminator_def] >>
  drule_all jump_ordinary_inst_retained >>
  simp[fn_insts_def, MEM_fn_insts_blocks_iff]
QED

Theorem jump_ordinary_origin:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') ==>
  !i. MEM i (fn_insts g) /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> PHI ==> MEM i (fn_insts f)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
              MEM i (fn_insts f)) (fn_insts g)` suffices_by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  irule do_merge_jump_every >> conj_tac
  >- (simp[update_phi_bypass_opcode] >> rpt strip_tac >>
      gvs[update_phi_bypass_def]) >>
  conj_tac
  >- (simp[] >> rpt strip_tac >>
      `is_terminator (canon_jnz_inst (subst_label_inst old new i)).inst_opcode` by
        (irule canon_jnz_inst_opcode_property >>
         simp[subst_label_inst_def, is_terminator_def]) >>
      gvs[]) >>
  qexistsl [`a`, `b`, `f`, `lm`, `lm'`] >> simp[EVERY_MEM]
QED

Theorem jump_code_end_forward:
  !f x. code_end_var f x ==>
  !a b lm g lm'. wf_function f /\ fn_inst_wf f /\
    lookup_block a.bb_label f.fn_blocks = SOME a /\
    lookup_block b.bb_label f.fn_blocks = SOME b /\
    can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') ==>
    code_end_var g x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts g)` by
    (irule jump_producer_retained >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem jump_code_end_backward:
  !g x. code_end_var g x ==>
  !f a b lm lm'. lookup_block a.bb_label f.fn_blocks = SOME a /\
    do_merge_jump f a b lm = SOME (g,lm') ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts f)` by
    (irule jump_ordinary_origin >> simp[is_terminator_def] >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED


Theorem jump_restricted_uses:
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  !i x. MEM i (fn_insts g) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >>
  `EVERY (\i. !x. MEM (Var x) i.inst_operands /\ code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
    (fn_insts g)` suffices_by (simp[EVERY_MEM] >> metis_tac[]) >>
  irule do_merge_jump_every >> conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by metis_tac[update_phi_bypass_var_subset] >>
      `i.inst_opcode <> PHI` by (first_x_assum drule >> simp[] >> strip_tac >> gvs[]) >>
      gvs[update_phi_bypass_def]) >>
  conj_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      `MEM (Var x) i.inst_operands` by
        metis_tac[canon_jnz_inst_var_subset, subst_label_inst_use_source] >>
      first_x_assum drule >> simp[] >> strip_tac >> gvs[is_terminator_def]) >>
  qexistsl [`a`, `b`, `f`, `lm`, `lm'`] >>
  gvs[EVERY_MEM, label_flow_ok_def] >> metis_tac[]
QED

(* Only the structural facts used by producer retention are needed here;
   the collapse callback's other SSA/reachability facts can be threaded
   independently using do_merge_jump_ssa_invariant. *)
Theorem simplify_do_merge_jump_label_flow:
  wf_function f /\ fn_inst_wf f /\
  label_flow_ok (ctx with ctx_functions := [f]) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (g,lm') ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  strip_tac >> simp[label_flow_ok_def] >>
  gen_tac >> strip_tac >>
  `inst.inst_opcode = CODESIZE ==> MEM inst (fn_insts f)` by
    (strip_tac >> irule jump_ordinary_origin >>
     simp[is_terminator_def] >> metis_tac[]) >>
  `inst.inst_opcode = CODECOPY ==> MEM inst (fn_insts f)` by
    (strip_tac >> irule jump_ordinary_origin >>
     simp[is_terminator_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[label_flow_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `code_end_var f x` by metis_tac[jump_code_end_backward] >>
      metis_tac[jump_restricted_uses]) >>
  strip_tac >>
  `?dst src sz. inst.inst_operands = [dst; src; sz] /\
    (src = Label "runtime_begin" \/ ?x. src = Var x /\ code_end_var f x)` by
    (gvs[label_flow_ok_def] >> metis_tac[]) >>
  metis_tac[jump_code_end_forward]
QED

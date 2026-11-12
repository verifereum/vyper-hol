(* Root frame for the actual entry, with every defined administrative operand.
   Unlike the legacy prologue interface, this admits an immutable reservation. *)
Theory bodyIntCallActualRootFrame
Ancestors
  bodyIntCallRootFrame bodyIntCallJointEntry bodyIntCallActualEntryFields
  bodyIntCallJointContract compileEnv venomState arithmetic

Theorem internal_entry_reserved_operands:
  rpc = Var x /\ not_fresh_at st x /\
  lookup_var x landing = SOME pc /\
  (!op sz. ce.ce_return_buf = SOME (PtrVar op sz) ==>
       ?x w. op = Var x /\ not_fresh_at st x /\
             lookup_var x landing = SOME w) /\
  (!op. ce.ce_imm_alloca = SOME op ==>
       ?x w. op = Var x /\ not_fresh_at st x /\
             lookup_var x landing = SOME w) ==>
  ?reserved.
    (!op. reserved op <=> op = rpc \/
      (?sz. ce.ce_return_buf = SOME (PtrVar op sz)) \/
      ce.ce_imm_alloca = SOME op) /\
    reserved rpc /\
    (!op sz. ce.ce_return_buf = SOME (PtrVar op sz) ==> reserved op) /\
    (!op. ce.ce_imm_alloca = SOME op ==> reserved op) /\
    (!op. reserved op ==>
      ?x w. op = Var x /\ lookup_var x landing = SOME w) /\
    (!op x. reserved op /\ op = Var x ==> not_fresh_at st x)
Proof
  strip_tac >>
  qexists `\op. op = rpc \/
    (?sz. ce.ce_return_buf = SOME (PtrVar op sz)) \/
    ce.ce_imm_alloca = SOME op` >>
  simp[] >> conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* All compiler-specific facts are premises; geometry is independent of
   the placement of the immutable reservation within the entry sequence. *)
Theorem internal_entry_root_frame_exists:
  supported_program tops /\
  cxf.stk = owner::ancestors /\
  call_stack_follows (call_edge_rel edges) cxf.stk /\
  irreflexive (TC (call_edge_rel edges)) /\
  functions_follow_call_graph edges cxf /\
  evaluate_type (get_tenv cxf) ret = SOME rtv /\
  root.ce_return_pc = SOME (PtrVar rpc 0) /\
  cenv_module_pins tops root /\
  root.ce_returns_count = returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields root.ce_struct_fields name)) ret /\
  (has_rb <=> root.ce_returns_count = 0 /\ ret <> NoneT) /\
  (?x. rpc = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME pc) /\
  (!op sz. root.ce_return_buf = SOME (PtrVar op sz) ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME w) /\
  (!op. root.ce_imm_alloca = SOME op ==>
    ?x w. op = Var x /\ not_fresh_at st x /\ lookup_var x u = SOME w) /\
  (!a k. P a k ==> a + k <= lo) /\
  (!b z. staged b z ==> !a k. P a k ==> regions_disjoint a k b z) /\
  (has_rb ==> cap = type_memory_size rtv /\ w2n bw + cap <= lo /\
    (!b z. staged b z ==> regions_disjoint (w2n bw) cap b z) /\
    (!a k. P a k ==> regions_disjoint a k (w2n bw) cap)) ==>
  ?fp. intcall_frame_ok fp /\
    fp.jc_tops = tops /\ fp.jc_ctx = ctx /\ fp.jc_func = callee /\
    fp.jc_cx = cxf /\ fp.jc_owner = owner /\ fp.jc_ancestors = ancestors /\
    fp.jc_edges = edges /\ fp.jc_ret_ty = ret /\ fp.jc_ret_tv = rtv /\
    fp.jc_lo = lo /\ fp.jc_morig = origin /\ fp.jc_oorig = u /\
    fp.jc_root_ce = root /\ fp.jc_rpc = rpc /\ fp.jc_pc = pc /\
    fp.jc_rb = (if has_rb then SOME (bw,cap) else NONE) /\
    fp.jc_prot = P /\ fp.jc_staged = staged /\
    fp.jc_reserved = (\op. op = rpc \/
      (?sz. root.ce_return_buf = SOME (PtrVar op sz)) \/
      root.ce_imm_alloca = SOME op) /\
    (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at st x)
Proof
  strip_tac >> drule_all internal_entry_reserved_operands >> strip_tac >>
  qexists `<| jc_tops := tops; jc_ctx := ctx; jc_func := callee;
    jc_cx := cxf; jc_edges := edges; jc_owner := owner;
    jc_ancestors := ancestors; jc_lo := lo;
    jc_staged := staged; jc_prot := P;
    jc_morig := origin; jc_oorig := u; jc_root_ce := root;
    jc_ret_ty := ret; jc_ret_tv := rtv; jc_rpc := rpc; jc_pc := pc;
    jc_rb := (if has_rb then SOME (bw,cap) else NONE);
    jc_reserved := reserved |>` >>
  `reserved = (\op. op = rpc \/
    (?sz. root.ce_return_buf = SOME (PtrVar op sz)) \/
    root.ce_imm_alloca = SOME op)` by simp[FUN_EQ_THM] >>
  simp[IgnAsm `has_rb <=> _`, intcall_frame_ok_def] >>
  rpt conj_tac
  >~ [`call_stack_follows _ (owner::ancestors)`]
  >- (qpat_assum `cxf.stk = _` (fn th => rewrite_tac[GSYM th]) >> simp[])
  >~ [`eval_operand _ _ = _`] >- simp[eval_operand_def]
  >~ [`!id. supported_struct_fields tops id <> SOME []`]
  >- metis_tac[supported_program_struct_fields_nonempty] >>
  Cases_on `has_rb` >> gvs[]
QED

(* Single-slot TopLevelName materialization: memory and pointer checks on
   the same operational load/store run. *)
Theory bodyFullToplevelSlotSingle
Ancestors
  bodyFullUnwrapRun exprPtrUnwrapSingleSegment bodyStorageCopyMemory
  exprPtrUnwrapEnsureSingle bodyFullUnwrapSlotPost exprPtrUnwrapStoragePost
  exprLoweringProps bodyPtrDefs venomState venomInst words list rich_list

Theorem toplevel_slot_single_suffix_origin_ptr:
  compile_expr cenv ty (TopLevelName ann nsid) si = (LocatedValue vt p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb func /\
  emitted_insts sa sb =
    [mk_inst id (if p.ptr_location=LocStorage then SLOAD else TLOAD)
       [p.ptr_operand] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand p.ptr_operand s = SOME key /\ op_taint tn p.ptr_operand = {} /\
  root <> out /\ ptr_covers G tn root s 32 /\ lookup_var root s = SOME addr /\
  w2n addr + 32 < dimword (:256) /\ w2n addr + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    t = mstore (w2n addr)
      (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key)
      (update_var out
        (slot_copy_word (if p.ptr_location=LocStorage then SLOAD else TLOAD) s key) s) /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr+32}) UNION
      {w2n addr+k | k IN key_taint
        (if p.ptr_location=LocStorage then tn.t_stor else tn.t_trans) key} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> out ==> FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!x k. x <> out /\ ptr_covers G tn x s k ==> ptr_covers Gf tnf x t k)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  mp_tac (Q.INST [`fn` |-> `func`, `src` |-> `p.ptr_operand`,
    `load` |-> `if p.ptr_location=LocStorage then SLOAD else TLOAD`]
    copy_single_slot_segment) >>
  (impl_tac >- (simp[] >> Cases_on `p.ptr_location=LocStorage` >> simp[])) >>
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (asm_rewrite_tac[] >> irule body_storage_singleton_mem_ok >>
     simp[eval_operand_def] >> qexists `w2n addr` >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    gvs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND, DROP_LENGTH_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (asm_rewrite_tac[] >> Cases_on `p.ptr_location=LocStorage` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf)` by
    (irule emitted_origin_ptr_path >> metis_tac[]) >>
  qexistsl [`Gf`, `tnf`, `t`] >> asm_rewrite_tac[] >>
  Cases_on `p.ptr_location=LocStorage` >> gvs[]
QED

(* Scratch stores relative to the suffix entry. *)
Theory bodyIntCallFamAggSubscriptScratchTail
Ancestors
  bodyIntCallFamAggSubscriptScratchStages bodyIntCallFamAggSubscriptStore
  bodyIntCallFamAggSubscriptScratch bodyIntCallJointContract
  exprSimProps exprSimDefs exprSimCopy exprLoweringProps intCallFrame context compileEnv
  venomState venomInst

Theorem intcall_scratch_store_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 es si s /\
  emit_void MSTORE [ptr_op; value] si = ((),sb) /\
  eval_operand ptr_op s = SOME addr /\ eval_operand value s = SOME w /\
  fn_has_code si sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  sa.cs_next_id <= inst.inst_id /\
  b <= w2n addr /\ w2n addr + 32 <= b + sz /\
  sa.cs_next_var <= si.cs_next_var /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     regions_disjoint b sz lb len) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func s 0
    (OK (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  intcall_expr_cont fp ce env es sa s0 es sb
    (mstore (w2n addr) w s with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `!n lb len. local_region ce es.scopes s n lb len ==>
      regions_disjoint b sz lb len` by
    (rpt strip_tac >> first_x_assum irule >> qexists_tac `n` >>
     irule local_region_frame >>
     conj_tac
     >- (qexists_tac `fp.jc_func` >>
         fs[intcall_joint_res_def, stmt_state_rel_def,
            state_rel_def]) >>
     qexistsl_tac [`sa`, `es.scopes`, `s`] >>
     fs[intcall_expr_cont_def, intcall_joint_res_def]) >>
  irule intcall_allocated_mstore_landing >> simp[] >>
  conj_tac >- fs[intcall_expr_cont_def, intcall_joint_res_def, stmt_state_rel_def] >>
  conj_tac
  >- (qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >>
      conj_tac >- (gvs[regions_disjoint_def] >> gvs[]) >>
      conj_tac >- (gvs[regions_disjoint_def] >> metis_tac[]) >>
      fs[intcall_expr_cont_def, intcall_joint_res_def, allocas_above_def] >>
      qpat_x_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
        drule >> simp[]) >>
  qexistsl_tac [`ptr_op`, `si`, `value`] >> simp[]
QED

(* Finish the scratch region after its first word is initialized.  The hash
   contents are intentionally opaque here: this boundary retains resources. *)
Theorem intcall_scratch_tail_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s0 /\
  intcall_expr_cont fp ce env es sa s0 es sn s /\
  gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK s) /\
  emit_op ADD [buf; Lit 32w] sn = (dst,sp) /\
  emit_void MSTORE [dst; key] sp = ((),sq) /\
  emit_op SHA3 [buf; Lit 64w] sq = (op,sb) /\
  fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
  fn_has_code sq sb fp.jc_func /\
  MEM inst (fn_insts fp.jc_func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n addr,64) /\
  sa.cs_next_id <= inst.inst_id /\ w2n addr + 64 < dimword (:256) /\
  sa.cs_next_var <= sn.cs_next_var /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  (!x. buf = Var x ==> not_fresh_at sn x) /\
  eval_operand buf s = SOME addr /\ eval_operand key s0 = SOME w /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
     regions_disjoint (w2n addr) 64 lb len) ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s0 es sb u /\
      (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all intcall_emit_add_cont >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sa s0 es sp added` >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK added)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `eval_operand key added = SOME w` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand >>
     qexists_tac `sa` >> simp[] >>
     goal_assum (drule_at Any) >> fs[intcall_expr_cont_def]) >>
  `sa.cs_next_var <= sp.cs_next_var` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_then Any strip_assume_tac emitHelperPropsTheory.emitted_insts_emit_op) >>
     simp[]) >>
  `w2n (addr + 32w) = w2n addr + 32` by
    simp[wordsTheory.w2n_add_2] >>
  `gas_marked_path F fp.jc_ctx fp.jc_func added 0
      (OK (mstore (w2n (addr + 32w)) w added with
        vs_inst_idx := LENGTH sq.cs_current_insts)) /\
   intcall_expr_cont fp ce env es sa s0 es sq
      (mstore (w2n (addr + 32w)) w added with
        vs_inst_idx := LENGTH sq.cs_current_insts)` by
    (irule intcall_scratch_store_cont >> simp[] >>
     conj_tac
     >- (qexistsl_tac [`w2n addr`, `inst`, `64`] >>
         gvs[venom_state_component_equality] >> gvs[]) >>
     qexistsl_tac [`dst`, `sp`, `key`] >> simp[]) >>
  qmatch_asmsub_abbrev_tac
    `intcall_expr_cont fp ce env es sa s0 es sq stored` >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s0 0 (OK stored)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `eval_operand buf added = SOME addr` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_saved_operand >>
     qexistsl_tac [`sn`, `fp.jc_ctx`, `fp.jc_func`, `F`, `0`, `s`] >> simp[]) >>
  `eval_operand buf stored = SOME addr` by
    simp[Abbr `stored`, mstore_def, eval_operand_def, lookup_var_def] >>
  `sa.cs_next_var <= sq.cs_next_var` by
    (drule emitHelperPropsTheory.emitted_insts_emit_void >> simp[]) >>
  `eval_operand (Lit 64w) stored = SOME 64w` by simp[eval_operand_def] >>
  `mem_bytes_at (w2n addr) (w2n (64w:bytes32)) stored.vs_memory =
     mem_bytes_at (w2n addr) 64 stored.vs_memory` by simp[] >>
  drule_all intcall_emit_sha3_cont >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all fragGasModeTheory.gas_marked_path_then >> simp[] >>
  strip_tac >> qexists_tac `u` >> simp[]
QED

(* Compiler layout boundary for the counted checked storage-copy loop. *)
Theory storageCopyCompiledPtr
Ancestors
  storageCopyIterationPtr storageCopyGasPath exprSimStorageCopy fragExec
  exprLoweringProps emitHelper compileEnv venomInst storageCopyInvariantPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun venomState storageCopyControlPtr fragGasPathPtr

Theorem storage_copy_compiled_layout_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn ==>
  ?hdr body_lbl exit cv tv sv vv mv dv nv hid bid entry_jump_id backedge_id eb hb bb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME eb /\
    isPREFIX [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv];
              mk_inst entry_jump_id JMP [Label hdr] []]
      (DROP (LENGTH sa.cs_current_insts) eb.bb_instructions) /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    hb.bb_instructions =
      [mk_inst hid EQ [Var cv; Lit (n2w n)] [tv];
       mk_inst (hid+1) JNZ [Var tv; Label exit; Label body_lbl] []] /\
    lookup_block body_lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst bid ADD [src; Var cv] [sv];
       mk_inst (bid+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (bid+2) MUL [Var cv; Lit 32w] [mv];
       mk_inst (bid+3) ADD [dst; Var mv] [dv];
       mk_inst (bid+4) MSTORE [Var dv; Var vv] [];
       mk_inst (bid+5) ADD [Var cv; Lit 1w] [nv];
       mk_inst (bid+6) ASSIGN [Var nv] [cv];
       mk_inst backedge_id JMP [Label hdr] []] /\
    sb.cs_current_bb = exit /\ sb.cs_current_insts = [] /\
    ALL_DISTINCT [cv;tv;sv;vv;mv;dv;nv] /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;sv;vv;mv;dv;nv])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_storage_copy_certificate >> strip_tac >>
  gvs[new_block_def, emit_inst_def, emit_op_def, fresh_id_def,
      fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      same_blocks_def, emitted_insts_def] >>
  qpat_x_assum `compile_word_copy_loop _ _ _ _ _ _ _ = _` kall_tac >>
  fs[fn_has_code_def, emitted_blocks_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  `s0.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]]` by
    metis_tac[prefix_drop_equiv] >>
  qexistsl_tac [`hdr`, `ste.cs_current_bb`, `cv`,
    `STRING #"%" (toString s0.cs_next_var)`, `sv`, `vv`, `mv`, `dv`, `nv`,
    `s0.cs_next_id+1`, `s0.cs_next_id+3`, `s0.cs_next_id`, `ste.cs_next_id`] >>
  simp[] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem storage_copy_compiled_init_inv_ptr:
  eval_operand src s = SOME a /\ lookup_var root s = SOME (n2w b) /\
  ptr_covers G tn root s (32*n) /\ op_taint tn src = {} /\
  cv IN scratch /\ cv <> root /\ src <> Var cv ==>
  storage_copy_inv_ptr loc src root cv scratch a b n s G tn 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (jump_to hdr (update_var cv 0w s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> simp[] >> Cases_on `src` >>
  gvs[storage_copy_inv_ptr_def, copy_prefix_update_var, copy_prefix_zero,
      eval_operand_def, lookup_var_def, update_var_def, ptr_covers_def,
      op_prov_def, op_taint_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DRESTRICT, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem storage_copy_entry_fetch_ptr[local]:
  isPREFIX [i;j] (DROP k bb.bb_instructions) ==>
  get_instruction bb k = SOME i /\ get_instruction bb (SUC k) = SOME j
Proof
  pure_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  `bb.bb_instructions = TAKE k bb.bb_instructions ++ [i;j] ++ l` by
    metis_tac[listTheory.TAKE_DROP, listTheory.APPEND_ASSOC] >>
  `k <= LENGTH bb.bb_instructions` by
    (`LENGTH (DROP k bb.bb_instructions) = 2 + LENGTH l` by
       (asm_rewrite_tac[] >> simp[]) >>
     fs[listTheory.LENGTH_DROP] >> decide_tac) >>
  `LENGTH (TAKE k bb.bb_instructions) = k` by simp[] >>
  simp[get_instruction_def] >>
  qpat_x_assum `bb.bb_instructions = _` (fn th => pure_once_rewrite_tac[th]) >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]
QED

Theorem compile_storage_copy_content_capacity_path_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src (Var root) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ root = x ==> not_fresh_at sa x) /\
  eval_operand src sbase = SOME a /\ lookup_var root sbase = SOME (n2w b) /\
  op_taint tn src = {} /\ ptr_covers G tn root sbase (32*n) /\
  n < dimword(:256) /\ b+32*n < dimword(:256) /\
  ~sbase.vs_halted /\ ~ctx_has_dalloca ctx /\
  sbase.vs_current_bb = sa.cs_current_bb /\
  sbase.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn sbase 0 G' tn' (OK t) /\
    copy_prefix loc a b n sbase n t /\ ptr_covers G' tn' root t (32*n) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    tn'.t_mem = (tn.t_mem DIFF {x | b <= x /\ x < b+32*n}) UNION
      {b+32*i+r | i < n /\ r < 32 /\
        (a+n2w i,r) IN (if loc = LocStorage then tn.t_stor else tn.t_trans)} /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x sbase /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_copy_compiled_layout_ptr >> strip_tac >>
  `~MEM root [cv;tv;sv;vv;mv;dv;nv]` by metis_tac[] >>
  `!x. MEM x [cv;tv;sv;vv;mv;dv;nv] ==> src <> Var x` by metis_tac[] >>
  `get_instruction eb sbase.vs_inst_idx = SOME
     (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv]) /\
   get_instruction eb (SUC sbase.vs_inst_idx) = SOME
     (mk_inst entry_jump_id JMP [Label hdr] [])` by
    (simp[] >> irule storage_copy_entry_fetch_ptr >> simp[]) >>
  `lookup_block sbase.vs_current_bb fn.fn_blocks = SOME eb` by simp[] >>
  drule_all storage_copy_init_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK s1` >>
  `storage_copy_inv_ptr loc src root cv (set [cv;tv;sv;vv;mv;dv;nv])
    a b n sbase G tn 0 (DRESTRICT G (COMPL {cv}))
    (tn with t_var := tn.t_var |+ (cv,{})) s1` by
    (unabbrev_all_tac >> irule storage_copy_compiled_init_inv_ptr >>
     fs[] >> metis_tac[]) >>
  suspend "iterate"
QED

Resume compile_storage_copy_content_capacity_path_ptr[iterate]:
  `ALL_DISTINCT [sv;vv;mv;dv;nv;cv;root;tv] /\
   EVERY (\x. x IN set [cv;tv;sv;vv;mv;dv;nv] /\ src <> Var x)
     [sv;vv;mv;dv;nv;cv;tv]` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[]) >>
  `s1.vs_current_bb = hdr /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted` by
    simp[Abbr `s1`, jump_to_def, update_var_def] >>
  `0+n = n` by simp[] >>
  drule_all storage_copy_iterate_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> conj_tac
  >- (irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
      qexistsl_tac [`DRESTRICT G (COMPL {cv})`, `s1`,
        `tn with t_var := tn.t_var |+ (cv,{})`] >> simp[]) >>
  fs[storage_copy_inv_ptr_def] >> metis_tac[]
QED

Finalise compile_storage_copy_content_capacity_path_ptr

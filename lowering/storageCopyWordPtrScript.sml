(* The single-word storage/transient normalizer, without a loop counter. *)
Theory storageCopyWordPtr
Ancestors
  storageCopyBodyPtr exprSimStorageCopy decoderGhostFramePtr payloadLoadStorePtr
  normalizerAllocationFrame
  fragGasPathPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst fragExec finite_map list arithmetic words pred_set

Theorem storage_copy_word_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id (if tr then TLOAD else SLOAD) [src] [out];
     mk_inst (id+1) MSTORE [Var root;Var out] []] ++ post /\
  s.vs_inst_idx = LENGTH pre /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s 32 /\
  root <> out /\ src <> Var out /\ w2n b+32 < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx+2 /\
    copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) 1 s 1 t /\
    eval_operand src t = SOME a /\ op_taint tn' src = {} /\
    lookup_var root t = SOME b /\ ptr_covers G' tn' root t 32 /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!h. h < 32 ==> (w2n b+h IN tn'.t_mem <=>
        (a,h) IN (if tr then tn'.t_trans else tn'.t_stor))) /\
    (!i. (i < w2n b \/ w2n b+32 <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ((t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
     alloca_inv t /\ alloca_room ctx fn t /\
     (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
       i.inst_operands = [Lit w] /\
       FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id (if tr then TLOAD else SLOAD) [src] [out])`
      by simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all storage_copy_load_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK ls` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gl tl` >>
  suspend "store"
QED
Resume storage_copy_word_path_ptr[store]:
  `~ls.vs_halted /\ lookup_block ls.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb ls.vs_inst_idx = SOME (mk_inst (id+1) MSTORE [Var root;Var out] []) /\
   eval_operand (Var root) ls = SOME b /\
   eval_operand (Var out) ls = SOME (if tr then tload a s else sload a s) /\
   ptr_covers Gl tl root ls 32` by
    (simp[Abbr `ls`, Abbr `Gl`, Abbr `tl`, get_instruction_def,
          EL_APPEND_EQN, update_var_def, lookup_var_def, eval_operand_def,
          FLOOKUP_UPDATE, ptr_covers_def, FLOOKUP_DRESTRICT, op_taint_def] >>
     gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  drule_all storage_copy_store_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK fs'` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG Gl tl ls 0 Gl tf` >>
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  qexistsl [`Gl`, `tf`, `fs'`] >>
  suspend "word_frames"
QED
Resume storage_copy_word_path_ptr[word_frames]:
  `copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) 1 s 1 fs'` by
    (simp[Abbr `fs'`, copy_prefix_idx] >>
     `copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) 1 s 0 ls`
       by simp[Abbr `ls`, copy_prefix_idx, copy_prefix_update_var, copy_prefix_zero] >>
     `copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) 1 s (0+1)
       (mstore (w2n b+32*0)
         (copy_runtime_word (if tr then LocTransient else LocStorage) s (a+n2w 0)) ls)`
       by (irule copy_prefix_extend >> simp[]) >>
     Cases_on `tr` >> gvs[copy_runtime_word_def, WORD_ADD_0]) >>
  drule_all copy_prefix_recorded_resources >> strip_tac >>
  simp[] >>
  simp[Abbr `fs'`, Abbr `ls`, Abbr `Gl`, Abbr `tf`, Abbr `tl`,
       update_var_def, mstore_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  suspend "observations"
QED
Resume storage_copy_word_path_ptr[observations]:
  gvs[ptr_covers_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      op_taint_def, key_taint_def] >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  TRY (rename1 `sz = w2n w` >>
       qpat_x_assum `!i w p sz. _ ==> sz = w2n w` drule_all >>
       simp[] >> NO_TAC) >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED
Finalise storage_copy_word_path_ptr

Theory createCopyExecution
Ancestors
  createMemoryInterface createFrameInterface createSourceCallback fragExec context contextProps
  emitHelperProps exprLoweringProps venomMemProps venomExecSemantics
  compileEnv emitHelper venomInst venomState list rich_list

(* Dynamic copying is one MCOPY, not a compiler-generated loop.  Lift its
   checked execution to the compositional CFG interface. *)
Theorem compile_create_dynamic_copy_frag:
  compile_copy_memory_dynamic dst src len cs = ((),cs') ==>
  cs_extends cs cs' /\
  frag_exec ctx cs cs'
    (\s. fresh_vars_wrt cs s /\
         eval_operand dst s = SOME d /\ eval_operand src s = SOME p /\
         eval_operand len s = SOME n /\ create_live live s /\
         create_memory_snapshot regions s /\
         EVERY (\(off,bs). off + LENGTH bs <= LENGTH s.vs_memory /\
           (off + LENGTH bs <= w2n d \/ w2n d + w2n n <= off)) regions /\
         read_memory (w2n p) (w2n n) s = bytes)
    (\s. fresh_vars_wrt cs' s /\ create_live live s /\
         create_memory_snapshot ((w2n d,bytes)::regions) s)
    (K F)
Proof
  strip_tac >> conj_tac
  >- (fs[compile_copy_memory_dynamic_def] >>
      metis_tac[cs_appends_def, cs_appends_emit_helpers]) >>
  irule frag_exec_run_inst_seq >>
  `emit_void MCOPY [dst;src;len] cs = ((),cs')` by
    fs[compile_copy_memory_dynamic_def] >>
  drule emit_void_extends >>
  drule emitted_insts_emit_void >>
  simp[same_blocks_def] >> strip_tac >> strip_tac >>
  gvs[IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  drule_all compile_create_copy_dynamic_execution >>
  strip_tac >> qexists_tac `s'` >> simp[] >>
  `LENGTH bytes = w2n n` by
    (qpat_x_assum `read_memory _ _ _ = bytes`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[read_memory_def]) >>
  `create_memory_snapshot [(w2n d,bytes)] s'` by
    metis_tac[create_copy_snapshot] >>
  `create_memory_snapshot regions s'` by
    (gvs[mcopy_def] >>
     irule create_snapshot_disjoint_write >> simp[] >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  gvs[fresh_vars_wrt_def, create_live_def, create_memory_snapshot_def,
      eval_operand_def, lookup_var_def, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  qpat_x_assum `!e. MEM e live ==> _` (qspec_then `(e0,e1)` mp_tac) >>
  simp[] >> strip_tac >>
  `eval_operand e0 (mcopy (w2n d) (w2n p) (w2n n) s) = SOME e1` by
    metis_tac[] >>
  Cases_on `e0` >> gvs[eval_operand_def, lookup_var_def,
    mcopy_def, write_memory_with_expansion_def]
QED

(* Names and blocks of the production storage/transient copy loop. *)
Definition slot_copy_var_def:
  slot_copy_var cs k = "%" ++ toString (cs.cs_next_var + k)
End

Definition slot_copy_cond_def:
  slot_copy_cond cs = fresh_label_output "wcopy_cond" cs.cs_next_label
End
Definition slot_copy_body_def:
  slot_copy_body cs = fresh_label_output "wcopy_body" (cs.cs_next_label + 1)
End
Definition slot_copy_exit_def:
  slot_copy_exit cs = fresh_label_output "wcopy_exit" (cs.cs_next_label + 2)
End

Definition slot_copy_init_insts_def:
  slot_copy_init_insts cs =
    [mk_inst cs.cs_next_id ASSIGN [Lit 0w] [slot_copy_var cs 0];
     mk_inst (cs.cs_next_id + 1) JMP [Label (slot_copy_cond cs)] []]
End
Definition slot_copy_cond_insts_def:
  slot_copy_cond_insts cs n =
    [mk_inst (cs.cs_next_id + 2) EQ
       [Var (slot_copy_var cs 0); Lit (n2w n)] [slot_copy_var cs 1];
     mk_inst (cs.cs_next_id + 3) JNZ
       [Var (slot_copy_var cs 1); Label (slot_copy_exit cs);
        Label (slot_copy_body cs)] []]
End
Definition slot_copy_body_insts_def:
  slot_copy_body_insts cs src dst load =
    [mk_inst (cs.cs_next_id + 4) ADD [src; Var (slot_copy_var cs 0)]
       [slot_copy_var cs 2];
     mk_inst (cs.cs_next_id + 5) load [Var (slot_copy_var cs 2)]
       [slot_copy_var cs 3];
     mk_inst (cs.cs_next_id + 6) MUL [Var (slot_copy_var cs 0); Lit 32w]
       [slot_copy_var cs 4];
     mk_inst (cs.cs_next_id + 7) ADD [dst; Var (slot_copy_var cs 4)]
       [slot_copy_var cs 5];
     mk_inst (cs.cs_next_id + 8) MSTORE
       [Var (slot_copy_var cs 5); Var (slot_copy_var cs 3)] [];
     mk_inst (cs.cs_next_id + 9) ADD [Var (slot_copy_var cs 0); Lit 1w]
       [slot_copy_var cs 6];
     mk_inst (cs.cs_next_id + 10) ASSIGN [Var (slot_copy_var cs 6)]
       [slot_copy_var cs 0];
     mk_inst (cs.cs_next_id + 11) JMP [Label (slot_copy_cond cs)] []]
End
Definition slot_copy_blocks_def:
  slot_copy_blocks cs src dst n load =
    [<|bb_label := slot_copy_body cs;
       bb_instructions := slot_copy_body_insts cs src dst load|>;
     <|bb_label := slot_copy_cond cs;
       bb_instructions := slot_copy_cond_insts cs n|>;
     <|bb_label := cs.cs_current_bb;
       bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|>]
End
Definition slot_copy_final_def:
  slot_copy_final cs src dst n load =
    cs with <|cs_next_label := cs.cs_next_label + 3;
              cs_next_var := cs.cs_next_var + 7;
              cs_next_id := cs.cs_next_id + 12;
              cs_blocks := slot_copy_blocks cs src dst n load ++ cs.cs_blocks;
              cs_current_bb := slot_copy_exit cs;
              cs_current_insts := []|>
End

Theorem compile_slot_to_memory_shape:
  (loc = LocStorage \/ loc = LocTransient) ==>
  compile_slot_to_memory src dst n loc cs =
    (slot_copy_body cs,
     slot_copy_final cs src dst n (if loc = LocStorage then SLOAD else TLOAD))
Proof
  strip_tac >> gvs[] >>
  simp[compile_slot_to_memory_def, compile_word_copy_loop_def,
       word_scale_def, compile_ptr_load_def, compile_ptr_store_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_void_def, emit_def, new_block_def,
       slot_copy_final_def, slot_copy_blocks_def, slot_copy_init_insts_def,
       slot_copy_cond_insts_def, slot_copy_body_insts_def, slot_copy_var_def,
       slot_copy_body_def, slot_copy_cond_def, slot_copy_exit_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem slot_copy_extends:
  cs_extends cs (slot_copy_final cs src dst n load)
Proof
  simp[cs_extends_def, slot_copy_final_def, slot_copy_blocks_def,
       IS_PREFIX_APPEND]
QED

Theorem slot_copy_emitted_blocks:
  emitted_blocks cs (slot_copy_final cs src dst n load) =
    slot_copy_blocks cs src dst n load
Proof
  simp[emitted_blocks_def, slot_copy_final_def, slot_copy_blocks_def]
QED

Theorem slot_copy_lookup:
  fn_has_code cs (slot_copy_final cs src dst n load) fn ==>
  lookup_block (slot_copy_body cs) fn.fn_blocks =
    SOME <|bb_label := slot_copy_body cs;
           bb_instructions := slot_copy_body_insts cs src dst load|> /\
  lookup_block (slot_copy_cond cs) fn.fn_blocks =
    SOME <|bb_label := slot_copy_cond cs;
           bb_instructions := slot_copy_cond_insts cs n|> /\
  lookup_block cs.cs_current_bb fn.fn_blocks =
    SOME <|bb_label := cs.cs_current_bb;
           bb_instructions := cs.cs_current_insts ++ slot_copy_init_insts cs|> /\
  ?bb. lookup_block (slot_copy_exit cs) fn.fn_blocks = SOME bb
Proof
  simp[fn_has_code_def, slot_copy_emitted_blocks, slot_copy_final_def,
       slot_copy_blocks_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem slot_copy_labels_distinct:
  slot_copy_cond cs <> slot_copy_body cs /\
  slot_copy_cond cs <> slot_copy_exit cs /\
  slot_copy_body cs <> slot_copy_exit cs
Proof
  simp[slot_copy_cond_def, slot_copy_body_def, slot_copy_exit_def] >>
  metis_tac[fresh_label_output_inj, DECIDE ``n <> n + 1``,
            DECIDE ``n <> n + 2``, DECIDE ``n + 1 <> n + 2``]
QED

Theorem slot_copy_var_distinct:
  slot_copy_var cs i = slot_copy_var cs j <=> i = j
Proof
  simp[slot_copy_var_def] >>
  metis_tac[fresh_var_distinct, DECIDE ``b + i = b + j <=> i = j``]
QED

Theorem slot_copy_var_not_live:
  fresh_vars_wrt cs s /\ eval_operand op s = SOME value /\
  op = Var name ==> name <> slot_copy_var cs k
Proof
  strip_tac >>
  `cs.cs_next_var + k >= cs.cs_next_var` by simp[] >>
  drule_all fresh_vars_wrt_eval_operand >>
  simp[slot_copy_var_def, arithmeticTheory.ADD_COMM]
QED

Theorem compile_slot_to_memory_boundary:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_slot_to_memory src dst n loc cs = (result,cs') ==>
  result = slot_copy_body cs /\
  cs' = slot_copy_final cs src dst n
          (if loc = LocStorage then SLOAD else TLOAD) /\
  cs_extends cs cs' /\
  cs'.cs_current_bb = slot_copy_exit cs /\
  cs'.cs_current_insts = [] /\
  cs'.cs_next_var = cs.cs_next_var + 7 /\
  cs'.cs_next_label = cs.cs_next_label + 3 /\
  cs'.cs_next_id = cs.cs_next_id + 12
Proof
  strip_tac >>
  gvs[compile_slot_to_memory_shape] >>
  simp[slot_copy_extends, slot_copy_final_def]
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createCopyExecution");

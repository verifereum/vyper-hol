(* Counted copy boundaries; fixed-run toolkit facts are used only for
   instruction safety and ghost updates, never to manufacture paths. *)
Theory annAssignPtrCopy
Ancestors
  annAssignPtrSetup typedCopyPtr fragExecPtr fragGasSeqPtr fragGasPathPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline venomInst venomInstProofs
  venomExecSemantics venomState venomMemDefs venomMemProofs
  context emitHelper emitHelperProps finite_map pred_set arithmetic
  compileEnv

Theorem annassign_mcopy_path_ptr:
 !D ctx func PG G tn s bb id dst src count_op a b n k.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx =
   SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
 w2n n = k /\ ptr_covers G tn src s k /\ ptr_covers G tn dst s k ==>
 gas_path_ptr D 0 ctx func PG G tn s 0 G
   (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
     (mcopy (w2n b) (w2n a) k s) tn)
   (OK ((mcopy (w2n b) (w2n a) k s) with
     vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `w2n n = k` (SUBST_ALL_TAC o SYM) >>
 `step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n b) (w2n a) (w2n n) s)` by
   (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
    simp[mk_inst_def, eval_operand_def]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
     (mcopy (w2n b) (w2n a) (w2n n) s))
   (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
     (mcopy (w2n b) (w2n a) (w2n n) s) tn)
   (OK ((mcopy (w2n b) (w2n a) (w2n n) s) with
     vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_mcopy_operand >> simp[]) >>
 gvs[mcopy_operand_ghost_frame, eval_operand_def] >>
 drule (cj 2 gas_path_ptr_rules) >>
 simp[mcopy_def, write_memory_with_expansion_def] >>
 disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
 simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem annassign_static_mcopy_ghost_word_ptr[local]:
 !PG G tn s id dst src a b n k.
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 w2n n = k ==>
 step_prov PG G (mk_inst id MCOPY [Var dst;Var src;Lit n] [])
   (mcopy (w2n b) (w2n a) k s) = G /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit n] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_var = tn.t_var /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit n] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_stor = tn.t_stor /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit n] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_trans = tn.t_trans /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit n] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_mem =
 (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + k}) UNION
 {w2n b + i | i < k /\ w2n a + i IN tn.t_mem}
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `w2n n = k` (SUBST_ALL_TAC o SYM) >>
 match_mp_tac mcopy_operand_ghost_frame >> simp[eval_operand_def]
QED

Theorem annassign_static_mcopy_ghost_ptr:
 !PG G tn s id dst src a b k.
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 k < dimword (:256) ==>
 step_prov PG G (mk_inst id MCOPY [Var dst;Var src;Lit (n2w k)] [])
   (mcopy (w2n b) (w2n a) k s) = G /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w k)] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_var = tn.t_var /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w k)] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_stor = tn.t_stor /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w k)] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_trans = tn.t_trans /\
 (step_taint (mk_inst id MCOPY [Var dst;Var src;Lit (n2w k)] []) s
   (mcopy (w2n b) (w2n a) k s) tn).t_mem =
 (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + k}) UNION
 {w2n b + i | i < k /\ w2n a + i IN tn.t_mem}
Proof
 rpt gen_tac >> strip_tac >>
 irule annassign_static_mcopy_ghost_word_ptr >>
 simp[wordsTheory.w2n_n2w]
QED

(* The cursor and variable projections not exported by
   mcopy_preserves_frame_metadata.  Memory stays opaque to consumers. *)
Theorem annassign_mcopy_cursor_ptr:
 !dst src k s idx.
 (mcopy dst src k s).vs_current_bb = s.vs_current_bb /\
 (mcopy dst src k s).vs_inst_idx = s.vs_inst_idx /\
 (mcopy dst src k s).vs_halted = s.vs_halted /\
 (!x. lookup_var x (mcopy dst src k s with vs_inst_idx := idx) =
      lookup_var x s)
Proof
 simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED
Theorem annassign_mcopy_restore_ptr:
 !dst src k s idx.
 ((mcopy dst src k s with vs_inst_idx := idx) with
   <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
 simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem annassign_mcopy_taint_restore_ptr:
 !id dst src count_op s u tn.
 (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s u tn
   with t_mem := tn.t_mem) = tn
Proof
 simp[step_taint_def, instruction_accessors, set_var_taint_def,
      adopt_reset_def, store_taint_def, imm_taint_def,
      finite_mapTheory.DRESTRICT_UNIV, taint_component_equality]
QED


Theorem annassign_compile_copy_path_ptr:
 !D ctx func PG G tn s dst src a b k sa sb.
 compile_copy_memory (Var dst) (Var src) k sa = ((),sb) /\
 fn_has_code sa sb func /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ k < dimword (:256) /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s k /\ ptr_covers G tn dst s k ==>
 ?s' tn'. gas_path_ptr D 0 ctx func PG G tn s 0 G tn' (OK s') /\
 s'.vs_current_bb = sb.cs_current_bb /\
 s'.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s'.vs_halted /\
 (s' with <|vs_memory := s.vs_memory;vs_inst_idx := s.vs_inst_idx|>) = s /\
 (tn' with t_mem := tn.t_mem) = tn /\
 (!x. lookup_var x s' = lookup_var x s) /\
 s'.vs_memory = (if k = 0 then s.vs_memory
                else (mcopy (w2n b) (w2n a) k s).vs_memory) /\
 tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\
 tn'.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + k}) UNION
              {w2n b + i | i < k /\ w2n a + i IN tn.t_mem}
Proof
 rpt gen_tac >> strip_tac >> Cases_on `k`
 >- (gvs[compile_copy_memory_def, comp_return_def] >>
     qexistsl [`s`,`tn`] >>
     simp[venom_state_component_equality] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
 `emit_inst MCOPY [Var dst;Var src;Lit (n2w (SUC n))] [] sa =
    ((),sb)` by
   gvs[compile_copy_memory_def, emit_void_def, emit_inst_def] >>
 drule_all annassign_emit_instruction_ptr >> strip_tac >>
 `sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
   gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
 qexistsl [`mcopy (w2n b) (w2n a) (SUC n) s with
               vs_inst_idx := SUC s.vs_inst_idx`,
   `step_taint (mk_inst sa.cs_next_id MCOPY
     [Var dst;Var src;Lit (n2w (SUC n))] []) s
     (mcopy (w2n b) (w2n a) (SUC n) s) tn`] >>
 conj_tac
 >- (irule annassign_mcopy_path_ptr >>
     simp[eval_operand_def, op_taint_def, wordsTheory.w2n_n2w] >>
     metis_tac[]) >>
 simp[annassign_mcopy_cursor_ptr, annassign_static_mcopy_ghost_ptr,
      annassign_mcopy_restore_ptr, annassign_mcopy_taint_restore_ptr]
QED

(* Declaration scope extension is independent of the operation initializing
   its buffer. Word stores and memory copies share this ghost boundary. *)
Theory annAssignPtrStore
Ancestors
  bodyPtrDefs vyperState finite_map stmtSimDeclStore typedCopyPtr
  annAssignPtrSetup fragGasSeqPtr fragGasPathPtr fragExecPtr
  venomInst venomInstProofs venomExecSemantics venomState emitHelperProps
  representationCleanPtr valueEncodingProps valueEncoding list pred_set
  venomMemProofs valueEncodingProofs

Theorem annassign_ghost_scope_update_ptr:
 !d cenv cx es G tn s sc rest id entry p sz.
 es.scopes = sc :: rest /\
 ghost_inv d cenv cx es G tn s /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 ptr_covers G tn p s sz /\
 (!w mem. lookup_var p s = SOME w /\
           mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n w) mem) ==>
 ghost_inv d cenv cx
   (es with scopes := (sc |+ (id,entry)) :: rest) G tn s
Proof
 rpt gen_tac >> strip_tac >> fs[ghost_inv_def] >>
 rpt gen_tac >> strip_tac >> Cases_on `name = id`
 >- gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
 `lookup_scopes name es.scopes = SOME entry'` by
   gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
 first_x_assum drule_all >> simp[]
QED

Theorem annassign_mstore_path_ptr:
 !D ctx func PG G tn s bb id p value a w.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
 get_instruction bb s.vs_inst_idx =
   SOME (mk_inst id MSTORE [Var p; value] []) /\
 ptr_covers G tn p s 32 /\ op_taint tn value = {} /\
 lookup_var p s = SOME a /\ eval_operand value s = SOME w ==>
 gas_path_ptr D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) w s))
   (step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn)
   (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
 rpt gen_tac >> strip_tac >>
 `step_inst_base (mk_inst id MSTORE [Var p; value] []) s =
    OK (mstore (w2n a) w s)` by
   (irule step_MSTORE >> simp[eval_operand_def]) >>
 `gas_path_ptr_edge D 0 ctx func PG G tn s 0
   (step_prov PG G (mk_inst id MSTORE [Var p; value] []) (mstore (w2n a) w s))
   (step_taint (mk_inst id MSTORE [Var p; value] []) s (mstore (w2n a) w s) tn)
   (OK ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
   (drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
    disch_then (irule o SRULE [instruction_accessors, is_terminator_def]) >>
    simp[] >> irule ptr_inst_ok_mstore >> simp[]) >>
 drule (cj 2 gas_path_ptr_rules) >> simp[mstore_def] >>
 disch_then irule >> irule (cj 1 gas_path_ptr_rules) >> simp[mstore_def]
QED

Theorem annassign_clean_store_observation_ptr:
 !off wd s tm mem base n.
 mem_agree_outside (tm DIFF {i | off <= i /\ i < off + 32})
   (mstore off wd s).vs_memory mem ==>
 mem_bytes_at base n (mstore off wd (s with vs_memory := mem)).vs_memory =
 mem_bytes_at base n mem
Proof
 rpt gen_tac >> strip_tac >>
 `!i. mem_bytes_at i 1 (mstore off wd (s with vs_memory := mem)).vs_memory =
      mem_bytes_at i 1 mem` by
   (gen_tac >> Cases_on `off <= i /\ i < off + 32`
    >- (`mem_bytes_at i 1 (mstore off wd s).vs_memory = mem_bytes_at i 1 mem` by
          (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[]) >>
        `mem_bytes_at off 32 (mstore off wd (s with vs_memory := mem)).vs_memory =
         mem_bytes_at off 32 (mstore off wd s).vs_memory` by
          simp[mem_bytes_at_mstore_same] >>
        fs[] >> drule_all mem_bytes_at_eq_byte >> simp[]) >>
    `i + 1 <= off \/ off + 32 <= i` by decide_tac >>
    simp[mstore_mem_bytes_at_disjoint]) >>
 irule LIST_EQ >> simp[] >> rpt strip_tac >>
 rename1 `EL k (mem_bytes_at addr n mem)` >>
 first_x_assum (qspec_then `addr + k` mp_tac) >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem annassign_clean_store_layout_ptr:
 !ty v off wd s tm mem.
  val_wf ty v /\
  (!u. val_in_memory ty v off (mstore off wd u).vs_memory) /\
  mem_agree_outside (tm DIFF {i | off <= i /\ i < off + 32})
    (mstore off wd s).vs_memory mem ==>
  val_in_memory ty v off mem
Proof
 rpt gen_tac >> strip_tac >>
 irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
 qexistsl [`type_memory_size ty`,
   `(mstore off wd (s with vs_memory := mem)).vs_memory`] >> simp[] >>
 irule annassign_clean_store_observation_ptr >> metis_tac[]
QED

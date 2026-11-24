(* Opcode inventory and closed branches of the installed request suffix. *)
Theory entryCreateRawCallFinishCode
Ancestors
  createSizeCallCode createSizeCutCode exprSimAbiDecodeSiteCoverage
  exprSimAbiGasBridge exprSimRawCallCalldata builtinSystem builtinSimple context emitHelper
  compileEnv fragExec exprLoweringProps venomInst list rich_list pair
Libs
  monadsyntax

Theorem finish_inventory_join[local]:
  cs_extends a b /\ EVERY P (frag_code a b) /\
  cs_extends b c /\ EVERY P (frag_code b c) ==>
  cs_extends a c /\ EVERY P (frag_code a c)
Proof
  strip_tac >> drule_all abi_decode_frag_code_compose >>
  fs[EVERY_MEM] >> metis_tac[cs_extends_trans]
QED

Theorem finish_inventory_bind[local]:
  (cs_extends a (SND (m a)) /\ EVERY P (frag_code a (SND (m a)))) /\
  (!x b. cs_extends b (SND (k x b)) /\ EVERY P (frag_code b (SND (k x b)))) ==>
  cs_extends a (SND (comp_bind m k a)) /\
  EVERY P (frag_code a (SND (comp_bind m k a)))
Proof
  Cases_on `m a` >> simp[comp_bind_def] >> metis_tac[finish_inventory_join]
QED

Theorem finish_inventory_empty[local,simp]:
  cs_extends a (SND (comp_return v a)) /\ EVERY P (frag_code a (SND (comp_return v a))) /\
  cs_extends a (SND (fresh_label suffix a)) /\ EVERY P (frag_code a (SND (fresh_label suffix a))) /\
  cs_extends a (SND (new_block lbl a)) /\ EVERY P (frag_code a (SND (new_block lbl a)))
Proof
  `cs_extends a (SND (new_block lbl a))` by
    (Cases_on `new_block lbl a` >> simp[] >> metis_tac[cs_extends_new_block]) >>
  simp[comp_return_def, fresh_label_def, cs_extends_same_block,
       frag_code_def, emitted_blocks_def, emitted_insts_def, new_block_def]
QED

Theorem finish_inventory_emit[local]:
  cs_extends a (SND (emit_op opc ops a)) /\
  (EVERY (\i. P i.inst_opcode) (frag_code a (SND (emit_op opc ops a))) <=> P opc) /\
  cs_extends a (SND (emit_inst opc ops outs a)) /\
  (EVERY (\i. P i.inst_opcode) (frag_code a (SND (emit_inst opc ops outs a))) <=> P opc) /\
  cs_extends a (SND (emit_void opc ops a)) /\
  (EVERY (\i. P i.inst_opcode) (frag_code a (SND (emit_void opc ops a))) <=> P opc)
Proof
  simp[emit_op_def, emit_inst_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
       cs_extends_same_block, frag_code_def, emitted_blocks_def, emitted_insts_def,
       DROP_LENGTH_APPEND, mk_inst_def]
QED

(* Consume one symbolic compiler action at a time; no expansion of the
   earlier compile states into instructions in the continuation. *)
fun inventory_steps extra =
  let val clean = simp (finish_inventory_empty :: finish_inventory_emit :: extra)
  in clean >> rpt (match_mp_tac finish_inventory_bind >>
        (conj_tac >- clean) >> rpt gen_tac >> BETA_TAC >> clean)
  end;

Theorem finish_inventory_alloc_select[local]:
  (cs_extends a (SND (compile_alloc_buffer n a)) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (frag_code a (SND (compile_alloc_buffer n a)))) /\
  (cs_extends a (SND (compile_select c x y a)) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
     (frag_code a (SND (compile_select c x y a))))
Proof
  conj_tac >> inventory_steps [compile_alloc_buffer_def, compile_select_def]
QED

Theorem raw_call_finish_inventory[local]:
  cs_extends a (SND (compile_raw_call_finish addr dp dl gas value kind cap rev ov op a)) /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2])
    (frag_code a (SND (compile_raw_call_finish addr dp dl gas value kind cap rev ov op a)))
Proof
  Cases_on `kind` >> Cases_on `rev` >> Cases_on `0 < cap` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  inventory_steps [finish_inventory_alloc_select]
QED

Theorem raw_call_finish_effect_code:
  compile_raw_call_finish addr dp dl gas value kind cap rev ov op sm = (result,sb) ==>
  create_cut_code {} sm sb /\
  EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sm sb)
Proof
  strip_tac >>
  `SND (compile_raw_call_finish addr dp dl gas value kind cap rev ov op sm) = sb`
    by simp[] >>
  pop_assum (SUBST1_TAC o SYM) >> simp[raw_call_finish_inventory]
QED

(* Retain the exact point immediately after the one installed request. *)
Theorem raw_call_finish_effect_split:
  compile_raw_call_finish addr dp dl gas value kind cap rev ov op sm = (result,sb) ==>
  ?success sc.
    (case kind of
       RegularCall => emit_op CALL [gas;addr;value;dp;dl;op;Lit (n2w cap)]
     | StaticCall => emit_op STATICCALL [gas;addr;dp;dl;op;Lit (n2w cap)]
     | DelegateCall => emit_op DELEGATECALL [gas;addr;dp;dl;op;Lit (n2w cap)]) sm =
      (success,sc) /\
    create_cut_code {} sm sc /\ cs_extends sc sb /\
    EVERY (\i. ~MEM i.inst_opcode [INVOKE; CREATE; CREATE2]) (frag_code sc sb)
Proof
  strip_tac >> drule raw_call_finish_effect_code >> strip_tac >>
  drule raw_call_finish_prefix >> strip_tac >>
  qexistsl_tac [`success`, `sc`] >> asm_rewrite_tac [] >>
  `!opc ops a v b. emit_op opc ops a = (v,b) /\
      create_cut_targets opc ops = [] ==> create_cut_code {} a b` by
    (rpt strip_tac >>
     `create_cut_code {} a (SND (emit_op opc ops a))` by
       (irule create_cut_code_emit_op >> simp[]) >>
     qpat_x_assum `create_cut_code {} a (SND _)` mp_tac >>
     asm_simp_tac bool_ss [SND]) >>
  `create_cut_code {} sm sc` by
    (Cases_on `kind` >> fs[] >>
     qpat_assum `!opc ops a v b. _ ==> _` drule >> simp[create_cut_targets_def]) >>
  simp[] >>
  `cs_extends sm sc` by fs[create_cut_code_def] >>
  drule_all abi_decode_frag_code_compose >> fs[EVERY_MEM] >> metis_tac[]
QED

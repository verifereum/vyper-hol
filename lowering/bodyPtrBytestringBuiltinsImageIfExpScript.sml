(* Bounded control-flow experiment; stack callbacks are an explicit restriction,
   not an established property of the complete supported compiler. *)
Theory bodyPtrBytestringBuiltinsImageIfExp
Ancestors bodyPtrBytestringBuiltinsImageFrontier
          bodyPtrBytestringBuiltinsWindows compileEnv emitHelper
          venomInst list rich_list exprLowering vyperAST emitHelperProps

Theorem image_pending_barrier:
  !xs inst.
    inst.inst_opcode <> ADD /\ inst.inst_opcode <> ALLOCA ==>
    ~image_pending2 (xs ++ [inst]) /\ ~image_pending3 (xs ++ [inst])
Proof
  rpt gen_tac >> strip_tac >>
  simp[image_pending2_def, image_pending3_def] >>
  metis_tac[mk_inst_opcode]
QED

Theorem image_bad_barrier:
  !xs inst.
    inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> ADD /\
    inst.inst_opcode <> MSTORE ==>
    (image_bad (xs ++ [inst]) <=> image_bad xs)
Proof
  rpt strip_tac >>
  `!a b c d p q. [inst] <> p ++ [a;b;c;d] ++ q` by
    (rpt strip_tac >>
     qpat_x_assum `[inst] = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `!i ops outs. inst <> mk_inst i MSTORE ops outs`
    by metis_tac[mk_inst_opcode] >>
  simp[image_bad_def, four_window_append]
QED

Theorem image_entry_emit_delimiter:
  !opc args outs st t.
    opc <> ALLOCA /\ opc <> ADD /\ opc <> MSTORE /\
    image_entry st /\ emit_inst opc args outs st = ((),t) ==>
    image_entry t
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  gvs[image_entry_def, image_bad_barrier, image_pending_barrier]
QED

Theorem image_entry_fresh_label:
  !suffix st label t.
    fresh_label suffix st = (label,t) ==> (image_entry t <=> image_entry st)
Proof
  simp[fresh_label_def] >> rpt strip_tac >> gvs[image_entry_def]
QED

Theorem image_word_ifexp_body:
  !cfn bfn tfn cenv ty rty cond yes no st out t.
    is_word_type rty /\ image_entry st /\
    (!s vv u. image_entry s /\
       cfn cenv (BaseT BoolT) cond s = (vv,u) ==>
       image_entry u /\ ?vty op. vv = StackValue vty op) /\
    (!s vv u. image_entry s /\ cfn cenv ty yes s = (vv,u) ==>
       image_entry u /\ ?vty op. vv = StackValue vty op) /\
    (!s vv u. image_entry s /\ cfn cenv ty no s = (vv,u) ==>
       image_entry u /\ ?vty op. vv = StackValue vty op) /\
    compile_expr_body cfn bfn tfn cenv ty (IfExp rty cond yes no) st = (out,t)
    ==> image_entry t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[Once compile_expr_body_def, expr_type_def, lower_value_def,
      comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!s vv u. _ /\ cfn _ _ cond _ = _ ==> _` drule_all >>
  strip_tac >> gvs[unwrap_value_def, comp_return_def] >>
  `image_entry st5` by
    (imp_res_tac image_entry_fresh_var >>
     imp_res_tac image_entry_fresh_label >> gvs[]) >>
  `image_entry st6` by
    (qpat_assum `emit_inst _ _ _ _ = ((),st6)`
       (mp_then Any mp_tac image_entry_emit_delimiter) >> simp[]) >>
  `image_entry st7` by metis_tac[image_entry_new_block] >>
  qpat_x_assum `!s vv u. _ /\ cfn _ _ yes _ = _ ==> _` drule_all >>
  strip_tac >> gvs[compile_ifexp_arm_def, unwrap_value_def, comp_return_def] >>
  `image_entry st9` by
    (qpat_assum `emit_inst _ _ _ _ = ((),st9)`
       (mp_then Any mp_tac image_entry_emit_delimiter) >> simp[]) >>
  `image_entry st10` by
    (qpat_assum `emit_inst _ _ _ _ = ((),st10)`
       (mp_then Any mp_tac image_entry_emit_delimiter) >> simp[]) >>
  `image_entry st11` by metis_tac[image_entry_new_block] >>
  qpat_x_assum `!s vv u. _ /\ cfn _ _ no _ = _ ==> _` drule_all >>
  strip_tac >> gvs[compile_ifexp_arm_def, unwrap_value_def, comp_return_def] >>
  `image_entry st13` by
    (qpat_assum `emit_inst _ _ _ _ = ((),st13)`
       (mp_then Any mp_tac image_entry_emit_delimiter) >> simp[]) >>
  `image_entry st14` by
    (qpat_assum `emit_inst _ _ _ _ = ((),st14)`
       (mp_then Any mp_tac image_entry_emit_delimiter) >> simp[]) >>
  metis_tac[image_entry_new_block]
QED

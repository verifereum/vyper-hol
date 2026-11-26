Theory bodyIntCallStagePacketMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs loweringPosts
  loweringStateRelDefs exprLoweringProps compileEnv valueEncoding
  valueEncodingDefs allocaHistory ptrDiscipline venomInst venomState
  vyperContext vyperState vyperTypeSystem vyperTyping vyperStorageFootprint
  finite_map list words

(* The explicit and default passes share this accumulated operand packet.
   The parallel lists record the actual operands and words, source values,
   formal types and stack-passing flags, in that order. *)
Definition intcall_stage_ops_mods_def[nocompute]:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) <=>
    LENGTH ws = LENGTH ops /\ LENGTH vals = LENGTH ops /\
    LENGTH ptys = LENGTH ops /\ LENGTH pflags = LENGTH ops /\
    eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops /\
    (!x. MEM (Var x) ops ==> not_fresh_at si x) /\
    (!j. j < LENGTH ops /\ ~EL j pflags ==>
      ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
        FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
        sa.cs_next_id <= aid /\ aid < si.cs_next_id /\ 32 <= cap /\
        ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          inst.inst_id = aid) /\
    (!i j b k c l. i < j /\ j < LENGTH ops /\
      ~EL i pflags /\ ~EL j pflags /\
      op_prov G (EL i ops) = SOME (b,k) /\
      op_prov G (EL j ops) = SOME (c,l) ==>
      regions_disjoint b k c l) /\
    (!j rt. j < LENGTH ops /\ evaluate_type (get_tenv cx) (EL j ptys) = SOME rt ==>
      value_has_type rt (EL j vals) /\ val_wf rt (EL j vals) /\
      val_footprint rt (EL j vals) <= type_memory_size rt /\
      (EL j pflags ==> EL j ws = typed_val_to_w256 rt (EL j vals) /\
        op_prov G (EL j ops) = NONE) /\
      (~EL j pflags ==>
        ?b cap aid. op_prov G (EL j ops) = SOME (b,cap) /\
          FLOOKUP s.vs_allocas aid = SOME (b,cap) /\
          sa.cs_next_id <= aid /\ aid < si.cs_next_id /\
          lo <= b /\ b+cap <= s.vs_alloca_next /\ b <= w2n (EL j ws) /\
          w2n (EL j ws) + type_memory_size rt <= b+cap /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt (EL j vals) (w2n (EL j ws)) mem) /\
          (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
            b+cap <= lb \/ lb+sz <= b) /\
          (case pin of NONE => T | SOME (rb,pb,pk) =>
            b+cap <= pb \/ pb+pk <= b)))
End

(* The origin is fixed across both passes; the current cut changes. A pin
   represents this call's reserved result space, not the caller's return buffer. *)
Definition intcall_stage_frame_mods_def[nocompute]:
  intcall_stage_frame_mods (DF,lo,d,ctx,func) cenv cx st0
    (sa,es0,s0,G0,tn0) (si,esi,s,G,tn) pin <=>
    (case pin of NONE => T | SOME (rb,b,k) =>
      FLOOKUP G rb = SOME (b,k) /\ op_taint tn (Var rb) = {} /\
      lookup_var rb s = SOME (n2w b) /\
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,k) /\
      sa.cs_next_id < si.cs_next_id /\ lo <= b /\ b+k <= s.vs_alloca_next /\
      not_fresh_at si rb /\
      (!n lb sz. local_region cenv esi.scopes s n lb sz ==>
        b+k <= lb \/ lb+sz <= b)) /\
    wb_frame cenv es0 esi sa s0 s /\
    ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn /\
    alloca_history func s /\ sa.cs_next_id <= si.cs_next_id /\
    sa.cs_next_var <= si.cs_next_var /\
    (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
      local_region cenv esi.scopes s n b sz) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    MAP FDOM es0.scopes = MAP FDOM esi.scopes /\
    return_buf_frame d cenv si s /\ ~s.vs_halted /\
    s.vs_current_bb = si.cs_current_bb /\
    s.vs_inst_idx = LENGTH si.cs_current_insts /\
    (!H. valid_horizon cx st0 H esi.storage_trace ==>
      stmt_state_rel H ctx func cenv cx esi s /\
      immutable_frame_mods func cenv cx esi s /\
      storage_well_formed_on cx esi (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx esi G tn s)
End

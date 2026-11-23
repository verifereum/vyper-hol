(* Relate an oversized CREATE reached within one expression invocation
   to the source initcode-size check. *)
Theory createExprSizeExitDefs
Ancestors
  abiEncoderProps allocaHistory bodyFullPreds bodyPtrDefs e2eDefs fragExec fragGasOrigin
  fragGasOriginPtr gasExplicitSites gasSummary venomExecSemantics venomInst s1PrefixDefs
  ptrDiscipline venomState vyperCreate vyperInterpreter vyperState exprLowering
  exprSimFullBundleProps relation list words vyperAST vfmConstants context loweringPosts
  exprSimMemDefs vyperStorageFootprint valueEncodingDefs

(* Restrict caller edges to this invocation's emitted fragment. An INVOKE
 * which returns is one caller edge, with its children's GAS marks. *)
Definition create_expr_prefix_def:
  create_expr_prefix sa sb explicit ctx func s0 marks s <=>
    RTC
      (\(u, left) (v, all).
         ?bb inst right.
           (u.vs_current_bb <> sb.cs_current_bb \/
            u.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
           lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb u.vs_inst_idx = SOME inst /\
           inst.inst_id IN frag_ids sa sb /\
           gas_origin_edge F explicit ctx func u right (OK v) /\
           all = left ++ right)
      (s0, []) (s, marks)
End

(* A completed operand replays the GAS observations of this invocation.
   Its successful arm carries the same value and ghost posts as full
   expression simulation. An exempt source error can happen before the cut. *)
Definition gas_completed_operand_def:
  gas_completed_operand (DF, lo, explicit, ctx, func, PG)
      tops cx st0 sa sb source (es, s0, G0, tn0) Q <=>
    !H0 marks s tail res ee.
      create_expr_prefix sa sb explicit ctx func s0 marks s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (res, ee) /\
      valid_horizon cx st0 H0 ee.storage_trace ==>
      (?G tn.
         ee.gas_obs = tail /\
         !H. valid_horizon cx st0 H ee.storage_trace ==>
           gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
             (s0,G0,tn0) marks (OK s,G,tn) /\
           Q H res (ee with gas_obs := []) G tn s) \/
      (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err)
End

Definition create_operand_completed_ok_def:
  create_operand_completed_ok cx e <=>
    !DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      expr_body_pre cenv cx env e es ==>
      (!st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
        expr_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) ==>
        gas_completed_operand
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          tops cx st0 sa sb (bind (eval_expr cx e) (read_result cx))
          (es, s0, G0, tn0)
          (expr_sim_full_post (DF, lo, d, ctx, func) cenv cx e
            (es, sa, sb, s0, op, G0, tn0))) /\
      (!st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
        expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
          cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
        gas_completed_operand
          (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
          tops cx st0 sa sb (eval_expr cx e) (es, s0, G0, tn0)
          (\H res ee G tn t. ?tv. res = INL tv /\
            vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
            vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
              ee tv vv t /\
            alloca_history func t /\
            (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
            s0.vs_alloca_next <= t.vs_alloca_next /\
            ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
            ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
            (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
            (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
            (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                     ptr_buf_ok cenv e op G t) /\
            (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
            ghost_kept_at lo cenv es sa G0 tn0 s0 G tn))
End

Definition create_expr_size_exit_def:
  create_expr_size_exit cx e <=>
    !DF lo d (PG : (num # num) option list) tops
      ctx shadow_ctx func shadow_func cenv env ty es
      st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      expr_body_pre cenv cx env e es /\
      expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      !H marks s bb inst value off sz salt w tail res ee.
        create_expr_prefix sa sb (gas_explicit_sites ctx shadow_ctx)
          ctx func s0 marks s /\
        (s.vs_current_bb <> sb.cs_current_bb \/
         s.vs_inst_idx <> LENGTH sb.cs_current_insts) /\
        lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst /\
        inst.inst_id IN frag_ids sa sb /\
        (!j. MEM j (fn_insts func) /\ j.inst_id IN frag_ids sa sb /\
             MEM j.inst_opcode [CREATE; CREATE2] ==> j.inst_id <= inst.inst_id) /\
        ((inst.inst_opcode = CREATE /\ inst.inst_operands = [value; off; sz]) \/
         (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [value; off; sz; salt])) /\
        eval_operand sz s = SOME w /\ 2 * max_code_size < w2n w /\
        eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (res, ee) /\
        valid_horizon cx st0 H ee.storage_trace ==>
        res = INR (Error (RuntimeError "create initcode too large")) \/
        (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err)
End

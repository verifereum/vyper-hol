(*
 * Algebraic Optimization (Venom IR) - Transform
 *
 * Updater-style mutation matching Vyper's runtime pass architecture:
 *   offset -> algebraic peephole -> iszero-chain -> algebraic peephole
 *)

Theory algebraicOptTransform
Ancestors
  algebraicOptAnalysis analysisCache instUpdater

(* ==========================================================================
   Flipping and Use Hints
   ========================================================================== *)

Definition inst_flippable_def:
  inst_flippable inst <=>
    is_commutative inst.inst_opcode \/ is_comparator inst.inst_opcode
End

Definition flip_flippable_inst_def:
  flip_flippable_inst inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_commutative inst.inst_opcode then
          inst with inst_operands := [op2; op1]
        else if is_comparator inst.inst_opcode then
          inst with <| inst_opcode := flip_comparator inst.inst_opcode;
                        inst_operands := [op2; op1] |>
        else inst
    | _ => inst
End

Definition flip_for_peephole_updater_def:
  flip_for_peephole_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if inst_flippable inst /\ is_lit op2 /\ ~is_lit op1 then
          let inst' = flip_flippable_inst inst in
          (inst_updater_update updater inst inst'.inst_opcode inst'.inst_operands, inst')
        else
          (updater, inst)
    | _ => (updater, inst)
End

Definition flip_after_peephole_updater_def:
  flip_after_peephole_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if inst_flippable inst /\ is_lit op1 /\ ~is_lit op2 then
          let inst' = flip_flippable_inst inst in
            inst_updater_update updater inst inst'.inst_opcode inst'.inst_operands
        else updater
    | _ => updater
End

Definition uses_hint_for_inst_def:
  uses_hint_for_inst updater inst =
    case inst_output inst of
      NONE => default_hint
    | SOME v =>
        let uses = dfg_get_uses updater.iu_dfg v in
          <| prefer_iszero := all_uses_prefer_iszero_ops uses;
             is_truthy := all_uses_truthy_ops uses;
             cmp_flip := cmp_flip_hint_for_uses_dfg updater.iu_dfg inst uses |>
End

(* ==========================================================================
   Local Rewrite Helpers
   ========================================================================== *)

Definition apply_single_rewrite_updater_def:
  apply_single_rewrite_updater updater inst out =
    case out of
      [inst'] =>
        inst_updater_update updater inst inst'.inst_opcode inst'.inst_operands
    | _ => updater
End

(* Signextend rewrite using DFG lookup to avoid repeated full-function scans. *)
Definition rewrite_signextend_dfg_def:
  rewrite_signextend_dfg ranges dfg inst =
    case inst.inst_operands of
      [x_op; n_op] =>
        (case n_op of
           Lit w =>
             let n = w2n w in
             if n >= 31 then [mk_assign inst x_op]
             else
               let r = range_lookup ranges inst.inst_id x_op in
               let within =
                 (~r.vr_is_top /\ ~r.vr_is_empty /\
                  r.vr_lo >= signed_min_for_bytes n /\
                  r.vr_hi <= signed_max_for_bytes n)
               in
                 if within then [mk_assign inst x_op]
                 else
                   (case x_op of
                      Var v =>
                        (case dfg_get_def dfg v of
                           SOME inst2 =>
                             if inst2.inst_opcode = SIGNEXTEND then
                               (case inst2.inst_operands of
                                  [x2; inner_n] =>
                                    (case inner_n of
                                       Lit w2 => if n >= w2n w2 then [mk_assign inst x_op] else [inst]
                                     | _ => [inst])
                                | _ => [inst])
                             else [inst]
                         | NONE => [inst])
                    | _ => [inst])
         | _ => [inst])
    | _ => [inst]
End

Definition algebraic_opt_handle_shift_updater_def:
  algebraic_opt_handle_shift_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op2 then inst_updater_mk_assign updater inst op1
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_exp_updater_def:
  algebraic_opt_handle_exp_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 then inst_updater_mk_assign updater inst (Lit (1w:bytes32))
        else if lit_is_one op2 then inst_updater_mk_assign updater inst (Lit (1w:bytes32))
        else if lit_is_zero op2 then inst_updater_update updater inst ISZERO [op1]
        else if lit_is_one op1 then inst_updater_mk_assign updater inst op2
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_add_sub_xor_updater_def:
  algebraic_opt_handle_add_sub_xor_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if (inst.inst_opcode = XOR \/ inst.inst_opcode = SUB) /\ op1 = op2 then
          inst_updater_mk_assign updater inst (Lit (0w:bytes32))
        else if lit_is_zero op1 then
          inst_updater_mk_assign updater inst op2
        else if inst.inst_opcode = SUB /\ lit_is_ones op2 then
          inst_updater_update updater inst NOT [op1]
        else if inst.inst_opcode = XOR /\ lit_is_ones op1 then
          inst_updater_update updater inst NOT [op2]
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_and_updater_def:
  algebraic_opt_handle_and_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          inst_updater_mk_assign updater inst (Lit (0w:bytes32))
        else if lit_is_ones op1 then
          inst_updater_mk_assign updater inst op2
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_mul_div_mod_updater_def:
  algebraic_opt_handle_mul_div_mod_updater updater inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          inst_updater_mk_assign updater inst (Lit (0w:bytes32))
        else if (inst.inst_opcode = Mod \/ inst.inst_opcode = SMOD) /\ lit_is_one op1 then
          inst_updater_mk_assign updater inst (Lit (0w:bytes32))
        else if (inst.inst_opcode = MUL \/ inst.inst_opcode = Div \/ inst.inst_opcode = SDIV) /\
                lit_is_one op1 then
          inst_updater_mk_assign updater inst op2
        else if is_pow2_lit op1 then
          let n = log2_lit op1 in
            if inst.inst_opcode = Mod then
              let k = w2n (case op1 of Lit w => w | _ => 0w) in
                inst_updater_update updater inst AND [lit_of_num (k - 1); op2]
            else if inst.inst_opcode = Div then
              inst_updater_update updater inst SHR [op2; lit_of_num n]
            else if inst.inst_opcode = MUL then
              inst_updater_update updater inst SHL [op2; lit_of_num n]
            else updater
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_or_updater_def:
  algebraic_opt_handle_or_updater updater inst is_truthy =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_ones op1 then
          inst_updater_mk_assign updater inst (Lit max_uint256)
        else if is_truthy /\ is_lit op1 /\ ~lit_is_zero op1 then
          inst_updater_mk_assign updater inst (Lit (1w:bytes32))
        else if lit_is_zero op1 then
          inst_updater_mk_assign updater inst op2
        else updater
    | _ => updater
End

Definition algebraic_opt_handle_eq_updater_def:
  algebraic_opt_handle_eq_updater updater inst prefer_iszero =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then
          inst_updater_mk_assign updater inst (Lit (1w:bytes32))
        else if lit_is_zero op1 then
          inst_updater_update updater inst ISZERO [op2]
        else if lit_is_ones op1 then
          let (upd1, vopt) = inst_updater_add_before updater inst NOT [op2] in
            (case vopt of
               NONE => upd1
             | SOME v => inst_updater_update upd1 inst ISZERO [Var v])
        else if prefer_iszero then
          let (upd1, vopt) = inst_updater_add_before updater inst XOR [op1; op2] in
            (case vopt of
               NONE => upd1
             | SOME v => inst_updater_update upd1 inst ISZERO [Var v])
        else updater
    | _ => updater
End

Definition cmp_range_opt_def:
  cmp_range_opt ranges inst signed is_gt op1 op2 =
    let a_op = op2 in
    let b_op = op1 in
    if is_lit a_op /\ ~is_lit b_op then
      let r = range_lookup ranges inst.inst_id b_op in
      if ~r.vr_is_top /\ ~r.vr_is_empty then
        let lit =
          if signed then
            if r.vr_hi <= max_int256_i then lit_int_signed a_op else NONE
          else
            if r.vr_lo >= (0:int) then lit_int_unsigned a_op else NONE
        in
          (case lit of
             NONE => NONE
           | SOME l =>
               if is_gt then
                 if l > r.vr_hi then SOME (1w:bytes32)
                 else if l <= r.vr_lo then SOME (0w:bytes32)
                 else NONE
               else
                 if l < r.vr_lo then SOME (1w:bytes32)
                 else if l >= r.vr_hi then SOME (0w:bytes32)
                 else NONE)
      else NONE
    else if is_lit b_op /\ ~is_lit a_op then
      let r = range_lookup ranges inst.inst_id a_op in
      if ~r.vr_is_top /\ ~r.vr_is_empty then
        let lit =
          if signed then
            if r.vr_hi <= max_int256_i then lit_int_signed b_op else NONE
          else
            if r.vr_lo >= (0:int) then lit_int_unsigned b_op else NONE
        in
          (case lit of
             NONE => NONE
           | SOME l =>
               if is_gt then
                 if r.vr_lo > l then SOME (1w:bytes32)
                 else if r.vr_hi <= l then SOME (0w:bytes32)
                 else NONE
               else
                 if r.vr_hi < l then SOME (1w:bytes32)
                 else if r.vr_lo >= l then SOME (0w:bytes32)
                 else NONE)
      else NONE
    else NONE
End

Definition algebraic_opt_handle_cmp_after_updater_def:
  algebraic_opt_handle_cmp_after_updater updater inst out_var =
    let uses = dfg_get_uses updater.iu_dfg out_var in
      case uses of
        [after0] =>
          (case lookup_inst_in_function after0.inst_id updater.iu_fn of
             NONE => updater
           | SOME after =>
               if after.inst_opcode = ASSERT then
                 let (upd1, vopt) = inst_updater_add_before updater after ISZERO [Var out_var] in
                   (case vopt of
                      NONE => upd1
                    | SOME v => inst_updater_update upd1 after ASSERT [Var v])
               else if after.inst_opcode = ISZERO then
                 inst_updater_mk_assign updater after (Var out_var)
               else updater)
      | _ => updater
End

Definition algebraic_opt_cmp_limits_def:
  algebraic_opt_cmp_limits signed is_gt =
    let lo = if signed then min_int256 else min_uint256 in
    let hi = if signed then max_int256 else max_uint256 in
      (if is_gt then lo else hi,
       if is_gt then hi else lo,
       if is_gt then word_sub hi (1w:bytes32)
       else word_add lo (1w:bytes32))
End

Definition algebraic_opt_cmp_rule_never_def:
  algebraic_opt_cmp_rule_never updater inst op1 never =
    if lit_eq op1 never then
      SOME (inst_updater_mk_assign updater inst (Lit (0w:bytes32)))
    else NONE
End

Definition algebraic_opt_cmp_rule_almost_never_def:
  algebraic_opt_cmp_rule_almost_never updater inst op1 op2 almost_never never =
    if lit_eq op1 almost_never then
      SOME (inst_updater_update updater inst EQ [op2; Lit never])
    else NONE
End

Definition algebraic_opt_cmp_rule_prefer_iszero_def:
  algebraic_opt_cmp_rule_prefer_iszero updater inst prefer_iszero op1 op2 almost_always =
    if prefer_iszero /\ lit_eq op1 almost_always then
      let (upd1, vopt) = inst_updater_add_before updater inst EQ [op1; op2] in
        SOME
          (case vopt of
             NONE => upd1
           | SOME v => inst_updater_update upd1 inst ISZERO [Var v])
    else NONE
End

Definition algebraic_opt_cmp_rule_gt_zero_def:
  algebraic_opt_cmp_rule_gt_zero updater inst op1 op2 =
    if inst.inst_opcode = GT /\ lit_is_zero op1 then
      let (upd1, vopt) = inst_updater_add_before updater inst ISZERO [op2] in
        SOME
          (case vopt of
             NONE => upd1
           | SOME v => inst_updater_update upd1 inst ISZERO [Var v])
    else NONE
End

Definition algebraic_opt_cmp_rule_flip_def:
  algebraic_opt_cmp_rule_flip updater inst cmp_flip is_gt op1 op2 =
    if cmp_flip /\ is_lit op1 then
      let new_op = flip_comparator inst.inst_opcode in
      let adj =
        if is_gt then
          word_add (case op1 of Lit w => w | _ => 0w) (1w:bytes32)
        else
          word_sub (case op1 of Lit w => w | _ => 0w) (1w:bytes32) in
      let upd1 = inst_updater_update updater inst new_op [Lit adj; op2] in
        SOME
          (case inst_output inst of
             NONE => upd1
           | SOME out_var =>
               algebraic_opt_handle_cmp_after_updater upd1 inst out_var)
    else NONE
End

Definition algebraic_opt_cmp_nonrange_rules_def:
  algebraic_opt_cmp_nonrange_rules updater inst signed prefer_iszero cmp_flip is_gt op1 op2 =
    let (almost_always, never, almost_never) =
      algebraic_opt_cmp_limits signed is_gt in
      case algebraic_opt_cmp_rule_never updater inst op1 never of
        SOME upd => upd
      | NONE =>
          (case algebraic_opt_cmp_rule_almost_never updater inst op1 op2 almost_never never of
             SOME upd => upd
           | NONE =>
               (case algebraic_opt_cmp_rule_prefer_iszero updater inst prefer_iszero op1 op2 almost_always of
                  SOME upd => upd
                | NONE =>
                    (case algebraic_opt_cmp_rule_gt_zero updater inst op1 op2 of
                       SOME upd => upd
                     | NONE =>
                         (case algebraic_opt_cmp_rule_flip updater inst cmp_flip is_gt op1 op2 of
                            SOME upd => upd
                          | NONE => updater))))
End

Definition algebraic_opt_handle_cmp_updater_def:
  algebraic_opt_handle_cmp_updater ranges updater inst prefer_iszero cmp_flip =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then
          inst_updater_mk_assign updater inst (Lit (0w:bytes32))
        else
          let signed = is_signed_cmp inst.inst_opcode in
          let is_gt = is_gt_op inst.inst_opcode in
          let range_opt = cmp_range_opt ranges inst signed is_gt op1 op2 in
            case range_opt of
              SOME w => inst_updater_mk_assign updater inst (Lit w)
            | NONE =>
                algebraic_opt_cmp_nonrange_rules updater inst signed prefer_iszero cmp_flip is_gt op1 op2
    | _ => updater
End

(* ==========================================================================
   Main Peephole Dispatcher
   ========================================================================== *)

Definition algebraic_opt_handle_inst_updater_def:
  algebraic_opt_handle_inst_updater ranges updater inst =
    if inst_num_outputs inst <> 1 \/ inst_is_volatile inst \/
       inst.inst_opcode = ASSIGN \/ inst_is_pseudo inst then
      updater
    else
      let (updater1, inst1) = flip_for_peephole_updater updater inst in
      let h = uses_hint_for_inst updater1 inst1 in
        case inst1.inst_opcode of
          ADD => algebraic_opt_handle_add_sub_xor_updater updater1 inst1
        | SUB => algebraic_opt_handle_add_sub_xor_updater updater1 inst1
        | XOR => algebraic_opt_handle_add_sub_xor_updater updater1 inst1
        | AND => algebraic_opt_handle_and_updater updater1 inst1
        | OR => algebraic_opt_handle_or_updater updater1 inst1 h.is_truthy
        | MUL => algebraic_opt_handle_mul_div_mod_updater updater1 inst1
        | Div => algebraic_opt_handle_mul_div_mod_updater updater1 inst1
        | SDIV => algebraic_opt_handle_mul_div_mod_updater updater1 inst1
        | Mod => algebraic_opt_handle_mul_div_mod_updater updater1 inst1
        | SMOD => algebraic_opt_handle_mul_div_mod_updater updater1 inst1
        | venomInst$EXP => algebraic_opt_handle_exp_updater updater1 inst1
        | SHL => algebraic_opt_handle_shift_updater updater1 inst1
        | SHR => algebraic_opt_handle_shift_updater updater1 inst1
        | SAR => algebraic_opt_handle_shift_updater updater1 inst1
        | SIGNEXTEND =>
            apply_single_rewrite_updater updater1 inst1
              (rewrite_signextend_dfg ranges updater1.iu_dfg inst1)
        | EQ => algebraic_opt_handle_eq_updater updater1 inst1 h.prefer_iszero
        | GT => algebraic_opt_handle_cmp_updater ranges updater1 inst1 h.prefer_iszero h.cmp_flip
        | LT => algebraic_opt_handle_cmp_updater ranges updater1 inst1 h.prefer_iszero h.cmp_flip
        | SGT => algebraic_opt_handle_cmp_updater ranges updater1 inst1 h.prefer_iszero h.cmp_flip
        | SLT => algebraic_opt_handle_cmp_updater ranges updater1 inst1 h.prefer_iszero h.cmp_flip
        | _ => updater1
End

(* ==========================================================================
   Block / Function Traversal Helpers
   ========================================================================== *)

Definition inst_ids_of_block_def:
  inst_ids_of_block bb = MAP (\inst. inst.inst_id) bb.bb_instructions
End

Definition fold_block_inst_ids_def:
  fold_block_inst_ids f updater bb =
    FOLDL
      (\acc iid.
         case lookup_inst_in_function iid acc.iu_fn of
           NONE => acc
         | SOME inst => f acc iid inst)
      updater (inst_ids_of_block bb)
End

Definition fold_updater_blocks_def:
  fold_updater_blocks f updater =
    FOLDL (\acc bb. f acc bb) updater updater.iu_fn.fn_blocks
End

Definition algebraic_opt_pass_block_updater_def:
  algebraic_opt_pass_block_updater ranges updater bb =
    fold_block_inst_ids
      (\acc iid inst.
         let acc1 = algebraic_opt_handle_inst_updater ranges acc inst in
           (case lookup_inst_in_function iid acc1.iu_fn of
              NONE => acc1
            | SOME inst' => flip_after_peephole_updater acc1 inst'))
      updater bb
End

Definition algebraic_opt_pass_updater_def:
  algebraic_opt_pass_updater ranges updater =
    fold_updater_blocks (algebraic_opt_pass_block_updater ranges) updater
End

Definition algebraic_opt_get_iszero_chain_updater_def:
  algebraic_opt_get_iszero_chain_updater fuel updater op =
    iszero_chain_aux_dfg updater.iu_dfg fuel op []
End

Definition iszero_keep_index_def:
  iszero_keep_index count op =
    if op = JNZ \/ op = ASSERT \/ op = ASSERT_UNREACHABLE then
      1 - (count MOD 2)
    else
      1 + (count MOD 2)
End

Definition algebraic_opt_rewrite_iszero_use_def:
  algebraic_opt_rewrite_iszero_use out_var chain count acc use0 =
    case lookup_inst_in_function use0.inst_id acc.iu_fn of
      NONE => acc
    | SOME use_inst =>
        case use_inst.inst_opcode of
          ISZERO => acc
        | _ =>
            let keep = iszero_keep_index count use_inst.inst_opcode in
              if keep >= count then acc
              else
                let dep_inst = EL keep chain in
                  case dep_inst.inst_operands of
                    [new_op] =>
                      inst_updater_update_operands acc use_inst [(Var out_var, new_op)]
                  | _ => acc
End

Definition algebraic_opt_optimize_iszero_chain_def:
  algebraic_opt_optimize_iszero_chain updater out_var chain =
    let count = LENGTH chain in
      if count = 0 then updater
      else
        let uses = dfg_get_uses updater.iu_dfg out_var in
          FOLDL
            (\acc use0. algebraic_opt_rewrite_iszero_use out_var chain count acc use0)
            updater uses
End

Definition algebraic_opt_optimize_iszero_inst_def:
  algebraic_opt_optimize_iszero_inst fuel updater inst =
    case inst.inst_opcode of
      ISZERO =>
        (case inst.inst_operands of
           [op] =>
             (case inst_output inst of
                NONE => updater
              | SOME out_var =>
                  let chain = algebraic_opt_get_iszero_chain_updater fuel updater op in
                    algebraic_opt_optimize_iszero_chain updater out_var chain)
         | _ => updater)
    | _ => updater
End

Definition algebraic_opt_optimize_iszero_block_updater_def:
  algebraic_opt_optimize_iszero_block_updater fuel updater bb =
    fold_block_inst_ids
      (\acc iid inst. algebraic_opt_optimize_iszero_inst fuel acc inst)
      updater bb
End

Definition algebraic_opt_optimize_iszero_updater_def:
  algebraic_opt_optimize_iszero_updater updater =
    let fuel = LENGTH (fn_insts updater.iu_fn) in
      fold_updater_blocks (algebraic_opt_optimize_iszero_block_updater fuel) updater
End

Definition algebraic_opt_handle_offset_inst_updater_def:
  algebraic_opt_handle_offset_inst_updater updater inst =
    case inst.inst_opcode of
      ADD =>
        (case inst.inst_operands of
           [op1; op2] =>
             if is_lit op1 /\ is_label op2 then
               inst_updater_update updater inst OFFSET [op1; op2]
             else updater
         | _ => updater)
    | _ => updater
End

Definition algebraic_opt_handle_offset_block_updater_def:
  algebraic_opt_handle_offset_block_updater updater bb =
    fold_block_inst_ids
      (\acc iid inst. algebraic_opt_handle_offset_inst_updater acc inst)
      updater bb
End

Definition algebraic_opt_handle_offset_updater_def:
  algebraic_opt_handle_offset_updater updater =
    fold_updater_blocks algebraic_opt_handle_offset_block_updater updater
End

(* ==========================================================================
   Pass Definition
   ========================================================================== *)

Definition algebraic_opt_pass_with_ranges_def:
  algebraic_opt_pass_with_ranges ranges fn =
    let updater0 = inst_updater_init fn in
    let updater1 = algebraic_opt_handle_offset_updater updater0 in
    let updater2 = algebraic_opt_pass_updater ranges updater1 in
    let updater3 = algebraic_opt_optimize_iszero_updater updater2 in
    let updater4 = algebraic_opt_pass_updater ranges updater3 in
      updater4.iu_fn
End

Definition algebraic_opt_pass_def:
  algebraic_opt_pass fn =
    let cache0 = analysis_cache_init fn in
    let ranges = FST (analysis_cache_request_ranges cache0) in
      algebraic_opt_pass_with_ranges ranges fn
End

Definition algebraic_opt_context_def:
  algebraic_opt_context ctx =
    ctx with ctx_functions := MAP algebraic_opt_pass ctx.ctx_functions
End

Definition algebraic_opt_transform_def:
  algebraic_opt_transform fn fn' <=> fn' = algebraic_opt_pass fn
End

val _ = export_theory();

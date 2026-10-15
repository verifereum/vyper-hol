(* Compatibility simplification for clients that unfold valid_state_rel.
   Only MASK equalities are expanded, never arbitrary state equalities.
   The generated component theorem supplies the complete current record:
   this conversion cannot silently omit components added in later theories.
   Definitions are fetched lazily because this module is loaded by their theory. *)
structure execEquivParamMaskLib =
struct
open HolKernel boolLib bossLib venomStateTheory

fun mask_name tm =
  case strip_comb tm of
    (c, [_]) =>
      (case total dest_thy_const c of
         SOME {Thy = "execEquivParamDefs", Name, ...} =>
           if Name = "vsr_frame" orelse Name = "vsr_term_frame"
           then SOME Name else NONE
       | _ => NONE)
  | _ => NONE

fun mask_eq_conv tm =
  let
    val (l,r) = dest_eq tm
    val name = case (mask_name l, mask_name r) of
      (SOME n, SOME m) => if n = m then n else raise UNCHANGED
    | _ => raise UNCHANGED
    val def = DB.fetch "execEquivParamDefs" (name ^ "_def")
  in
    (REWRITE_CONV [def] THENC
     simpLib.SIMP_CONV (srw_ss()) [venom_state_component_equality]) tm
  end

val _ = BasicProvers.logged_addfrags {thyname = "execEquivParamDefs"}
  [simpLib.conv_ss {name = "vsr_complete_mask_equality", trace = 2,
    key = SOME ([], ``(s1:venom_state) = s2``),
    conv = K (K mask_eq_conv)}]
end

(* Lazy, datatype-derived normalization restricted to these five masks.
   Never expands arbitrary record equality or exports a retained-selector list.
   Lazy definition lookup also permits loading in the defining theory. *)
structure passResidualFrameLib =
struct
open HolKernel boolLib bossLib venomStateTheory

val masks = ["commute_frame", "alloca_remap_frame", "concretize_frame",
             "copy_fwd_frame", "icf_frame"]

fun mask_name tm =
  case strip_comb tm of
    (c, [_]) =>
      (case total dest_thy_const c of
         SOME {Thy = "passResidualFrame", Name, ...} =>
           if List.exists (fn n => n = Name) masks then SOME Name else NONE
       | _ => NONE)
  | _ => NONE

fun mask_eq_conv tm =
  let
    val (l,r) = dest_eq tm
    val name = case (mask_name l, mask_name r) of
      (SOME n, SOME m) => if n = m then n else raise UNCHANGED
    | _ => raise UNCHANGED
    val def = DB.fetch "passResidualFrame" (name ^ "_def")
  in
    (REWRITE_CONV [def] THENC
     simpLib.SIMP_CONV (srw_ss()) [venom_state_component_equality]) tm
  end

val _ = BasicProvers.logged_addfrags {thyname = "passResidualFrame"}
  [simpLib.conv_ss {name = "pass_residual_mask_equality", trace = 2,
    key = SOME ([], ``(s1:venom_state) = s2``),
    conv = K (K mask_eq_conv)}]
end

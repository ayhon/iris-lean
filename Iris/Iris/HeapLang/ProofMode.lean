module

public import Iris.ProofMode
public import Iris.HeapLang.Tactic
public import Iris.ProgramLogic.WeakestPre
public import Iris.ProgramLogic.Language
public import Lean
public import Qq

namespace Iris.ProofMode

open Lean hiding Expr
open Meta Elab Tactic Qq
open Iris.HeapLang

#check Wp.wp

#check wp_bind

-- TODO: Is this really needed?
meta def quoteList {α : Q(Type u)}: List Q($α) → Q(List $α)
  | [] => q([])
  | x :: xs => q($x :: $(quoteList xs))

elab "wp_bind" K:term : tactic => do
  -- TODO: Do we ask for a function or for a "pattern"?
  let K ← elabTermEnsuringTypeQ K q(HeapLang.Exp)
  let (Ks, _) ← HeapLang.extractAllEctxItems K
  ProofModeM.runTactic fun mvar {u, prop, bi, hyps, goal, ..} => do
    let .defEq _ ← isLevelDefEqQ u 0
      | throwError "`wp_bind` only works over `IProp` (at universe level 0)"
    let ~q(IProp $GF) := prop
      | throwError "`wp_bind` only works over `IProp`"
    let ~q(UPred.instBIUPred) := bi
      | throwError "`wp_bind` expected the BI implementation of `IProp` to be `UPred.instBIUPred`"

    -- TODO: It'd be nice to check `expTy =Q Expr` from this match directly, instead of introducing the assumption directly.
    let ~q(Wp.wp (A := Stuckness) (Expr := $expTy) (Val := $Val) (self := wp.def (Λ := $Λ) (ι := $ι)) $s $E $e $Φ) := goal
      | throwError "The goal was not a WP application"
    let (ctx, e) ← HeapLang.extractAllEctxItems e
    let (inner_Ks, outer_Ks) := ctx.splitAt Ks.length
    let e ← HeapLang.fill inner_Ks e
    unless ← isDefEq K e do throwError s!"Couldn't unify {←ppExpr K} with {←ppExpr e}"

    have : u_1 =QL 0 := ⟨⟩
    have : $expTy =Q Exp := ⟨⟩

    let outer_K := quoteList outer_Ks
    let out_fun : Q(Exp → Exp) := q($(outer_K).foldl (fun x y => ECtxItem.fill y x))

    let .some evctxInst ← trySynthInstanceQ q(ProgramLogic.Language.Context $out_fun)
      | throwError "Can only bind over an evaluation context, and {←ppExpr out_fun} is not"

    let pf := q(wp_bind (GF := $GF) _ (κ := $evctxInst) (s := $s) (E := $E) (e := $out_fun $e) (Φ := $Φ))

    let newGoal := q(Wp.wp $s $E ($out_fun $e) fun v => Wp.wp $s $E (List.foldl (fun x y => ECtxItem.fill y x) ((v : $Val) : Exp) $outer_K) $Φ)
    let newProof ← addBIGoal hyps newGoal
    mvar.assign q($(newProof).trans $pf)

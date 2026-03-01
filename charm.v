(* =================================================================== *)
(* 外部から見た鈴木悠起也の可愛いところを形式化 *)
(* =================================================================== *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

(* ---------------------------- *)
(* 可愛さの特徴を列挙 *)
(* ---------------------------- *)
Inductive CuteTrait :=
  | Curiosity        (* 好奇心旺盛 *)
  | Diligence        (* 細部へのこだわり *)
  | Playfulness      (* 遊び心 *)
  | Honesty          (* 素直・正直 *)
  | BalanceSense.    (* 理論と実務の両立 *)

(* ---------------------------- *)
(* 鈴木悠起也が持つ特徴のリスト *)
(* ---------------------------- *)
Definition YukiyaTraits : list CuteTrait :=
  [Curiosity; Diligence; Playfulness; Honesty; BalanceSense].

(* ---------------------------- *)
(* 特徴が全て揃っているか *)
(* ---------------------------- *)
Fixpoint all_traits_present (required : list CuteTrait) (present : list CuteTrait) : Prop :=
  match required with
  | [] => True
  | t :: ts => In t present /\ all_traits_present ts present
  end.

(* ---------------------------- *)
(* 定義: 全て揃うと「可愛い」 *)
(* ---------------------------- *)
Definition is_cute (traits : list CuteTrait) : Prop :=
  all_traits_present [Curiosity; Diligence; Playfulness; Honesty; BalanceSense] traits.

(* ---------------------------- *)
(* 定理: 鈴木悠起也は可愛い *)
(* ---------------------------- *)
Theorem Yukiya_is_cute :
  is_cute YukiyaTraits.
Proof.
  unfold is_cute, YukiyaTraits, all_traits_present.
  simpl; repeat split; auto.
Qed.
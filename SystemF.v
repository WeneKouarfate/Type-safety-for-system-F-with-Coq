Require Import String.
Require Import Arith.
Require Import Relations.
(* From Ltac2 Require Import Ltac2. ( * make some simple tactics composition not working *)
(* ================== TYPES AND TERMS ====================
  Plus their annotations
  ======================================================== *)

(* Type definition *)
(* type variables are nat and not string for parsing and coercion easyness *)
Inductive typ : Set :=
  | typ_bool : typ
  | typ_nat : typ
  | typ_var : nat -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : nat -> typ -> typ.

(* Term definition *)
Inductive trm : Set :=
  | trm_var : string -> trm
  | trm_absV : string -> typ -> trm -> trm
  | trm_absT : nat -> trm -> trm
  | trm_appV : trm -> trm -> trm
  | trm_appT : trm -> typ -> trm
  | trm_true : trm
  | trm_false : trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_zero : trm
  | trm_succ : trm -> trm
  | trm_pred : trm -> trm
  | trm_iszero : trm -> trm.


(* Boolean values definition *)
Inductive value_bool : trm -> Prop :=
  | val_true : value_bool trm_true
  | val_false : value_bool trm_false.
(* Natural values definition (for predecessor beta reduction?) *)
Inductive value_nat : trm -> Prop :=
  | val_zero : value_nat trm_zero
  | val_succ : forall {t' : trm}, (value_nat t') -> value_nat (trm_succ t').
(* Values definition adding types and terms redexes *)
Inductive val : trm -> Prop :=
  | val_bool : forall {t:trm}, (value_bool t) -> val t
  | val_nat : forall {t:trm}, (value_nat t) -> val t
  | val_absV : forall {x:string}{T:typ}{t:trm}, val (trm_absV x T t)
  | val_absT : forall {T:nat}{t:trm}, val (trm_absT T t).

(* will later try with Notation scope instead of custom entry, seems less complicated *)
Declare Custom Entry sys_f.
(* ??? *)
Notation "$< e >$" := e (e custom sys_f at level 99).
Notation "( x )" := x (in custom sys_f, x at level 99).
Notation "x" := x (in custom sys_f at level 0, x constr at level 0).

(* Types notations *)
Notation "M '→' N" := (typ_arrow M N) (in custom sys_f at level 50, right associativity).
Notation "'Bool'" := typ_bool (in custom sys_f at level 0).
Notation "'Nat'" := typ_nat (in custom sys_f at level 0).
Notation "'∀' x ',' t" := (typ_all x t) (in custom sys_f at level 90, x at level 99, t custom sys_f at level 99, left associativity).

(* Terms notations *)
Notation "'λ' x : T , t" := (trm_absV x T t) (in custom sys_f at level 49, x constr at level 99, T custom sys_f at level 99, t custom sys_f at level 99, left associativity).
Notation "'Λ' x , t" := (trm_absT x t) (in custom sys_f at level 90, x constr at level 99, t custom sys_f at level 99, left associativity).
Notation "t1 t2" := (trm_appV t1 t2) (in custom sys_f at level 1, left associativity).
Notation "t1 [ T ]" := (trm_appT t1 T) (in custom sys_f at level 1, left associativity).
Notation "'true'" := trm_true (in custom sys_f at level 0).
Notation "'false'" := trm_false (in custom sys_f at level 0).
Notation "'if' x 'then' y 'else' z" := (trm_if x y z) (in custom sys_f at level 89, x custom sys_f at level 99, y custom sys_f at level 99, z custom sys_f at level 99, left associativity).
Notation "'0'" := trm_zero (in custom sys_f at level 0).
Notation "'S' t" := (trm_succ t) (in custom sys_f at level 0, t custom sys_f at level 0).
Notation "'P' t" := (trm_pred t) (in custom sys_f at level 0, t custom sys_f at level 0).
Notation "'Z' t" := (trm_iszero t) (in custom sys_f at level 0, t custom sys_f at level 0).

(* To interpret string and nat as term and types variables without constructors *)
Coercion trm_var : string >-> trm.
Coercion typ_var : nat >-> typ.

Open Scope string_scope.

(* TEST *)
Check $< S (if true then 0 else S 0) >$.
Check ($<λ "k" : Nat , if (Z "k") then 0 else S S "k" >$). 

Goal (val $<true>$).
    auto using val, value_bool.
Abort.

(* =================== SUBSTITUTIONS =======================
  No α-conversion or free variable notion as we use variable conventions
  (variable capture shouldn't be relevant in type safety proof
  Designed as functions to avoid supplementary hypothesis in β-reduction
      - Substitutions of term into terms (λ→)
      - Substitutions of type into terms (λ2)
      - Substitutions of type into types (λω) (used for type annotation in terms)
  ========================================================== *)

(* Si definition of terms  and notations (couples with where clause)*)
Reserved Notation "'V{' x '→' s } t" (in custom sys_f at level 20, x constr).
Reserved Notation "'TT{' α '→' σ } X" (in custom sys_f at level 20, α constr).
Reserved Notation "'TV{' α '→' σ } M" (in custom sys_f at level 20, α constr).

(* substitution of a term variable (string) by a term in a term *)
Fixpoint sub_trm (x:string)(s t:trm) {struct t}: trm := match t with
  | trm_var y => if String.eqb x y then s else t
  | $<λ y : T , t1>$ =>
        if String.eqb x y then t else $<λ y : T , (V{x → s} t1)>$
  | $<Λ k, t1>$ =>  $<Λ k, (V{x → s}t1)>$
  | $<t1 t2>$ =>  $<(V{x → s}t1) (V{x → s}t2)>$
  | $<t1 [ T ]>$ => $<(V{x → s}t1) [ T ]>$
  | $<true>$ => $<true>$
  | $<false>$ => $<false>$
  | $<if t1 then t2 else t3>$ => 
        $<if (V{x → s}t1) then (V{x → s}t2) else (V{x → s}t3)>$
  | $<0>$ => $<0>$
  | $<S t1>$ => $<S (V{x → s}t1)>$ 
  | $<P t1>$ => $<P (V{x → s}t1)>$
  | $<Z t1>$ => $<Z (V{x → s}t1)>$
end
where "'V{' x '→' s } t" := (sub_trm x s t)(in custom sys_f).

(* TEST *)
Check $<"x" "x">$.

(* substitutions of a type variables (nat) by a type into a type *)
(* Avoid T bcause of Notation parsing conflict with TT{α→σ} and TV{α→σ *)
Fixpoint sub_typ (α:nat)(σ X:typ) {struct X} : typ := match X with
  | $<Bool>$ => $<Bool>$
  | $<Nat>$ => $<Nat>$
  | typ_var k => if (Nat.eqb k α) then σ else X
  | typ_arrow T1 T2 => typ_arrow $<TT{α → σ}T1>$ $<TT{α → σ}T2>$
  | $<∀ t1, T1>$ => if (Nat.eqb t1 α) then X else $<∀ t1, (TT{α → σ}T1)>$
end
where "'TT{' α '→' σ } X":= (sub_typ α σ X)(in custom sys_f).

(* substitution of a type variable (nat) by a type into a term *)
Fixpoint sub_typ2 (α:nat)(σ:typ)(M:trm) {struct M} : trm := match M with
  | trm_var y => M
  | $<λ x : X , t>$ => $<λ x : (TT{α → σ} X), (TV{α → σ}t)>$
  | $<Λ γ, t>$ =>  if (Nat.eqb α γ) then M else $<Λ γ, (TV{α → σ}t)>$
  | $<t1 t2>$ =>  $<(TV{α → σ}t1) (TV{α → σ}t2)>$
  | $<t [ X ]>$ => $<(TV{α → σ}t) [ TT{α → σ}X ]>$
  | $<true>$ => $<true>$
  | $<false>$ => $<false>$
  | $<if t1 then t2 else t3>$ => 
        $<if (TV{α → σ}t1) then (TV{α → σ}t2) else (TV{α → σ}t3)>$
  | $<0>$ => $<0>$
  | $<S t>$ => $<S (TV{α → σ}t)>$ 
  | $<P t>$ => $<P (TV{α → σ}t)>$
  | $<Z t>$ => $<Z (TV{α → σ}t)>$
end
where "'TV{' α '→' σ } M":= (sub_typ2 α σ M)(in custom sys_f).

(* TEST *)
Compute $<V{"x" → (S 0)}(if true then "x" else (Λ 1,λ "z" : 1→1, "z" "x"))>$.
Compute $<TV{1 → Nat}((Λ 2, λ "f" : 1 → 2, λ "x" : 1, "f" "x")[1 → Bool])>$.
Compute $<TT{1 → Nat}(TT{2 → (1 → Bool)}(((1 → 2) → 1 → 2)))>$.

(* ======================= β-REDUCTION ====================== 
  Design as Proposition (or binary relation) (confluence?)
  No call by value policy for type application ????
  (Since trm -> trm -> Prop)
  or do we extend β-reduction  of typpes on types ???
  will it appear in typing relation ?!?!
  ============================================================*)
Reserved Notation "t1 '→β' t2" (in custom sys_f at level 40).

Inductive one_step_red : trm -> trm -> Prop :=
  (* term redexes*)
  | red_V_redex : forall (x:string)(M N:trm)(X:typ),
      $<(λ x : X,M) N →β (V{x → N} M)>$
  | red_appV1 : forall (M M' N:trm),
       $<M →β M'>$ -> $<(M N) →β (M' N)>$
  | red_appV2 : forall (v M M':trm),
      (val v)->$<M →β M'>$ -> $<(v M) →β (v M')>$
  (* Type redexes*)
  | red_T_redex : forall (α:nat)(M:trm)(σ:typ),
      $<(Λ α, M) [σ] →β TV{α → σ} M>$
  | red_appT : forall (M M':trm)(σ : typ),
      $<M →β M'>$ -> $<M [σ] →β M' [σ]>$
  (*If then Else*)
  (* No call-by-value on M and N as they could be inconsistent (k/0) *)
  | red_if_true : forall (M N:trm),
      $<(if true then M else N) →β M>$
  | red_if_false : forall (M N:trm),
      $<(if false then M else N) →β N>$
  | red_if : forall (M M' N N':trm),
      $<M →β M'>$ ->
      $<(if M then N else N') →β (if M' then N else N')>$
  (* Successor *)
  | red_succ : forall (M M':trm),
      $<M →β M'>$ -> $<(S M) →β (S M')>$
  (* Predecessor *)
  | red_pred_z : $<P 0 →β 0>$
  | red_pred_succ : forall (v:trm),
      val v -> $<P (S v) →β v>$
  | red_pred : forall (M M':trm),
      $<M →β M'>$ -> $<(P M) →β (P M')>$
  (* Zero predicate *)
  | red_iszero_z : $<(Z 0) →β true>$
  | red_iszero_succ : forall (v:trm),
      val v -> $<(Z (S v)) →β false>$
  | red_iszero : forall (M M':trm),
      $<M →β M'>$ -> $<(Z M) →β (Z M')>$
where "t1 '→β' t2" := (one_step_red t1 t2)(in custom sys_f).

(* Reflexive transitive closure of the β-reduction import Relations *)

Definition multi_step_red := clos_refl_sym_trans trm one_step_red.

(* multi-step β-reduction notation ((sh/c)ould not be in sys_f) *)
Notation "t1 '↠β' t2" := (multi_step_red t1 t2)(in custom sys_f at level 40).

(* TEST *)
Fact red_1 : $<
        (Λ 1, (Λ 2, λ "f" : 1 → 2, λ "x" : 1, "f" "x")[1 → Bool])[Nat]
          →β
        (Λ 2, λ "f" : Nat → 2, λ "x" : Nat, "f" "x")[Nat → Bool]
        >$.
Proof.
  assert ($<(Λ 2, λ "f" : Nat → 2, λ "x" : Nat, "f" "x")[Nat → Bool]>$ =
          $<TV{1 → Nat}((Λ 2, λ "f" : 1 → 2, λ "x" : 1, "f" "x")[1 → Bool])>$).
    info_eauto using one_step_red.
  info_eauto using one_step_red.
Qed.

Fact red_2 : $<
         (Λ 2, λ "f" : Nat → 2, λ "x" : Nat, "f" "x")[Nat → Bool]
          →β
          λ "f" : Nat → (Nat → Bool), λ "x" : Nat, "f" "x"
       >$.
Proof.
  assert (


          $<λ "f" : Nat → (Nat → Bool), λ "x" : Nat, "f" "x">$ 
                                    = 
          $<TV{2 → (Nat → Bool)}(λ "f" : Nat → 2, λ "x" : Nat, "f" "x")>$


).
    info_eauto using one_step_red.
  info_eauto using one_step_red.
Qed.

Goal $<
       (Λ 1, (Λ 2, λ "f" : 1 → 2, λ "x" : 1, "f" "x")[1 → Bool])[Nat]
          ↠β
       λ "f" : Nat → (Nat → Bool), λ "x" : Nat, "f" "x"
      >$.

Print clos_refl_sym_trans.
Proof.
  apply rst_trans with (y:=$<(Λ 2, λ "f" : Nat → 2, λ "x" : Nat, "f" "x")[Nat → Bool]>$);
  (*eauto using multi_step_red;*)
  apply rst_step;
  [exact red_1 | exact red_2].
  Qed.

(* ======================= TYPING =======================
   Defining contexts as (partial) maps using option on terms
   Should context be functions that can directly applied to variables to yield
   option but requiring compute during proof 
    -Term context directly applied to term variable that yield some type or none
    -Type context directly applied to type variable (should yield bool ?)
   or else inductive proposition whose coonstructors can be integrated 
    into hint databases but Prop that deal either with context extension
    and variable membership may not be trivial
  ======================================================= *)

Definition ctxV := string -> option typ.
Definition ctx_nilV : ctxV := (fun _ => None).
Definition ctx_consV (s:string)(T:typ)(c:ctxV) : ctxV := 
                     (fun (x:string) =>  if (String.eqb s x) then (Some T) else (c x)).

Definition ctxT := nat -> option nat.
Definition ctx_nilT : ctxT := (fun _ => None).
Definition ctx_consT (n:nat)(c:ctxT) :=
                     (fun (x:nat) => if (Nat.eqb n x) then (Some n) else (c x)).

(* types and term synthax notations not so readable  *)
Notation "'nilV'" := (ctx_nilV)(in custom sys_f).
Notation "'nilT'" := (ctx_nilT)(in custom sys_f).
Notation "s ; t 'V::' c" := (ctx_consV s t c)(in custom sys_f at level 60, right associativity).
Notation "n 'T::' c" := (ctx_consT n c)(in custom sys_f at level 60, right associativity).

(* TEST *) 
Compute ($<"b" ; Bool V:: "x" ; Nat V:: nilV>$ "x").  
Compute ($<4 T:: 2 T:: 1 T:: nilT>$ 1).

Inductive BV (Δ:ctxT) : typ -> Prop :=
  | bv_bool : BV Δ $<Bool>$
  | bv_nat : BV Δ $<Nat>$
  | bv_varT : forall (α:nat),
                ((Δ α) = Some α) -> (BV Δ (typ_var α))
  | bv_arr : forall (σ δ:typ),
                (BV Δ σ) -> (BV Δ δ) -> (BV Δ $<σ → δ>$)
  | bv_all : forall (α:nat)(σ:typ),
                (BV $<α T:: Δ>$ σ) -> (BV Δ $<∀ α, σ>$).

(* TEST *)
Goal (BV $<1 T:: 4 T:: nilT>$ $<∀ 9,4 → 9>$).
  auto using BV.
 Qed.

Reserved Notation "Γ '-' Δ '⊢' t ∈ T" (in custom sys_f at level 40).

Inductive typ_rel (Γ : ctxV)(Δ : ctxT) : trm -> typ -> Prop :=
  | typ_rel_var : forall (x : string)(σ : typ),
                      (BV Δ σ) ->
                      (Γ x) = Some σ ->(* Will need to use compute tactic *)
                      $<Γ - Δ ⊢ x ∈ σ>$
  | typ_rel_arr_i : forall (x : string)(M : trm)(σ δ : typ),
                      $<(x ; σ V:: Γ) - Δ ⊢ M ∈ δ>$ ->
                      $<Γ - Δ ⊢ (λ x : σ, M) ∈ (σ → δ)>$
  | typ_rel_arr_e : forall (M N : trm)(σ δ : typ),
                      $<Γ - Δ ⊢ M ∈ (σ → δ)>$ ->
                      $<Γ - Δ ⊢ N ∈ σ>$ ->
                      $<Γ - Δ ⊢ (M N) ∈ δ>$
  | typ_rel_all_i : forall (α : nat)(M : trm)(σ : typ),
                      $<Γ - (α T:: Δ) ⊢ M ∈ σ>$ ->
                      $<Γ - Δ ⊢ (Λ α , M) ∈ (∀α , σ)>$
  | typ_rel_all_e : forall (α : nat)(M : trm)(σ δ : typ),
                      $<Γ - Δ ⊢ M ∈ (∀ α , σ)>$ ->
                      $<Γ - Δ ⊢ (M [δ]) ∈ (TT{α → δ}σ)>$
  | typ_rel_true : $<Γ - Δ ⊢ true ∈ Bool>$
  | typ_rel_false : $<Γ - Δ ⊢ false ∈ Bool>$
  | typ_rel_if : forall (b M N : trm)(σ : typ),
                      $<Γ - Δ ⊢ b ∈ Bool>$->
                      $<Γ - Δ ⊢ M ∈ σ>$ ->
                      $<Γ - Δ ⊢ N ∈ σ>$ ->
                      $<Γ - Δ ⊢ (if b then M else N) ∈ σ>$
  | typ_rel_zero : $<Γ - Δ ⊢ 0 ∈ Nat>$
  | typ_rel_succ : forall (M : trm),
                      $<Γ - Δ ⊢ M ∈ Nat>$ ->
                      $<Γ - Δ ⊢ (S M) ∈ Nat>$
  | typ_rel_pred : forall (M : trm),
                      $<Γ - Δ ⊢ M ∈ Nat>$ ->
                      $<Γ - Δ ⊢ (P M) ∈ Nat>$
  | typ_rel_iszero : forall (M : trm),
                      $<Γ - Δ ⊢ M ∈ Nat>$ ->
                      $<Γ - Δ ⊢ (Z M) ∈ Bool>$
where "Γ '-' Δ '⊢' t ∈ T" := (typ_rel Γ Δ t T)(in custom sys_f).

Check clos_refl_sym_trans trm one_step_red.
Check multi_step_red.

(* Theorem database for auto the using statement is sufficient for the moment *)
Hint Constructors one_step_red clos_refl_sym_trans typ_rel BV : sys_f_base.
(* Write Ltac strategy that include compute in auto-linke tactic loop for typing *)
(* Write Ltac strategy that do prove provided substitution and rewrite  ???? *)

(* TEST *)
(*
Definition Γ := $<nilV>$.
Definition Δ := $<nilT>$.
Definition Id := ($<(Λ 4 , λ "x" : 4 , "x")>$).
Definition trm1 := $<((Λ 1, (Λ 2, λ "f" : 1 → 2, λ "x" : 1, "f" "x")[1 → Bool])[Nat])>$.
Definition trm2 := $<Λ 1,λ "f" : 1 → 1,λ "x" : 1, ("f" ("f" "x"))>$.

Goal $<("x" ; Nat V:: Γ) - Δ ⊢ "x" ∈ Nat>$.
  info_eauto with sys_f_base.
  Abort.

Goal $<("x" ; Nat V:: Γ) - Δ ⊢ (if (Z 0) then "x" else (S "x")) ∈ Nat>$.
  (* eauto use simple apply and not  eapply. It reason modulo conversion
and only apply to subterms that contains no variables to instanciate.
Used because it fail faster than apply in backtracking strategies *)
  info_eauto 10 with sys_f_base.
  Abort.

Goal $<Γ - Δ ⊢ ((λ "x" : Nat, (S "x")) 0) ∈ Nat>$.
  info_eauto with sys_f_base.
  Abort.

Goal $<(λ"x":Nat, S "x") 0 →β S 0>$.
  info_eauto with sys_f_base.
  Abort.

Goal $<Γ - Δ ⊢ (S 0) ∈ Nat>$.
  info_eauto with sys_f_base.
  Abort.

(*Hint Extern 10 => compute : sys_f_base.*)

Print trm2.
Fact typ_1 : $<Γ - Δ ⊢ trm2 ∈ (∀ 1,(1 → 1) → 1 → 1)>$.
Proof.
  apply typ_rel_all_i.
  apply typ_rel_arr_i.
  apply typ_rel_arr_i.
  apply typ_rel_arr_e with (σ:=(typ_var 1)).
    info_eauto with sys_f_base.
    apply typ_rel_arr_e with (σ:=(typ_var 1));info_eauto with sys_f_base.
Qed.

Goal $<Γ - Δ ⊢ (trm2[Nat]) ∈ ((Nat → Nat) → Nat → Nat)>$.
Proof.
  pose proof typ_1.
  assert ($<(Nat → Nat) → Nat → Nat>$ = $<TT{1 → Nat}((1 → 1) → 1 → 1)>$).
  auto.
  rewrite H0.
  info_eauto with sys_f_base.
Qed.

Print trm1.
Goal $<Γ - Δ ⊢ trm1 ∈ ((Nat → (Nat → Bool)) → Nat → (Nat → Bool))>$.
Proof.
  assert ($<(Nat → (Nat → Bool)) → Nat → (Nat → Bool)>$ =
          $<TT{1 → Nat}((1 → (1 → Bool)) → 1 → (1 → Bool))>$).
    simpl;easy.
  rewrite H.
  apply typ_rel_all_e.
  apply typ_rel_all_i.

  assert ($<(1 → (1 → Bool)) → 1 → 1 → Bool>$ =
          $<TT{2 → (1 → Bool)}((1 → 2) → 1 → 2)>$).
  simpl;easy.

  rewrite H0.
  apply typ_rel_all_e.
  apply typ_rel_all_i.
  apply typ_rel_arr_i.
  apply typ_rel_arr_i.
  apply typ_rel_arr_e with (σ:=typ_var 1);info_eauto with sys_f_base.
Qed.
*)

(* =========== INVERSION OF THE TYPING RELATION ========== *)
(* BOOLEAN *)
Lemma itr_true : forall (Γ : ctxV)(Δ : ctxT)(σ:typ),
                $<Γ - Δ ⊢ true ∈ σ>$ -> σ = $<Bool>$.
Proof.
  induction σ;easy.
Qed.

Lemma itr_false : forall (Γ : ctxV)(Δ : ctxT)(σ:typ),
                $<Γ - Δ ⊢ false ∈ σ>$ -> σ = $<Bool>$.
Proof.
  induction σ;easy.
Qed.
(* IF THEN ELSE *)
Lemma itr_ite : forall (Γ : ctxV)(Δ : ctxT)(M N N':trm)(σ:typ),
                $<Γ - Δ ⊢ (if M then N else N')∈ σ>$ -> (* Could add M of type Bool *)
                ($<Γ - Δ ⊢ M ∈ Bool>$ /\ $<Γ - Δ ⊢ N ∈ σ>$ /\ $<Γ - Δ ⊢ N' ∈ σ>$).
Proof.
  intros.
  split;inversion H;easy.
Qed.
(* NATURAL NUMBERS *)
Lemma itr_zero : forall (Γ : ctxV)(Δ : ctxT)(σ:typ),
                $<Γ - Δ ⊢ 0 ∈ σ>$ -> σ = $<Nat>$.
Proof.
  induction σ;easy.
Qed.

Lemma itr_succ : forall (Γ : ctxV)(Δ : ctxT)(M:trm)(σ:typ),
                $<Γ - Δ ⊢ (S M) ∈ σ>$ ->
                ($<Γ - Δ ⊢ M ∈ Nat>$ /\ σ = $<Nat>$).
Proof.
  intros;split;[inversion H | induction σ];easy.
Qed.

Lemma itr_pred : forall (Γ : ctxV)(Δ : ctxT)(M:trm)(σ:typ),
                $<Γ - Δ ⊢ (P M) ∈ σ>$ ->
                ($<Γ - Δ ⊢ M ∈ Nat>$ /\ σ = $<Nat>$).
Proof.
  intros;split;[inversion H | induction σ];easy.
Qed.

Lemma itr_iszero : forall (Γ : ctxV)(Δ : ctxT)(M:trm)(σ:typ),
                $<Γ - Δ ⊢ (Z M) ∈ σ>$ ->
                ($<Γ - Δ ⊢ M ∈ Nat>$ /\ σ = $<Bool>$).
Proof.
  intros;split;[inversion H | induction σ];easy.
Qed.
(* VARIABLES *)
Lemma itr_varV : forall (Γ : ctxV)(Δ : ctxT)(x:string)(σ:typ),
                $<Γ - Δ ⊢ x ∈ σ>$ -> (Γ x) = Some σ.
Proof.
  intros;inversion H;easy.
Qed.
(* ABSTRACTIONS *)
Lemma itr_absV : forall (Γ : ctxV)(Δ : ctxT)(x:string)(M:trm)(σ δ:typ),
                  $<Γ - Δ ⊢ (λ x : δ, M) ∈ σ>$ -> 
                  (exists (γ:typ),
                       $<(x; δ V::Γ) - Δ ⊢ M ∈ γ>$ /\ σ = $<δ → γ>$).
Proof.
  intros;inversion H.
  apply ex_intro with δ0;easy.
Qed.

Lemma itr_absT : forall (Γ : ctxV)(Δ : ctxT)(α:nat)(M:trm)(σ:typ),
                  $<Γ - Δ ⊢ (Λ α, M) ∈ σ>$ ->
                  (exists (γ:typ),
                       $<Γ - (α T:: Δ) ⊢ M ∈ γ>$ /\ σ = $<∀ α, γ>$).
Proof.
  intros;inversion H.
  apply ex_intro with σ0;easy.
Qed.
(* APPLICATIONS *)
Lemma itr_appV : forall (Γ : ctxV)(Δ : ctxT)(M N:trm)(σ:typ),
                  $<Γ - Δ ⊢ (M N) ∈ σ>$ ->
                  (exists (δ γ:typ),
                        $<Γ - Δ ⊢ M ∈ (δ → γ)>$ /\ $<Γ - Δ ⊢ N ∈ δ>$ /\ σ = γ).
Proof.
  intros;inversion H.
  exists σ0.
  exists σ.
  easy.
Qed.

Lemma itr_appT : forall (Γ : ctxV)(Δ : ctxT)(M:trm)(σ δ:typ),
                  $<Γ - Δ ⊢ (M [δ]) ∈ σ>$ ->
                  (exists (α:nat)(γ:typ),
                      $<Γ - Δ ⊢ M ∈ (∀ α,γ)>$ /\ σ = $<TT{α → δ}γ>$).
Proof.
  intros;inversion H.
  exists α.
  exists σ0.
  easy.
Qed. 

Hint Resolve itr_true itr_false itr_ite itr_zero itr_succ itr_pred itr_iszero
    itr_varV itr_absV itr_absT itr_appV itr_appT : sys_f_base.

(* ================== UNIQUENESS OF TYPES ================ *)

Theorem uniq_typ : forall (M:trm)(σ δ:typ)(Γ : ctxV)(Δ : ctxT),
                    $<Γ - Δ ⊢ M ∈ σ>$ ->
                    $<Γ - Δ ⊢ M ∈ δ>$ -> σ = δ.
Proof.
  induction M.
Show 2.
  intros. 
    info_eauto with sys_f_base.
    assert (H1 := (itr_varV _ _ _ _ H)).
    assert (H2 := (itr_varV _ _ _ _ H0)).
    rewrite H1 in H2.
    injection H2;auto.

    intros.
    assert (H1 := itr_absV _ _ _ _ _ _ H). 
    assert (H2 := itr_absV _ _ _ _ _ _ H0).
    clear H H0;destruct H1;destruct H;destruct H2;destruct H1.
    assert (H3:=(IHM _ _ _ _ H H1));clear H H1.
    rewrite H3 in H0.
    rewrite <- H2 in H0.
    assumption.

    intros.
    assert (H1:=(itr_absT _ _ _ _ _ H)). 
    clear H;destruct H1;destruct H. 
    assert (H2:=(itr_absT _ _ _ _ _ H0)).
    clear H0;destruct H2;destruct H0.
    assert (H3:=(IHM _ _ _ _ H H0)).
    clear H H0.
    rewrite H3 in H1;rewrite <- H2 in H1.
    assumption.

    intros.
    assert (H1:=(itr_appV _ _ _ _ _ H));clear H.
    destruct H1;destruct H;destruct H;destruct H1.
    assert (H3:=(itr_appV _ _ _ _ _ H0));clear H0.
    destruct H3;destruct H0;destruct H0;destruct H3.
    assert (H5:=(IHM2 _ _ _ _ H1 H3));clear H1 H3.
    assert (H1:=(IHM1 _ _ _ _ H H0));clear H H0.
    rewrite H5 in H1;injection H1;intro.
    rewrite H in H2;rewrite <- H4 in H2.
    assumption.

    intros.
    assert (H1:=(itr_appT _ _ _ _ _ H));clear H.
    destruct H1;destruct H; destruct H.
    assert (H2:=(itr_appT _ _ _ _ _ H0));clear H0.
    destruct H2;destruct H0; destruct H0.
    assert (H3:=(IHM _ _ _ _ H H0)).
    clear H H0;injection H3;intros.
    rewrite H in H1;rewrite H0 in H1;clear H H0 H3.
    rewrite <- H2 in H1.
    assumption.

    intros.
    assert (H1:=(itr_true _ _ _ H));clear H.
    assert (H:=(itr_true _ _ _ H0));clear H0.
    rewrite <- H in H1.
    assumption.

    intros.
    assert (H1:=(itr_false _ _ _ H));clear H.
    assert (H:=(itr_false _ _ _ H0));clear H0.
    rewrite <- H in H1.
    assumption.

2:{
  intros.
  assert (H1:=(itr_zero _ _ _ H));clear H.
  assert (H:=(itr_zero _ _ _ H0));clear H0.
  rewrite <- H in H1.
  assumption.
}
2:{
  intros.
  assert (H1:=(itr_succ _ _ _ _ H)).
  clear H;destruct H1.
  assert (H2:=(itr_succ _ _ _ _ H0)).
  clear H0;destruct H2.
  rewrite <- H2 in H1.
  assumption.
}
2:{
  intros.
  assert (H1:=(itr_pred _ _ _ _ H)).
  clear H;destruct H1.
  assert (H2:=(itr_pred _ _ _ _ H0)).
  clear H0;destruct H2.
  rewrite <- H2 in H1.
  assumption.
}
2:{
  intros.
  assert (H1:=(itr_iszero _ _ _ _ H)).
  clear H;destruct H1.
  assert (H2:=(itr_iszero _ _ _ _ H0)).
  clear H0;destruct H2.
  rewrite <- H2 in H1.
  assumption.
} 
    intros.
    assert(H1:=(itr_ite _ _ _ _ _ _ H)).
    clear H;destruct H1;destruct H1.
    assert(H3:=(itr_ite _ _ _ _ _ _ H0)).
    clear H0;destruct H3;destruct H3.
    exact (IHM2 _ _ _ _ H1 H3). 
Qed.

Check uniq_typ.
(* ======================= CANONICAL FORMS ==================
  Usefool lemma for facts about canonical forms regarding their type
  =========================================================== *)
(* boolean values must be true or false *)
Lemma can_bool : forall (Γ:ctxV)(Δ:ctxT)(M:trm),
                    (val M) -> $<Γ - Δ ⊢ M ∈ Bool>$ ->
                    (M = $<true>$  \/ M = $<false>$).
Proof.
  intros.
  inversion H;destruct H1;auto.

    assert (H1:=(itr_zero _ _ _ H0)).
    discriminate.

    assert (H3:=(itr_succ _ _ _ _ H0)).
    destruct H3.
    discriminate.

    assert (H1:=(itr_absV _ _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.

    assert (H1:=(itr_absT _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.
Qed.

(* Corollary with empty term context *)
Definition can_bool_empty := (can_bool ctx_nilV ctx_nilT).

(* Natural values must be 0 or S n where n is itself a natural value *)
Lemma can_nat : forall (Γ:ctxV)(Δ:ctxT)(M:trm),
                    (val M) -> $<Γ - Δ ⊢ M ∈ Nat>$ ->
                    (M = $<0>$ \/ (exists (N:trm),
                                  (value_nat N) /\ $<Γ - Δ ⊢ N ∈ Nat>$ /\
                                  M = $<S N>$)).
Proof.
  intros.
  inversion H;destruct H1;auto.

    assert (H1:=(itr_true _ _ _ H0)).
    discriminate.

    assert (H1:=(itr_false _ _ _ H0)).
    discriminate.

    right.
    exists t'.
    auto. 

    split.
      auto using val.
      split.
         inversion H0;easy.
    easy.

    assert (H1 :=(itr_absV _ _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.

    assert (H1:=(itr_absT _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.
Qed.
(* Corollary with empty term context *)
Definition can_nat_empty := (can_nat ctx_nilV ctx_nilT).
(* arrow type values must be λ x : σ. M *)
Lemma can_absV : forall (Γ:ctxV)(Δ:ctxT)(M:trm)(α δ:typ),
                    (val M) -> $<Γ - Δ ⊢ M ∈ (α → δ)>$ ->
                    (exists (x:string)(N:trm),
                            $<(x; α V::Γ) - Δ ⊢ N ∈ δ>$ /\ M = $<λ x : α, N>$).
Proof.
  intros.
  inversion H;destruct H1;auto.
 
    assert (H1:=(itr_true _ _ _ H0)).
    discriminate.

    assert (H1:=(itr_false _ _ _ H0)).
    discriminate.

    assert (H1:=(itr_zero _ _ _ H0)).
    discriminate.

    assert (H3:=(itr_succ _ _ _ _ H0)).
    destruct H3.
    discriminate.

    exists x;exists t.
    inversion H0.
    split;easy.

    assert (H1:=(itr_absT _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.
Qed.
(* Corollary with empty term context *)
Definition can_absV_empty := (can_absV ctx_nilV ctx_nilT).
(* forall type values must be Λ α. M *)
Lemma can_absT : forall (Γ:ctxV)(Δ:ctxT)(α:nat)(M:trm)(δ:typ),
                    (val M) -> $<Γ - Δ ⊢ M ∈ (∀ α, δ)>$ ->
                    (exists (N:trm),
                            $<Γ - (α T::Δ) ⊢ N ∈ δ>$ /\ M = $<Λ α, N>$).
Proof.
    intros.
    inversion H;destruct H1.

    assert (H1:=(itr_true _ _ _ H0)).
    discriminate.

    assert (H1:=(itr_false _ _ _ H0)).
    discriminate.

    assert (H1:=(itr_zero _ _ _ H0)).
    discriminate.

    assert (H3:=(itr_succ _ _ _ _ H0)).
    destruct H3.
    discriminate.

    assert (H1 :=(itr_absV _ _ _ _ _ _ H0)).
    destruct H1;destruct H1.
    discriminate.

    exists t.
    inversion H0.
    split;easy.
Qed.
(* Corollary with empty term context *)
Definition can_absT_empty := (can_absT ctx_nilV ctx_nilT).

(* ================================================================
   ************************ PROGRESS ******************************
   A well typed term can either be a value or take an evaluation step
  *****************************************************************
   =============================================================== *)


Theorem sys_f_progress : forall (M:trm)(δ:typ),
                            ($< nilV - nilT ⊢ M ∈ δ>$) ->
                            ((val M) \/ (exists (N:trm), $<M →β N>$)).
Proof with eauto with sys_f_base.

  intros M δ H.
  remember ctx_nilV as Γ.
  remember ctx_nilT as Δ.

  induction H;subst Γ;subst Δ. (*eauto 100 using one_step_red, val, value_nat, value_bool  with sys_f_base.*)

  assert ($< nilV >$ x = None).
    compute;easy.
  easy.

  left.
  auto using val.

  right.
  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val M \/ (exists N : trm, $< M →β N >$)) by exact (IHtyp_rel1 H1 H2).
  clear H1 H2.
  destruct H3.
    assert (exists (x : string) (N : trm),
         $< (x; σ V:: nilV) - nilT ⊢ N ∈ δ >$ /\ M = $< λ x : σ, N >$) by exact (can_absV_empty _ _ _ H1 H).
    destruct H2;destruct H2;destruct H2.
    assert ($< (λ x : σ, x0) N →β V{ x → N} x0 >$) by exact (red_V_redex x x0 N σ).
    rewrite <- H3 in H4.
    exists ($<V{ x → N} x0 >$);easy.

    destruct H1.
    assert $< M N →β x N >$ by exact (red_appV1 _ _ N H1).
    exists ($<x N>$);easy.

  left.
  auto using val.

  right.
  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val M \/ (exists N : trm, $< M →β N >$)) by exact (IHtyp_rel H0 H1).
  clear IHtyp_rel H1 H0.
  destruct H2.
    assert (exists N : trm,
        $< nilV - α T:: nilT ⊢ N ∈ σ >$ /\ M = $< Λ α, N >$) by exact (can_absT_empty _ _ _ H0 H).
    clear H0;destruct H1;destruct H0.
    assert ($< (Λ α, x) [δ] →β TV{ α → δ} x >$) by exact (red_T_redex α x δ).
    rewrite <- H1 in H2.
    exists ($<TV{ α → δ} x >$);easy.

   destruct H0.
   assert ($< M [δ] →β x [δ] >$) by exact (red_appT _ _ δ H0).
   exists ($<x [δ] >$);easy.

  left.
  auto using val, value_bool.

  left.
  auto using val, value_bool.

  Check can_bool_empty.
  right.
  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val b \/ (exists N : trm, $< b →β N >$)) by exact (IHtyp_rel1 H2 H3).
  clear H0 H1 H2 H3 IHtyp_rel1 IHtyp_rel2 IHtyp_rel3;destruct H4.

    assert (b = $< true >$ \/ b = $< false >$) by exact (can_bool_empty b H0 H).
    clear H0;destruct H1;rewrite H0.
      assert ($< (if true then M else N) →β M >$) by exact (red_if_true M N).
      exists M;easy. 

      assert ($< (if false then M else N) →β N >$) by exact (red_if_false M N).
      exists N;easy.

    destruct H0.
    assert ($< (if b then M else N) →β (if x then M else N) >$) by exact (red_if b x M N H0).
    exists ($<(if x then M else N) >$);easy.

  left.
  auto using val, value_nat.

  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val M \/ (exists N : trm, $< M →β N >$)) by exact (IHtyp_rel H0 H1).
  clear H0 H1 IHtyp_rel;destruct H2.
    Show 2.
    left.  
    assert (M = $< 0 >$ \/ (exists N : trm, value_nat N /\ $< nilV - nilT ⊢ N ∈ Nat >$ /\ M = $< S N >$)) by exact (can_nat_empty _ H0 H).
    destruct H1.
        rewrite H1.
        auto using val, value_nat.

        destruct H1;destruct H1;destruct H2.
        assert (value_nat $<S x>$) by auto using value_nat.
        rewrite <- H3 in H4.
        eauto using val, value_nat.

    right;destruct H0.
    assert ($< S M →β S x >$) by exact (red_succ M x H0).
    exists ($<S x >$);easy.

  right.
  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val M \/ (exists N : trm, $< M →β N >$)) by exact (IHtyp_rel H0 H1).
  clear H0 H1 IHtyp_rel;destruct H2.
    assert (M = $< 0 >$ \/ (exists N : trm, value_nat N /\ $< nilV - nilT ⊢ N ∈ Nat >$ /\ M = $< S N >$)) by exact (can_nat_empty _ H0 H).
      destruct H1.
      rewrite H1.
      
        exists $<0>$.
        auto using one_step_red.

        destruct H1;destruct H1;destruct H2.
        rewrite H3.
        exists x.
        assert (val x) by auto using val.
        eauto using one_step_red.

      destruct H0.
       assert ($< P M →β P x >$) by exact (red_pred M x H0).
      exists ($<P x >$);easy.

  right.
  assert ($< nilV >$ = $< nilV >$) by easy.
  assert ($< nilT >$ = $< nilT >$) by easy.
  assert (val M \/ (exists N : trm, $< M →β N >$)) by exact (IHtyp_rel H0 H1).
  clear H0 H1 IHtyp_rel;destruct H2.
    assert (M = $< 0 >$ \/ (exists N : trm, value_nat N /\ $< nilV - nilT ⊢ N ∈ Nat >$ /\ M = $< S N >$)) by exact (can_nat_empty _ H0 H).
      destruct H1.
      rewrite H1.
      
        exists $<true>$.
        auto using one_step_red.

        destruct H1;destruct H1;destruct H2.
        rewrite H3.
        exists $<false>$.
        assert (val x) by auto using val.
        eauto using one_step_red.

      destruct H0.
       assert ($< Z M →β Z x >$) by exact (red_iszero M x H0).
      exists ($<Z x >$);easy.
Qed. 

(* ==================== WEAKENING ==================== *)

Compute ($< "x" ; Bool V:: "x" ; Nat V:: ctx_nilV>$ "x").

Fact update_eqV : forall (Γ : ctxV)(x:string)(σ:typ),
                      ($< x ; σ V:: Γ>$ x) = Some σ.
Proof.
  intros.
  unfold ctx_consV.
  assert ((x =? x) = true) by exact (eqb_refl x).
  rewrite H;easy.
Qed.

Fact update_eqT : forall (Δ : ctxT)(α:nat),
                      ($< α T:: Δ>$ α) = Some α.
Proof.
  intros.
  unfold ctx_consT.
  rewrite (Nat.eqb_refl α);easy.
Qed.

Lemma update_neqV : forall (Γ : ctxV)(x y:string)(σ:typ),
                      (y <> x)->
                      ($< y ; σ V:: Γ>$ x) = (Γ x).
Proof.
  intros.
  unfold ctx_consV.
  assert ((y =? x) = false <-> y <> x) by exact (eqb_neq y x).
  destruct H0.
  rewrite (H1 H);easy.
Qed.

Lemma update_neqT : forall (Δ:ctxT)(α μ:nat),
                      (μ <> α)->
                      ($< μ T:: Δ>$ α) = (Δ α).
Proof.
  intros.
  unfold ctx_consT.
  assert ((μ =? α)%nat = false <-> μ <> α) by exact (Nat.eqb_neq μ α).
  destruct H0.
  rewrite (H1 H);easy.
Qed.

Definition includedinV (Γ Γ' : ctxV) :=  forall (x:string)(σ:typ),
                  ((Γ x) = Some σ) ->  ((Γ' x) = Some σ).

Definition includedinT (Δ Δ' : ctxT) :=  forall (α:nat),
                  ((Δ α) = Some α) ->  ((Δ' α) = Some α).

Infix "V⊆" := includedinV (in custom sys_f at level 80).
Infix "T⊆" := includedinT (in custom sys_f at level 80).

Lemma includedin_updateV : forall (Γ Γ':ctxV)(x:string)(σ:typ),
                             $<Γ V⊆ Γ'>$ ->
                             $<(x ; σ V:: Γ) V⊆ (x ; σ V:: Γ')>$.
Proof.
  unfold includedinV.
  intros Γ Γ' x σ H.
  intros y δ. 
  destruct (eqb_spec x y) as [Hxy | Hxy].
    rewrite Hxy.
    rewrite update_eqV.
    rewrite update_eqV.
    easy.

    rewrite update_neqV.
    intro; rewrite <- H0.
    rewrite <- (H _ _ H0) in H0;rewrite H0.
    exact (update_neqV Γ' _ _ σ Hxy).

    easy.
Qed.

Lemma includedin_updateT : forall (Δ Δ':ctxT)(α:nat),
                             $<Δ T⊆ Δ'>$ ->
                             $<(α T:: Δ) T⊆ (α T:: Δ')>$.
Proof.
  unfold includedinT.
  intros Δ Δ' α H.
  intros μ. 
  destruct (Nat.eqb_spec α μ) as [Hxy | Hxy].
    rewrite Hxy.
    rewrite update_eqT.
    rewrite update_eqT.
    easy.

    rewrite update_neqT.
    intro; rewrite <- H0.
    rewrite <- (H _ H0) in H0;rewrite H0.
    exact (update_neqT Δ' _ _ Hxy).

    easy.
Qed.

Print BV.

Lemma BV_updateT : forall (Δ Δ':ctxT)(σ:typ),
                             $<Δ T⊆ Δ'>$ ->
                             (BV Δ σ) -> (BV Δ' σ).
Proof.
  intros.
  generalize dependent Δ'.
  induction H0;eauto using includedin_updateT with sys_f_base.
Qed.

Fact cons_includedinT : forall (Δ:ctxT)(n:nat), $<Δ T⊆ (n T:: Δ)>$.
Proof.
  unfold includedinT.
  intros.
  destruct (Nat.eqb_spec n α);unfold ctx_consT;[destruct (Nat.eqb_eq n α) | destruct (Nat.eqb_neq n α)].
    rewrite (H1 e).
    f_equal;assumption.

    rewrite (H1 n0);assumption.
Qed.

Corollary BV_cons_updateT : forall (Δ:ctxT)(n:nat)(σ:typ), (BV Δ σ) -> (BV $<n T:: Δ>$ σ).
Proof.
  intros.
  exact (BV_updateT _ _ σ (cons_includedinT Δ n) H).
Qed.

Lemma weakeningV : forall (Γ Γ':ctxV)(Δ:ctxT)(M:trm)(σ:typ), 
                      $<Γ V⊆ Γ'>$ ->
                      $<Γ - Δ ⊢ M ∈ σ>$ ->
                      $<Γ' - Δ ⊢ M ∈ σ>$.
Proof.
  intros.
  generalize dependent Γ'.
  induction H0;eauto using includedin_updateV with sys_f_base.
Qed.

Corollary empty_weakeningV : forall (Γ:ctxV)(Δ:ctxT)(M:trm)(σ:typ),
                      $<nilV - Δ ⊢ M ∈ σ>$ ->
                      $<Γ - Δ ⊢ M ∈ σ>$.
Proof.
  intros.
  apply weakeningV with (Γ:=$<nilV>$).
    unfold includedinV.
    intros.
    compute in H0.
    inversion H0.

    easy.
Qed.


Lemma weakeningT : forall (Γ:ctxV)(Δ Δ':ctxT)(M:trm)(σ:typ), 
                      $<Δ T⊆ Δ'>$ ->
                      $<Γ - Δ ⊢ M ∈ σ>$ ->
                      $<Γ - Δ' ⊢ M ∈ σ>$.
Proof.
  intros.
  generalize dependent Δ'.
  induction H0;eauto using includedin_updateT, BV_updateT with sys_f_base.
Qed.

Corollary empty_weakeningT : forall (Γ:ctxV)(Δ:ctxT)(M:trm)(σ:typ),
                      $<Γ - nilT ⊢ M ∈ σ>$ ->
                      $<Γ - Δ ⊢ M ∈ σ>$.
Proof.
  intros.
  apply weakeningT with (Δ:=$<nilT>$).
    unfold includedinT.
    intros.
    compute in H0;inversion H0.

    easy.
Qed.

Lemma weakening_neq_var : forall (Γ:ctxV)(x y:string)(σ γ:typ),
                       (x <> y) ->
                       $< (x; σ V:: y; γ V:: Γ) V⊆ (y ; γ V:: x; σ V:: Γ)>$.
Proof.
  intros.
  unfold includedinV.
  intros.
  destruct (eqb_spec x x0);destruct (eqb_spec y x0).
    rewrite <- e0 in e.
    contradiction.

    unfold ctx_consV in H0.
    destruct (eqb_eq x x0).
    rewrite (H2 e) in H0.
    unfold ctx_consV.
    rewrite (H2 e).
    destruct (eqb_neq y x0).
    rewrite (H4 n).
    exact H0.

    unfold ctx_consV in H0.
    destruct (eqb_eq y x0).
    rewrite (H2 e) in H0.
    unfold ctx_consV.
    rewrite (H2 e).
    destruct (eqb_neq x x0).
    rewrite (H4 n) in H0.
    exact H0.

    unfold ctx_consV in H0.
    unfold ctx_consV.
    destruct (eqb_neq y x0).
    destruct (eqb_neq x x0).
    rewrite (H4 n) in H0.
    rewrite (H4 n).
    rewrite (H2 n0).
    rewrite (H2 n0) in H0.
    assumption.
Qed.

Lemma weakening_double_var : forall (Γ:ctxV)(x:string)(σ γ:typ),
                       $< (x; σ V:: x; γ V:: Γ) V⊆ (x; σ V:: Γ)>$.
Proof.
  intros.
  unfold includedinV.
  intros.
  destruct (eqb_spec x x0).
    destruct (eqb_eq x x0).
    unfold ctx_consV in H.
    rewrite (H1 e) in H.
    unfold ctx_consV.
    rewrite (H1 e).
    easy.

    destruct (eqb_neq x x0).
    unfold ctx_consV in H.
    rewrite (H1 n) in H.
    unfold ctx_consV.
    rewrite (H1 n).
    easy.
Qed.
 
Lemma weakeningV_abs_var : forall (Γ:ctxV)(Δ:ctxT)(x:string)(M:trm)(σ δ γ:typ),
                       $<(x ; γ V:: Γ) - Δ ⊢ ( λ x : σ, M) ∈ δ >$ ->
                        $< Γ - Δ ⊢ ( λ x : σ, M) ∈ δ >$.
Proof.
  intros.
  inversion H.
  apply typ_rel_arr_i.
  assert ($< x; σ V:: x; γ V:: Γ V⊆ x; σ V:: Γ >$) by exact (weakening_double_var Γ x σ γ).
  exact (weakeningV _ _ _ _ _ H5 H4).
Qed.


(* =====================================================================
*****************SUBSTITUTION LEMMA FOR TERMS **************************
====================================================================== *)

Lemma substitutionV : forall (Γ:ctxV)(Δ:ctxT)(x:string)(M s:trm)(σ δ:typ),
                                (BV Δ σ) ->
                                $<(x ; σ V:: Γ) - Δ ⊢ M ∈ δ>$ ->
                                $< nilV - Δ ⊢ s ∈ σ>$ ->
                                $< Γ - Δ ⊢ (V{x → s}M) ∈ δ>$.
Proof with eauto with sys_f_base.
  intros.
  generalize dependent Γ.
  generalize dependent Δ.
  generalize dependent δ.
  induction M;intros.

  (* VARIABLE *)
  simpl.
  destruct (eqb_spec x s0).
  assert ($< (x; σ V:: Γ) - Δ ⊢ x ∈ σ >$).
  apply typ_rel_var.
    easy.

    cbv beta delta [ctx_consV].
    assert ((x =? x) = true) by exact (eqb_refl x).
    rewrite H2.
    easy.
  rewrite <- e in H0.
  assert (δ = σ) by exact (uniq_typ _ _ _ _ _ H0 H2).
  rewrite <- H3 in H1.
  apply empty_weakeningV.
  easy.

  (* ABSTRACTION ON TERMS *)
  inversion H0.
  cbv beta delta [ctx_consV] in H4.
  destruct (eqb_neq x s0).
  rewrite (H7 n) in H4.
  exact (typ_rel_var _ _ _ _ H3 H4).
  destruct (itr_absV _ _ _ _ _ _ H0).
  destruct H2.
  rewrite H3 in H0.
  destruct (eqb_spec x s0).
  cbv beta iota delta [sub_trm].
  destruct (eqb_eq x s0).
  rewrite (H5 e).
  rewrite <- H3 in H0.
  rewrite e in H0.
  exact (weakeningV_abs_var _ _ _ _ _ _ _ H0).
  assert ($< s0; t V:: x; σ V:: Γ V⊆ x; σ V:: s0; t V:: Γ >$) by exact (weakening_neq_var Γ s0 x t σ (not_eq_sym n)).
  assert ($< (x; σ V:: s0; t V:: Γ) - Δ ⊢ M ∈ x0 >$) by exact (weakeningV _ _ _ _ _ H4 H2).
  assert ($< (s0; t V:: Γ) - Δ ⊢ V{ x → s} M ∈ x0 >$) by exact (IHM _ _ H H1 _ H5).
  assert ($< Γ - Δ ⊢ λ s0 : t, V{ x → s} M ∈ (t → x0) >$) by exact (typ_rel_arr_i _ _ _ _ _ _ H6).
  unfold sub_trm.
  destruct (eqb_neq x s0).
  rewrite (H9 n).
  fold sub_trm.
  rewrite <- H3 in H7.
  assumption.

  (* ABSTRACTION ON TYPES *)
  destruct (itr_absT _ _ _ _ _ H0);destruct H2.
  assert (BV $< n T:: Δ >$ σ) by exact (BV_cons_updateT _ n _ H).
  assert ($< Δ T⊆ n T:: Δ >$) by exact (cons_includedinT Δ n).
  assert ($< nilV - n T:: Δ ⊢ s ∈ σ >$) by exact (weakeningT _ _ _ _ _ H5 H1).
  assert ($< Γ - n T:: Δ ⊢ V{ x → s} M ∈ x0 >$) by exact (IHM _ _ H4 H6 _ H2).
  assert ($< Γ - Δ ⊢ Λ n, V{ x → s} M ∈ (∀ n, x0) >$) by exact (typ_rel_all_i _ _ _ _ _ H7).
  rewrite H3;simpl;assumption.

  (*TERMS APPLICATION *)
  destruct (itr_appV _ _ _ _ _ H0);destruct H2;destruct H2;destruct H3.
  assert ($< Γ - Δ ⊢ V{ x → s} M1 ∈ (x0 → x1) >$) by exact (IHM1 _ _ H H1 _ H2).
  assert ($< Γ - Δ ⊢ V{ x → s} M2 ∈ x0 >$) by exact (IHM2 _ _ H H1 _ H3).
  simpl; rewrite H4.
  exact (typ_rel_arr_e _ _ _ _ _ _ H5 H6).

  (*TYPE APPLICATION *)
  destruct (itr_appT _ _ _ _ _ H0); destruct H2;destruct H2.
  assert ($< Γ - Δ ⊢ V{ x → s} M ∈ (∀ x0, x1) >$) by exact (IHM _ _ H H1 _ H2).
  rewrite H3;simpl.
  exact (typ_rel_all_e _ _ _ _ _ t H4).

  (* TRUE *)
  simpl.
  rewrite (itr_true _ _ _ H0).
  eauto using typ_rel.

  (* FALSE *)
  simpl.
  rewrite (itr_false _ _ _ H0).
  eauto using typ_rel.

  (* IF THEN ELSE *)
  destruct (itr_ite _ _ _ _ _ _ H0);destruct H3.
  assert ($< Γ - Δ ⊢ V{ x → s} M1 ∈ Bool >$) by exact (IHM1 _ _ H H1 _ H2).
  assert ($< Γ - Δ ⊢ V{ x → s} M2 ∈ δ >$) by exact (IHM2 _ _ H H1 _ H3).
  assert ($< Γ - Δ ⊢ V{ x → s} M3 ∈ δ >$) by exact (IHM3 _ _ H H1 _ H4).
  simpl.
  exact (typ_rel_if _ _ _ _ _ _ H5 H6 H7).

  (* ZERO *)
  simpl.
  rewrite (itr_zero _ _ _ H0).
  eauto using typ_rel.

  (* SUCCESSOR *)
  destruct (itr_succ _ _ _ _ H0).
  assert ($< Γ - Δ ⊢ V{ x → s} M ∈ Nat >$) by exact (IHM _ _ H H1 _ H2).
  simpl;rewrite H3.
  exact (typ_rel_succ _ _ _ H4).

  (* PREDECESSOR *)
  destruct (itr_pred _ _ _ _ H0).
  assert ($< Γ - Δ ⊢ V{ x → s} M ∈ Nat >$) by exact (IHM _ _ H H1 _ H2).
  simpl;rewrite H3.
  exact (typ_rel_pred _ _ _ H4).

  (* ZERO PREDICATE *)
  destruct (itr_iszero _ _ _ _ H0).
  assert ($< Γ - Δ ⊢ V{ x → s} M ∈ Nat >$) by exact (IHM _ _ H H1 _ H2).
  simpl;rewrite H3.
  exact (typ_rel_iszero _ _ _ H4).
Qed.

(*============================================================================
*******************SUBSTITUTION LEMMA FOR TYPES ******************************
=============================================================================*)

Definition sub_ctxV (α:nat) (σ:typ) (Γ:ctxV) : ctxV := fun x =>
  match Γ x with
  | None => None
  | Some δ => Some $<TT{α → σ}δ>$  
  end.

Notation "'CTT{' α '→' σ } Γ" := (sub_ctxV α σ Γ) (in custom sys_f at level 20, α at level 0, σ at level 0).

Compute ($<CTT{1 → Nat}( "y" ; (Bool → 1) V:: "x" ;  1 V:: nilV) >$ "y").










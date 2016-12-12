Require Import Coq.Lists.List.
Require Import ExtLib.Data.Member.

Section with_univ.
  Variable T' : Set.
  Inductive T : Set :=
  | Arr : T -> T -> T
  | Prod : T -> T -> T
  | Inj : T' -> T
  | Unit.

  Inductive CMor : T -> T -> Set :=
  | MId : forall {t}, CMor t t
  | MCompose : forall {a b c}, CMor b c -> CMor a b -> CMor a c
    (* Cartesian *)
  | MFst : forall {a b}, CMor (Prod a b) a
  | MSnd : forall {a b}, CMor (Prod a b) b
  | MFork : forall {a b c}, CMor a b -> CMor a c -> CMor a (Prod b c)
    (* Closed *)
  | MCurry : forall {a b c}, CMor (Prod a b) c -> CMor a (Arr b c)
  | MUncurry : forall {a b c}, CMor a (Arr b c) -> CMor (Prod a b) c
  | MApply : forall {a b}, CMor (Prod (Arr a b) a) b.

  Inductive CMor_eq : forall {d c}, CMor d c -> CMor d c -> Prop :=
  | LUnit : forall {a b} {c : CMor a b}, CMor_eq (MCompose MId c) c
  | RUnit : forall {a b} {c : CMor a b}, CMor_eq (MCompose c MId) c
  | CAssoc : forall {a b c d} (f : CMor a b) (g : CMor b c) (h : CMor c d),
      CMor_eq (MCompose h (MCompose g f)) (MCompose (MCompose h g) f)
    (* Cartesian *)
  | Fst_Fork : forall a b c l r, CMor_eq (MCompose MFst (@MFork a b c l r)) l
  | Snd_Fork : forall a b c l r, CMor_eq (MCompose MSnd (@MFork a b c l r)) r
    (* Closed *)
  | Curry_Uncurry : forall {a b c} (x : CMor a (Arr b c)), CMor_eq (MCurry (MUncurry x)) x
  | Uncurry_Curry : forall {a b c} (x : CMor (Prod a b) c), CMor_eq (MUncurry (MCurry x)) x
  | Curry_Apply   : forall {a b}, CMor_eq (MCurry (@MApply a b)) MId
  (* Refl and Trans *)
  | Refl_CMor_eq : forall {a b} (x : CMor a b), CMor_eq x x
  | Sym_CMor_eq : forall {a b} (x y : CMor a b), CMor_eq x y -> CMor_eq y x
  | Trans_CMor_eq : forall {a b} (x y z : CMor a b), CMor_eq x y -> CMor_eq y z -> CMor_eq x z.


(*
  Definition optCompose {a b c} (g : CMor b c) : CMor a b -> CMor a c.
  refine
    match g in CMor b c return CMor a b -> CMor a c with
    | MId => fun x => x
    | MFst => fun x => match x in CMor a b return CMor a b -> CMor a c with
                   | MFork l _ => _
                   | _ => _
                   end
    | x => MCompose x
    end.

  Fixpoint optCat {t t'} (m : CMor t t') : CMor t t'.
  refine
    match m in CMor t t' return CMor t t' with
    | MId => MId
    | MCompose g f => _
    | MFst => MFst
    | MSnd => MSnd
    | MFork l r => _
    end.
*)

  Inductive Expr (g : list T) : T -> Set :=
  | EApp : forall t t', Expr g (Arr t t') -> Expr g t -> Expr g t'
  | EAbs : forall t t', Expr (t :: g) t' -> Expr g (Arr t t')
  | EVar : forall t, member t g -> Expr g t
    (* Cartesian *)
  | EFst : forall a b, Expr g (Arr (Prod a b) a)
  | ESnd : forall a b, Expr g (Arr (Prod a b) b)
  | EPair : forall a b, Expr g (Arr a (Arr b (Prod a b))).

  Arguments EVar {_ _} _.
  Arguments EAbs {_ _ _} _.
  Arguments EApp {_ _ _} _ _.
  Arguments EFst {_ _ _}.
  Arguments ESnd {_ _ _}.
  Arguments EPair {_ _ _}.

  Arguments MZ {_ _ _}.
  Arguments MN {_ _ _ _} _.

  Inductive Expr' : T -> T -> Set :=
  | EApp' : forall {g t t'}, Expr' g (Arr t t') -> Expr' g t -> Expr' g t'
  | EAbs' : forall {g t t'}, Expr' (Prod t g) t' -> Expr' g (Arr t t')
  | ELiftL' : forall {a b c}, Expr' a c -> Expr' (Prod a b) c
  | ELiftR' : forall {a b c}, Expr' b c -> Expr' (Prod a b) c
  | EHere'  : forall {a}, Expr' a a
  | EFst' : forall {g a b}, Expr' g (Arr (Prod a b) a)
  | ESnd' : forall {g a b}, Expr' g (Arr (Prod a b) b)
  | EPair' : forall {g a b}, Expr' g (Arr a (Arr b (Prod a b))).

  Fixpoint expr'2cat {a b} (e : Expr' a b) : CMor a b :=
    match e in (Expr' t t0) return (CMor t t0) with
    | EApp' e1 e2 => MCompose MApply (MFork (expr'2cat e1) (expr'2cat e2))
    | EAbs' e0 => MCurry (MCompose (expr'2cat e0) (MFork MSnd MFst))
    | ELiftL' e0 => MCompose (expr'2cat e0) MFst
    | ELiftR' e0 => MCompose (expr'2cat e0) MSnd
    | EHere' => MId
    | EFst' => MCurry (MCompose MFst MSnd)
    | ESnd' => MCurry (MCompose MSnd MSnd)
    | EPair' => MCurry (MCurry (MFork (MCompose MSnd MFst) MSnd))
    end.

  Definition Epair' {g a b} (e1 : Expr' g a) (e2 : Expr' g b) : Expr' g (Prod a b) :=
    EApp' (EApp' EPair' e1) e2.

  Fixpoint expr'subst {a b c} (s : Expr' c a) (e : Expr' a b) {struct e} : Expr' c b :=
    match e in (Expr' t t0) return (Expr' c t -> Expr' c t0) with
   | @EApp' g t t' e1 e2 =>
       fun s0 : Expr' c g => EApp' (expr'subst s0 e1) (expr'subst s0 e2)
   | @EAbs' g t t' e0 =>
       fun s0 : Expr' c g =>
       EAbs'
         (expr'subst
            (EApp'
               (EApp' (EAbs' (EAbs' (ELiftR' (ELiftR' (Epair' (ELiftL' EHere') (ELiftR' s0))))))
                  (ELiftR' s0)) (ELiftL' EHere')) e0)
   | @ELiftL' a0 b0 c0 e0 => fun s0 : Expr' c (Prod a0 b0) => expr'subst (EApp' EFst' s0) e0
   | @ELiftR' a0 b0 c0 e0 => fun s0 : Expr' c (Prod a0 b0) => expr'subst (EApp' ESnd' s0) e0
   | @EHere' a0 => fun s0 : Expr' c a0 => s0
   | @EFst' g a0 b0 => fun _ : Expr' c g => EFst'
   | @ESnd' g a0 b0 => fun _ : Expr' c g => ESnd'
   | @EPair' g a0 b0 => fun _ : Expr' c g => EPair'
   end s.

  Fixpoint cat2expr' {a b} (m : CMor a b) : Expr' a b :=
    match m in (CMor t t0) return (Expr' t t0) with
    | @MId t => EHere'
    | @MCompose a0 b0 c m1 m2 => expr'subst (cat2expr' m2) (cat2expr' m1)
    | @MFst a0 b0 => ELiftL' EHere'
    | @MSnd a0 b0 => ELiftR' EHere'
    | @MFork a0 b0 c m1 m2 => EApp' (EApp' EPair' (cat2expr' m1)) (cat2expr' m2)
    | @MCurry a0 b0 c m0 =>
      EAbs' (expr'subst (Epair' (ELiftR' EHere') (ELiftL' EHere')) (cat2expr' m0))
    | @MUncurry a0 b0 c m0 =>
      EApp' (expr'subst (ELiftL' EHere') (cat2expr' m0)) (ELiftR' EHere')
    | @MApply a0 b0 => EApp' (ELiftL' EHere') (ELiftR' EHere')
    end.

  Theorem cat2expr'_expr'2cat : forall a b (e : Expr' a b),
      cat2expr' (expr'2cat e) = e.
  Proof.
    (** Only true in the equational theory of Expr'. **)
  Admitted.

  Instance Reflexive_CMor_eq {a b} : Reflexive (@CMor_eq a b).
  constructor.
  Defined.

  Instance Symmetric_CMor_eq {a b} : Symmetric (@CMor_eq a b).
  constructor; auto.
  Defined.

  Instance Transtive_CMor_eq {a b} : Transitive (@CMor_eq a b).
  red. intros; eapply Trans_CMor_eq; eauto.
  Defined.

  Theorem expr'2cat_cat2expr' : forall a b (e : CMor a b),
      CMor_eq (expr'2cat (cat2expr' e)) e.
  Proof.
  Admitted.

  Section with_t.
    Context {t : T}.
    Fixpoint member_weaken ls' {ls}
    : member t ls -> member t (ls' ++ ls) :=
      match ls' as ls'
            return member t ls -> member t (ls' ++ ls)
      with
      | nil => fun x => x
      | l :: ls' => fun x => MN (member_weaken ls' x)
      end.

    Fixpoint member_lift ls ls' ls''
      : member t (ls'' ++ ls) -> member t (ls'' ++ ls' ++ ls) :=
      match ls'' as ls''
            return member t (ls'' ++ ls) -> member t (ls'' ++ ls' ++ ls)
      with
      | nil => member_weaken ls'
      | l :: ls'' => fun m =>
                       match m in member _ (x :: xs)
                             return forall xs', (member t xs -> member t xs') ->
                                                member t (x :: xs')
                       with
                       | MZ => fun _ _ => MZ
                       | MN m => fun _ rec => MN (rec m)
                       end _ (member_lift  ls ls' ls'')
      end.
  End with_t.


  Section del_member.
    Context {T : Type}.
    Context {t : T}.

    Fixpoint del_member {ls} (m : member t ls) : list T :=
      match m with
      | @MZ _ _ ls => ls
      | @MN _ _ l _ m' => l :: del_member m'
      end.

  End del_member.

  Section member_heq.
    Context {T : Type}.
    Fixpoint member_heq {l r : T} {ls} (m : member l ls)
    : member r ls -> member r (del_member m) + (l = r).
    refine
      match m as m in member _ ls
            return member r ls -> member r (del_member m) + (l = r)
      with
      | @MZ _ _ ls => fun b : member r (l :: ls) =>
                       match b in member _ (z :: ls)
                             return l = z -> member r (del_member (@MZ _ _ ls)) + (l = r)
                       with
                       | MZ => @inr _ _
                       | MN m' => fun pf => inl m'
                       end eq_refl
      | @MN _ _ l' ls' mx => fun b : member r (l' :: ls') =>
        match b in member _ (z :: ls)
              return (member _ ls -> member _ (del_member mx) + (_ = r)) ->
                     member r (del_member (@MN _ _ _ _ mx)) + (_ = r)
        with
        | MZ => fun _ => inl MZ
        | MN m' => fun f => match f m' with
                            | inl m => inl (MN m)
                            | inr pf => inr pf
                            end
        end (fun x => @member_heq _ _ _ mx x)
      end.
    Defined.

  End member_heq.

  Fixpoint lift {g} g' g'' {t} (e : Expr (g'' ++ g) t)
  : Expr (g'' ++ g' ++ g) t :=
    match e in Expr _ t return Expr (g'' ++ g' ++ g) t with
    | EApp f x => EApp (@lift g g' g'' _ f) (@lift g g' g'' _ x)
    | EAbs e' => EAbs (@lift g g' (_ :: g'') _ e')
    | EVar m => EVar (member_lift _ _ _ m)
    | EFst => EFst
    | ESnd => ESnd
    | EPair => EPair
    end.

  Fixpoint subst {t t'} {g} (m : member t' g) (w : Expr (del_member m) t') (e : Expr g t)
  : Expr (del_member m) t :=
    match e in Expr _ t return Expr (del_member m) t with
    | EApp f x => EApp (subst m w f) (subst m w x)
    | EAbs e => EAbs (subst (MN m) (lift (_::nil) nil w) e)
    | EVar v =>
      match member_heq m v with
      | inl v' => EVar v'
      | inr pf => match pf with
                 | eq_refl => w
                 end
      end
    | EFst => EFst
    | ESnd => ESnd
    | EPair => EPair
    end.

  Inductive Expr_eq : forall {g t}, Expr g t -> Expr g t -> Prop :=
  | Beta : forall {g t t'} (x : Expr (t :: g) t') y,
      Expr_eq (EApp (EAbs x) y) (subst MZ y x)
    (* Cartesian *)
  | Fst_Pair : forall {g t t'} x y, Expr_eq (EApp (@EFst g t t') (EApp (EApp EPair x) y)) x
  | Snd_Pair : forall {g t t'} x y, Expr_eq (EApp (@ESnd g t t') (EApp (EApp EPair x) y)) y.

  Fixpoint cat2expr {g} {t} (c : CMor g t) : Expr nil (Arr g t).
  refine
    (match c in CMor ts' t'
           return Expr nil (Arr ts' t') with
     | MId => EAbs (EVar MZ)
     | MCompose g f =>
       EAbs (EApp (lift (_ :: nil) nil (cat2expr _ _ g))
                  (EApp (lift (_ :: nil) nil (cat2expr _ _ f)) (EVar MZ)))
     | MFst => EFst
     | MSnd => ESnd
     | MFork l r =>
       EAbs (EApp
               (EApp EPair (EApp (lift (_::nil) nil (cat2expr _ _ l)) (EVar MZ)))
                     (EApp (lift (_::nil) nil (cat2expr _ _ r)) (EVar MZ)))
     | MCurry e =>
       EAbs (EAbs (EApp (lift (_::_::nil) nil (cat2expr _ _ e))
                        (EApp (EApp EPair (EVar (MN MZ))) (EVar MZ))))
     | MUncurry e =>
       EAbs (EApp (EApp (lift (_::nil) nil (cat2expr _ _ e)) (EApp EFst (EVar MZ)))
                  (EApp ESnd (EVar MZ)))
     | MApply =>
       EAbs (EApp (EApp EFst (EVar MZ)) (EApp ESnd (EVar MZ)))
     end).
  Defined.

  Fixpoint Prods (ts : list T) (l : T) : T :=
    match ts with
    | nil => l
    | t :: ts => Prod t (Prods ts l)
    end.

  Fixpoint var_to_mor {t} {g} (v : member t g) : CMor (Prods g Unit) t :=
    match v in member _ g return CMor (Prods g Unit) t with
    | MZ => MFst
    | MN v' => MCompose (var_to_mor v') MSnd
    end.

  Fixpoint expr2cat {g} {t} (e : Expr g t) : CMor (Prods g Unit) t :=
    match e in (Expr _ t0) return (CMor (Prods g Unit) t0) with
    | EApp f x => MCompose MApply (MFork (expr2cat f) (expr2cat x))
    | EAbs e0 => MCurry (MCompose (expr2cat e0) (MFork MSnd MFst))
    | EVar v => var_to_mor v
    | EFst => MCurry (MCompose MFst MSnd)
    | ESnd => MCurry (MCompose MSnd MSnd)
    | EPair => MCurry (MCurry (MFork (MCompose MSnd MFst) MSnd))
    end.

  Fixpoint cat2expr' {t g} (m : CMor g t) : Expr (g :: nil) t.
    destruct m.
    { apply EVar. eapply MZ. }
    { eapply EApp.
      eapply (lift (_::nil) nil (EAbs (cat2expr' _ _ m1))).
      eapply cat2expr'. assumption. }
    { eapply EApp. eapply EFst. eapply (EVar MZ). }
    { eapply EApp. eapply ESnd. eapply (EVar MZ). }
    { eapply EApp. eapply EApp. eapply EPair.
      eapply cat2expr'; assumption.
      eapply cat2expr'; assumption. }
    { eapply EAbs.
      refine (EApp (lift (b::a::nil) nil (EAbs (cat2expr' _ _ m))) _); clear. simpl.
      refine (EApp (EApp EPair (EVar (MN MZ))) (EVar MZ)). }
    { refine (EApp (EApp (lift (_::nil) nil (EAbs (cat2expr' _ _ m))) (EApp EFst (EVar MZ))) (EApp ESnd (EVar MZ))). }
    { eapply EApp.
      eapply (EApp EFst (EVar MZ)).
      eapply (EApp ESnd (EVar MZ)). }
  Defined.


  Definition fixup {a b} (m : Expr (a :: nil) b) : Expr (Prod a Unit :: nil) b.
    eapply EApp. eapply (lift (_::nil) nil (EAbs m)).
    refine (EApp EFst (EVar MZ)).
  Defined.

  Theorem cat2expr_expr2cat : forall a b (m : Expr (a :: nil) b),
      Expr_eq (cat2expr' (expr2cat m)) (fixup m).
  Proof.
    induction m.
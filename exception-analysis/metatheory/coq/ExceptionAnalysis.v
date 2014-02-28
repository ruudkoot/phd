(* About the proofs in this file:
   + the file contains partial but pretty complete mechanized proofs of 
     Progress and Preservation for our annotated type system for 
     our paper entitled Type-based Exception Analysis for Non-strict Higher-order 
     Functional Languages with Imprecise Exception Semantics.
   + we have made a few simplificiations so that we do not quite attain
     the strength of the proofs of Progress and Preservation:
     1. T-Sub, T-Gen and T-Inst are not in the annotated type system proper, since
        they are not needed there. However, they are needed in the
        proof of Preservation. This is why we have posed them as 
        Theorems and just admitted them. The rules would normally be justified
        by the soundness of a non-syntax-directed version of our type system.
     2. The cases for E-Bind1 and E-Bind2 are not proven for Preservation,
        because we found out during that process that doing so would
        involve reformulating the whole syntactic structure of types,
        type schemes and the like. We did not have the time to attempt
        these refactorings, and decided to just not prove these cases
        for now. Fortunately these cases are relatively small (on paper).
     3. Because we do not have an underlying type system, some inversions
        in the proof of Progress give a large number of possible
        cases that we can be sure cannot occur (these can be recognized
        by the large numbers of AdmitByCanonicalForms). 
        An example is when you invert the structure of a value in 
        the position of a function. In that case, you can be sure the
        value is not true, false, int or nil, but it can be a close
        of a lambda abstraction, or a crash. In all cases, the
        AdmitByCanonicalForms says in comments, which case is 
        discharged there.
        This issue could be resolved by defining the underlying type system, 
        but we have not yet done so.
     4. Some of our results involve reasoning within lattices, and
        we did not implement that as such. Fortunately all of these 
        are straightforward (reflexivity, transitivity, existence of bottom etc.).
     5. We needed Induction-Recursion to model consistency of our operator
        abstraction, but Coq does not support it. Therefore we have phrased
        this property as an axiom to be employed in our proof. Another such
        property (monotonicity) did not give us such issues, so we could
        include it in the type system.
     6. The cases for E-Fix and E-Let in Preservation are incomplete. The  
        reasons for this are explained below in their proofs.
        
   This file is supposed to follow the structure of the written proofs.
   Slight deviations from the numbering of hypotheses in the written submitted
   proofs can occur, because some of the mechanized proofs were made based on 
   a paper version of which some cases where still subject to change (and this may
   change the numbering of hypotheses also in other cases)..

   In total, 32 of the 36 cases for Preservation have been proven. All cases
   for Progress are proven, with caveat 3. 
*)

Require Export SfLib.
Require Export ZArith.
Require Import LibTactics.

Hypothesis eq_dec : forall (A : Type) (x : A) (y : A), {x = y}+{x <> y}.

Fixpoint eltof (A : Type) (x : A) (l : list A) : bool :=
  match l with 
    | [] => false
    | y :: l' => if (eq_dec A x y) then true else eltof A x l'
  end.

Fixpoint intersect (A : Type) (l1 : list A) (l2 : list A) : list A :=
  match l1 with
    | [] => []
    | y::rest => if (eltof A y l2) then y :: intersect A rest l2 else intersect A rest l2
  end.

Fixpoint difference (A : Type) (l1 : list A) (l2 : list A) : list A :=
  match l1 with
    | [] => []
    | y::rest => if (eltof A y l2) then difference A rest l2 else y :: intersect A rest l2
  end.
  
(**** Locations, analogous to id/Id ****)

Inductive loc : Type :=
  Loc : nat -> loc.

Definition beq_loc l1 l2 :=
  match (l1, l2) with
    (Loc n1, Loc n2) => beq_nat n1 n2
  end.

Theorem beq_loc_refl : forall l,
  true = beq_loc l l.
Proof.
  intros. destruct l.
  apply beq_nat_refl.  Qed.

Theorem beq_loc_eq : forall l1 l2,
  true = beq_loc l1 l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  destruct l1. destruct l2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_loc_false_not_eq : forall l1 l2,
  beq_loc l1 l2 = false -> l1 <> l2.
Proof.
  intros l1 l2 H.
  destruct l1. destruct l2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  
Qed.

Theorem not_eq_beq_loc_false : forall l1 l2,
  l1 <> l2 -> beq_loc l1 l2 = false.
Proof.
  intros l1 l2 H.
  destruct l1. destruct l2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  
Qed.

Theorem beq_loc_sym: forall l1 l2,
  beq_loc l1 l2 = beq_loc l2 l1.
Proof.
  intros l1 l2. destruct l1. destruct l2. apply beq_nat_sym. 
Qed.

(* Types *)
Inductive ty : Type := 
  | TBool  : ty
  | TNum   : ty 
  | TArrow : ty -> ty -> ty
  | TVar   : ty
  | TPair  : ty -> ty -> ty
  | TList  : ty -> ty.

Inductive opT : Type := op.

Inductive opTp : Type := 
  | add : opTp
  | mul : opTp
  (* Add your own here *)
  .

(* The expression language and expression environments *) 
Inductive rho : Type :=
  | rnil  : rho
  | rcons : rho -> id -> exp -> rho

with 

exp : Type :=
  | evar : id -> exp
  | efalse : list loc -> exp
  | etrue : list loc -> exp
  | eint : list loc -> Z -> exp 
  | ecrash : list loc -> exp
  | enil : list loc -> exp
  | eclose : list loc -> exp -> rho -> exp
  | eabs : id -> exp -> exp
  | efix : id -> exp -> exp
  | eapp : exp -> exp -> exp
  | elet : id -> exp -> exp -> exp
  | eif : exp -> exp -> exp -> exp
  | eop : exp -> opTp -> exp -> exp
  | epair : exp -> exp -> exp
  | efst : exp -> exp
  | esnd : exp -> exp
  | econs : exp -> exp -> exp
  | ecase : exp -> exp -> id -> id -> exp -> exp
  | ebind : rho -> exp -> exp.

Tactic Notation "e_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "evar"   | Case_aux c "efalse" 
  | Case_aux c "etrue"  | Case_aux c "eint" 
  | Case_aux c "ecrash" | Case_aux c "enil" 
  | Case_aux c "eclose" | Case_aux c "eabs"
  | Case_aux c "efix" 
  | Case_aux c "eapp"   | Case_aux c "elet" 
  | Case_aux c "eif"    | Case_aux c "eop" 
  | Case_aux c "epair"  | Case_aux c "efst" 
  | Case_aux c "esnd"   | Case_aux c "econs" 
  | Case_aux c "tcase"  | Case_aux c "ebind" ].

Inductive value : exp -> Prop :=
  | vint   : forall ls n,
      value (eint ls n)
  | vcrash : forall ls,
      value (ecrash ls)
  | vtrue  : forall ls, value (etrue ls)
  | vfalse : forall ls, value (efalse ls)
  | vnil   : forall ls, value (enil ls)
  | vclose : forall ls e r,
      value (eclose ls e r).

(* Given the ``name'' of an operator, interpret it on its arguments and return 
   the result. If you add a div operator, you can return a division by zero 
   exception in the result. *)
Definition interpret (anop : opTp) (n1 : Z) (n2 : Z) : exp :=
  match anop with
   | add => eint nil (n1 + n2)
   | mul => eint nil (n1 * n2)
  end.

(* Exception carry the location of where they occurred. For the other values,
   you can expect the locations to be nil. *)
Definition locs (e:exp) : list loc := 
  match e with
    | eint ls n     => ls
    | ecrash ls     => ls
    | etrue ls      => ls
    | efalse ls     => ls
    | enil ls       => ls
    | eclose ls e r => ls
    | _ => nil
  end.  
  
Hint Constructors value.

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Definition l1 := (Loc 0).
Definition l2 := (Loc 1).
Definition l3 := (Loc 2).
Hint Unfold l1.
Hint Unfold l2.
Hint Unfold l3.

(* Functions for manipulating rho's *)
Definition rhd (default:exp) (l:rho) : exp :=
  match l with
  | rnil => default
  | rcons rho' v e => e
  end.

Definition rtail (l:rho) : rho :=
  match l with
  | rnil => rnil
  | rcons rho' v e => rho'
  end.

Definition e1 := (eint nil 1).
Definition e2 := (eint nil 2).
Definition e3 := (eint nil 3).
Definition e4 := (eint nil 4).
Definition e5 := (eint nil 5).

Fixpoint rcombine (r1:rho) (r2:rho) : rho :=
  match r1 with
   | rnil => r2
   | rcons r1' v e => rcombine r1' (rcons r2 v e)
  end.

Fixpoint lookup (r:rho) (v:id) (ac:rho) : option (exp * rho) := 
  match r with
   | rnil => None
   | rcons rho' v' e' => 
        if (beq_id v v') then Some (e', rcombine ac rho') 
                         else lookup rho' v (rcons ac v' e')
  end. 

Theorem lookuplast : forall rho rho' v' e e',
  lookup (rcons rho' v' e') v' rnil = Some (e, rho) ->
  e = e' /\ rho = rho'.  
Proof.
  intros.
  unfold lookup in H.
  rewrite <- beq_id_refl in H.
  unfold rcombine in H.
  inversion H...
  split...
  reflexivity.
  reflexivity.
Qed.

(* Unit test: *)
Definition rhoex := 
  rcons (rcons (rcons (rcons (rcons rnil z e5) y e4) x e3) z e2) y e1.

Eval simpl in (lookup rhoex x rnil).
 

Reserved Notation "rho '|--' e '\-->' e' " (at level 80). 

(* The small step semantics *)
Inductive step : rho -> exp -> exp -> Prop := 
  | E_Var : forall rho rho' x e, 
              lookup rho x rnil = Some (e, rho') -> 
              rho |-- evar x \--> ebind rho' e
  | E_Abs : forall rho x e ls, 
              rho |-- eabs x e \--> 
                      eclose ls (eabs x e) rho
  | E_Fix : forall rho f e, 
              rho |-- efix f e \-->  
                      ebind (rcons rho f (ebind rho (efix f e))) e
  | E_App : forall rho e1 e1' e2, 
              rho |-- e1 \--> e1'   -> 
              rho |-- eapp e1 e2 \--> eapp e1' e2
  | E_AppAbs : forall rho x e1 rho1 e2 ls, 
              rho |-- eapp (eclose ls (eabs x e1) rho1) e2 \-->  
                      ebind (rcons rho1 x (ebind rho e2)) e1 
  | E_AppExn1 : forall rho e2 e2' ls1, 
              rho |-- e2 \--> e2' -> 
              rho |-- eapp (ecrash ls1) e2 \--> 
                      eapp (ecrash ls1) e2'
  | E_AppExn2 : forall rho ls1 ls2 v2,  (* Is this the right way of doing it? *)
              (value v2) /\ ls2 = locs(v2) -> 
              rho |-- eapp (ecrash ls1) v2 \-->  
                      ecrash (ls1 ++ ls2)
  | E_Let: forall rho x e1 e2, 
              rho |-- elet x e1 e2 \--> 
              ebind (rcons rho x (ebind rho e1)) e2
  | E_If : forall rho e1 e1' e2 e3, 
              rho |-- e1 \--> e1' -> 
              rho |-- eif e1 e2 e3 \--> eif e1' e2 e3
  | E_IfTrue: forall rho ls e2 e3, 
              rho |-- eif (etrue ls) e2 e3 \--> e2
  | E_IfFalse: forall rho ls e2 e3, 
              rho |-- eif (efalse ls) e2 e3 \--> e3
  | E_IfExn1: forall rho ls1 e2 e2' e3, 
              rho |-- e2 \--> e2' -> 
              rho |-- eif (ecrash ls1) e2 e3 \--> 
                      eif (ecrash ls1) e2' e3
  | E_IfExn2: forall rho ls1 e2 e3 e3', 
              rho |-- e3 \--> e3' -> 
              rho |-- eif (ecrash ls1) e2 e3 \--> eif (ecrash ls1) e2 e3'
  | E_IfExn3: forall rho ls1 v2 ls2 v3 ls3, 
              value v2 /\ value v3 /\ ls2 = locs(v2) /\ ls3 = locs(v3) ->
              rho |-- eif (ecrash ls1) v2 v3 \-->  
                      ecrash (ls1 ++ ls2 ++ ls3)
  | E_Op1: forall rho e1 op e2 e1', 
              rho |-- e1 \--> e1' -> 
              rho |-- eop e1 op e2 \--> eop e1' op e2
  | E_Op2: forall rho e1 op e2 e2', 
              rho |-- e2 \--> e2' -> 
              rho |-- eop e1 op e2 \--> eop e1 op e2'
  | E_OpNum: forall rho n1 op n2 ls1 ls2, 
              rho |-- eop (eint ls1 n1) op (eint ls2 n2) \-->  
                      interpret op n1 n2
  | E_OpExn1: forall rho ls1 op n2, 
              rho |-- eop (ecrash ls1) op n2 \--> ecrash ls1
  | E_OpExn2: forall rho n1 op ls2, 
              rho |-- eop n1 op (ecrash ls2) \--> ecrash ls2
  | E_OpExn3: forall rho ls1 op ls2, 
              rho |-- eop (ecrash ls1) op (ecrash ls2) \-->  
                      ecrash (ls1 ++ ls2)
  | E_Pair: forall rho e1 e2 ls, 
              rho |-- epair e1 e2 \--> 
                      eclose ls (epair e1 e2) rho
  | E_Cons: forall rho e1 e2 ls, 
              rho |-- econs e1 e2 \--> 
                      eclose ls (econs e1 e2) rho 
  | E_Fst: forall rho e e', 
              rho |-- e \--> e' -> 
              rho |-- efst e \--> efst e' 
  | E_FstPair: forall rho ls e1 e2 rho', 
              rho |-- efst (eclose ls (epair e1 e2) rho') \--> 
                      ebind rho' e1
  | E_FstExn: forall rho ls, 
              rho |-- efst (ecrash ls) \--> ecrash ls
  | E_Snd: forall rho e e', 
              rho |-- e \--> e' -> 
              rho |-- esnd e \--> esnd e' 
  | E_SndPair: forall rho ls e1 e2 rho', 
              rho |-- esnd (eclose ls (epair e1 e2) rho') \--> 
                      ebind rho' e2 
  | E_SndExn: forall rho ls, 
              rho |-- esnd (ecrash ls) \--> ecrash ls
  | E_Case: forall rho e1 e2 x1 x2 e3 e1', 
              rho |-- e1 \--> e1' ->
              rho |-- ecase e1 e2 x1 x2 e3 \--> 
                      ecase e1' e2 x1 x2 e3
  | E_CaseNil: forall rho ls e2 x1 x2 e3, 
              rho |-- ecase (enil ls) e2 x1 x2 e3 \--> 
                      e2  
  | E_CaseCons: forall rho ls1 rho1 e1 e2 x1 x2 e3 e1',
              rho |-- ecase (eclose ls1 (econs e1 e1') rho1) e2 x1 x2 e3 \-->  
                      ebind (rcons (rcons rho x1 (ebind rho1 e1)) x2 (ebind rho1 e1')) e3
  | E_CaseExn1: forall rho ls1 e2 x1 x2 e3 e2', 
              rho |-- e2 \--> e2' ->
              rho |-- ecase (ecrash ls1) e2 x1 x2 e3 \-->  
                      ecase (ecrash ls1) e2' x1 x2 e3
  | E_CaseExn2: forall rho ls1 e2 x1 x2 e3 e3', 
              (rcons (rcons rho x1 (ecrash nil)) x2 (ecrash nil)) |-- e3 \--> e3' ->
              rho |-- ecase (ecrash ls1) e2 x1 x2 e3 \--> 
                      ecase (ecrash ls1) e2 x1 x2 e3'
  | E_CaseExn3: forall rho ls1 v2 ls2 v3 ls3 x1 x2, 
              value v2 /\ value v3 /\ ls2 = locs(v2) /\ ls3 = locs(v3) ->
              rho |-- ecase (ecrash ls1) v2 x1 x2 v3 \-->  
                      ecrash (ls1 ++ ls2 ++ ls3)
  | E_Bind1: forall rho rho1 e1 e1', 
              rho1 |-- e1 \--> e1' -> 
              rho  |-- ebind rho1 e1 \--> 
                       ebind rho1 e1'
  | E_Bind2: forall rho rho1 v1, 
              value v1 -> 
              rho |-- ebind rho1 v1 \--> v1 
where "rho '|--' e '\-->' e' " := (step rho e e').


(* Annotation variables, again analogous to variables and locations *)

Inductive avar : Type :=
  Avar : nat -> avar.

Definition beq_avar a1 a2 :=
  match (a1, a2) with
    (Avar n1, Avar n2) => beq_nat n1 n2
  end.

Inductive iota : Type := Data | Exn.

(* The tau as defined in the paper *)
Inductive sh : Type :=
  | Annvar  : avar -> sh
  | ArrowT  : sh -> avar -> sh -> sh
  | ProdT   : sh -> avar -> sh -> sh
  | ListT   : sh -> avar -> sh.

(* The dataflow lattice, a rather minimal one at that. *)  
Inductive dflow : Type :=
  | Bot : dflow
  | T : dflow (* true *)
  | F : dflow  (* false *)
  | TF : dflow (* true or false *)
  | N : dflow (* empty list *)
  | C : dflow (* cons node *)
  | NC : dflow (* any list *)
  | I : dflow (* any integer *)
 (* | Top : dflow is not necessary because of type correctness *) 
  .

Definition dexp : Type := list loc.

(* Since we have two lattices, one for dataflow and one for exceptions,
   the paper uses an index to select the right one. *)
Definition latt (i : iota) : Type := 
  match i with 
    | Data => dflow 
    | Exn => dexp
  end.

Definition bottom (i : iota) : latt i :=
   match i with
     | Data => Bot
     | Exn => []
   end.

(* The constraint language *)   

Inductive guard: Type := 
  | Atomg: forall (i : iota), latt i -> avar -> guard
  | Exst : forall (i : iota), avar -> guard
  | Disj : guard -> guard -> guard
  | True : guard
  .

Inductive rhs : Type :=
  | Atomr: forall (i : iota), latt i -> avar -> rhs
  | B4   : forall (i : iota), avar -> avar -> rhs
  | Subtf: forall (i : iota), sh -> sh -> rhs
  .

Inductive c : Type :=
  | Implc : guard -> rhs -> c
  .

(* This this our equivalent of $c^g$ in the paper *)
Inductive anyc : Type :=
  | Guard : guard -> anyc
  | Full : c -> anyc
  .
  
Inductive shsch : Type :=
  | Scheme : list avar -> sh -> list anyc -> shsch
  .

Inductive env : Type :=
  | envnil  : env
  | envcons : env -> id -> shsch -> env
  .
      
Definition outer tau :=
  match tau with
    | Annvar av => av
    | ArrowT t1 av t2 => av
    | ProdT t1 av t2 => av
    | ListT t av => av
  end.  

(* Helper functions for constraints, type schemes and environments. *)

Definition lift (r : rhs) : c :=
  Implc True r.

Definition c2full (g : guard) (r : rhs) : anyc :=
  Full (Implc g r).

Definition r2full (r : rhs) : anyc :=
  c2full True r.
  
Definition omega (op : opTp) (alpha1 : avar) (alpha2 : avar) (alpha : avar) : list anyc :=
  match op with
  | add => [r2full (Atomr Data I alpha)]
  | mul => [r2full (Atomr Data I alpha)]
  end.

Fixpoint shfav (tau : sh) : list avar :=
  match tau with
    | Annvar alpha => [alpha]
    | ArrowT tau1 alpha tau2 => alpha :: (shfav tau1 ++ shfav tau2)
    | ProdT  tau1 alpha tau2 => alpha :: (shfav tau1 ++ shfav tau2)
    | ListT  tau alpha => alpha :: shfav tau
  end.

Fixpoint guardfav (g : guard) : list avar :=
  match g with
    | Atomg i lit v => [v]
    | Exst i v => [v] (* Note: Exst does not bind the variable! *)
    | Disj g1 g2 => guardfav g1 ++ guardfav g2
    | True => []
  end.

Definition rhsfav (r : rhs) : list avar :=
  match r with
    | Atomr i lit v => [v]
    | B4 i v1 v2 => [v1,v2]
    | Subtf i tau1 tau2 => shfav tau1 ++ shfav tau2
  end.

Definition cfav (ac : c) : list avar :=
  match ac with
    | Implc g r => guardfav g ++ rhsfav r
  end.

Definition anycfav (ac : anyc) : list avar :=
  match ac with
    | Guard g => guardfav g
    | Full ac' => cfav ac'
  end.

Fixpoint csetfav (cs : list anyc) : list avar :=
  match cs with 
    | [] => []
    | ac :: cs' => anycfav ac ++ csetfav cs'
  end.
 
Definition schfav (sigma : shsch) : list avar :=
  match sigma with
    | Scheme boundvars tau cs => difference avar (shfav tau ++ csetfav cs) boundvars  
  end.

Fixpoint efav (gamma : env) : list avar :=
  match gamma with
    | envnil  => []
    | envcons gamma' x sigma => efav gamma' ++ schfav sigma
  end.
  
(* Substitutions are restricted to renamings (we don't need more). *)
Definition subst := avar -> avar.

Fixpoint shsubst (s : subst) (tau : sh) : sh :=
  match tau with
    | Annvar alpha => Annvar (s alpha)
    | ArrowT tau1 alpha tau2 => ArrowT (shsubst s tau1) (s alpha) (shsubst s tau2)
    | ProdT  tau1 alpha tau2 => ProdT (shsubst s tau1) (s alpha) (shsubst s tau2)
    | ListT  tau alpha => ListT (shsubst s tau) (s alpha)
  end.

Fixpoint guardsubst (s : subst) (g : guard) : guard :=
  match g with
    | Atomg i lit v => Atomg i lit (s v)
    | Exst i v => Exst i (s v) (* Note: Exst does not bind the variable! *)
    | Disj g1 g2 => Disj (guardsubst s g1) (guardsubst s g2)
    | True => True
  end.

Definition rhssubst (s : subst) (r : rhs) : rhs :=
  match r with
    | Atomr i lit v => Atomr i lit (s v)
    | B4 i v1 v2 => B4 i (s v1) (s v2)
    | Subtf i tau1 tau2 => Subtf i (shsubst s tau1) (shsubst s tau2)
  end.

Definition csubst (s : subst) (ac : c) : c :=
  match ac with
    | Implc g r => Implc (guardsubst s g) (rhssubst s r)
  end.

Definition anycsubst (s : subst) (ac : anyc) : anyc :=
  match ac with
    | Guard g => Guard (guardsubst s g)
    | Full ac' => Full (csubst s ac')
  end.
 
Fixpoint cssubst (s : subst) (cs : list anyc) : list anyc :=
  match cs with
    | [] => []
    | ac :: cs' => anycsubst s ac :: cssubst s cs'
  end.    

Fixpoint lookupavar (v : avar) (v2vs : list (avar * avar)) : avar := 
  match v2vs with
    | [] => v (* If it ain't there, just return it *)
    | (v1,v2) :: v2vs' => if beq_avar v v1 then v2 else lookupavar v v2vs'
  end.

Definition list2Subst (alphabetas : list (avar * avar)) : subst := 
  fun v => lookupavar v alphabetas.

Definition renamesh (abs : list (avar * avar)) (tau : sh) : sh := 
  shsubst (list2Subst abs) tau
. 

Definition renamecs (abs : list (avar * avar)) (cs : list anyc) : list anyc := 
  cssubst (list2Subst abs) cs
.

(* Two obvious lemma's for use later. Proving this in Coq is, we expect, quite involved. *)
Theorem renameid4sh: forall alphas tau,
  renamesh (combine alphas alphas) tau = tau.
Admitted.

Theorem renameid4cs: forall alphas cs,
  renamecs (combine alphas alphas) cs = cs.
Admitted.

Reserved Notation "cs '||=' ac" (at level 75). (* Constraints *)

(* Constraint reasoning, syntax-directed rules. *)
Inductive baseEntails : list anyc -> anyc -> Prop :=
   | CL_SBase: forall cs i g alpha1 alpha2,
               cs ||= c2full g (B4 i alpha1 alpha2) ->
               cs ||= c2full g (Subtf i (Annvar alpha1) (Annvar alpha2))
   | CL_SFun: forall cs i g alpha1 alpha2 tau1 tau2 tau3 tau4,
               cs ||= c2full g (B4 i alpha1 alpha2) ->
               cs ||= c2full g (Subtf i tau3 tau1) ->
               cs ||= c2full g (Subtf i tau2 tau4) ->
               cs ||= c2full g (Subtf i (ArrowT tau1 alpha1 tau2) (ArrowT tau3 alpha2 tau4))
   | CL_SPair: forall cs i g alpha1 alpha2 tau1 tau2 tau3 tau4,
               cs ||= c2full g (B4 i alpha1 alpha2) -> 
               cs ||= c2full g (Subtf i tau1 tau3) ->
               cs ||= c2full g (Subtf i tau2 tau4) ->
               cs ||= c2full g (Subtf i (ProdT tau1 alpha1 tau2) (ProdT tau3 alpha2 tau4))
   | CL_SList: forall cs i g alpha1 alpha2 tau1 tau2,
               cs ||= c2full g (B4 i alpha1 alpha2) -> 
               cs ||= c2full g (Subtf i tau1 tau2) ->
               cs ||= c2full g (Subtf i (ListT tau1 alpha1) (ListT tau2 alpha2))
   | CL_OrI: forall cs g1 g2, 
               cs ||= Guard g1 -> cs ||= Guard (Disj g1 g2)
   | CL_ExI: forall cs alpha i (val : latt i),  
               cs ||= Guard (Atomg i val alpha) -> 
               cs ||= Guard (Exst i alpha)
   | CL_Botr: forall cs i alpha, 
               cs ||= r2full (Atomr i (bottom i) alpha)
   | CL_Botg: forall cs i alpha, 
               cs ||= Guard (Atomg i (bottom i) alpha)
where "cs '||=' ac" := (baseEntails cs ac).

(* The following Theorems all follow from Theorem 5 (Soundness of constraint 
   logic). See addendum to the paper. *)
 
Theorem CL_ImplE: forall g r cs,
  cs ||= c2full g r -> cs ++ [Guard g] ||= r2full r.
Admitted.
      
Theorem CL_ImplI: forall g r cs,
  cs ++ [Guard g] ||= r2full r -> cs ||= c2full g r.
Admitted.

Theorem CL_Weak: forall cs1 cs2 c, 
  cs1 ||= c -> cs1 ++ cs2 ||= c.
Admitted.

(* Also easy to have,and just as correct: *)
Theorem CL_Weak2: forall cs1 cs2 c, 
  cs2 ||= c -> cs1 ++ cs2 ||= c.
Admitted.

Theorem CL_MP: forall cs c1 c2, 
  cs ||= c1 /\ cs ++ [c1] ||= c2 ->  (* Is order an issue? *)
  cs ||= c2.
Admitted.

Theorem CL_OrC: forall cs g1 g2,
  cs ||= Guard (Disj g1 g2) -> cs ||= Guard (Disj g2 g1).
Admitted.

Theorem CL_CoerceRG: forall cs i elt alpha,
  cs ||= r2full (Atomr i elt alpha) ->
  cs ||= Guard (Atomg i elt alpha).
Admitted.

Theorem CL_CoerceGR: forall cs i elt alpha,
  cs ||= Guard (Atomg i elt alpha) ->
  cs ||= r2full (Atomr i elt alpha).
Admitted.

(* This theorem says that if two sets of exceptions are observed, then
   the union of the two is observed. We'd get this for free if we'd
   defined our abstract datatype as a lattice, with ++ being its join operator. *)
Theorem CL_B4_ExnConcat: forall cs val1 val2 alpha,
  cs ||= r2full (Atomr Exn val1 alpha) ->
  cs ||= r2full (Atomr Exn val2 alpha) ->
  cs ||= r2full (Atomr Exn (val1 ++ val2) alpha).
Admitted.

(* Again, because we have not imposed a lattice structure explicitly, we
   assume the following transitivity property for our lattice. *)
Theorem AtomB4_Trans: forall cs i alpha alpha' val1,
  cs ||= r2full (Atomr i val1 alpha) ->
  cs ||= r2full (B4 i alpha alpha') ->
  cs ||= r2full (Atomr i val1 alpha').
Admitted.

(* And again... *)
Theorem B4_Refl : forall cs i alpha,
  cs ||= Full (Implc True (B4 i alpha alpha)).
Admitted.

Theorem S_Refl : forall cs i tau,
  cs ||= Full (Implc True (Subtf i tau tau)).
Proof with eauto.
  intros.
  induction tau...
  apply CL_SBase.
  apply B4_Refl.
  apply CL_SFun...
  apply B4_Refl.
  apply CL_SPair...
  apply B4_Refl.
  apply CL_SList...
  apply B4_Refl.
Qed.


(* Follows, ultimately, from using lattices for our annotations. *)
Theorem S_Trans: forall cs g i tau1 tau2 tau3,  
  (* Using g everywhere is hopefully enough. *)
  cs ||= c2full g (Subtf i tau1 tau2) ->
  cs ||= c2full g (Subtf i tau2 tau3) ->
  cs ||= c2full g (Subtf i tau1 tau3).
Proof.
Admitted.


(* With S_Trans in place, this is not a big deal: *)
Theorem B4_Trans : forall cs i alpha1 alpha2 alpha3, 
  cs ||= r2full (B4 i alpha1 alpha2) ->
  cs ||= r2full (B4 i alpha2 alpha3) ->
  cs ||= r2full (B4 i alpha1 alpha3).
Proof.
  intros.
  apply CL_SBase in H.
  apply CL_SBase in H0.
  assert (Tmp: cs ||= c2full True (Subtf i (Annvar alpha1) (Annvar alpha3))).
  apply S_Trans with (tau2 := Annvar alpha2).
  assumption.
  assumption.
  inversion Tmp...
  assumption.
Qed.

(* Intuitively the following follows from all lists have a data 
   flow annotation on or under NC. This theorem is necessary for 
   E-CaseCons. Again, we feel the lack of underlying types here. *)
Theorem ListsUnderNC: forall cs tau' tau alpha beta,
  tau' = ListT tau alpha ->
  cs ||= r2full (Atomr Data NC beta) -> 
  cs ||= r2full (B4 Data alpha beta).
Admitted.

Definition trueAbs : dflow :=
  T.
Definition falseAbs : dflow :=
  F.
Definition intAbs : dflow := 
  I. 

(* Copied from somewhere else: *)
Inductive Forall {A} (P:A->Prop) : list A -> Prop :=
 | Forall_nil : Forall P nil
 | Forall_cons : forall x l, P x -> Forall P l -> Forall P (x::l).
Hint Constructors Forall.

(* Lift a tau into a sigma, essentially, without generalizing anything. *)
Definition mono (x : sh) : shsch :=
  Scheme nil x nil.

(* As in the paper: *)
Definition opmonotonic (op : opTp) : Prop :=
  forall alpha1 alpha2 alpha alpha1' alpha2' alpha' cs,
     Forall (baseEntails cs) (omega op alpha1 alpha2 alpha) ->
     cs ||= r2full (B4 Data alpha1' alpha1) ->
     cs ||= r2full (B4 Exn alpha1' alpha1) ->
     cs ||= r2full (B4 Data alpha2' alpha2) ->
     cs ||= r2full (B4 Exn alpha2' alpha2) ->
     cs ||= r2full (B4 Data alpha alpha') ->
     cs ||= r2full (B4 Exn alpha alpha') ->
     Forall (baseEntails cs) (omega op alpha1' alpha2' alpha').

Reserved Notation "cs1 ';' env1 '|-' exp1 ';;' tau1" (at level 80). 
(* Note the ;; instead of :, to : Coq reacted allergically. *)

(* Consistency of environments, and the annotated type system: *)
Inductive consistent : list anyc -> env -> rho -> Prop :=
  (* Figure 13 *)
  | EC_Empty: forall cs, consistent cs envnil rnil  
  | EC_Extend: forall cs gamma x rho e sigma,
             consistent cs gamma rho /\
             cs; gamma |- e ;; sigma ->
             consistent cs (envcons gamma x sigma) (rcons rho x e) 

with

          hastype : list anyc -> env -> exp -> shsch -> Prop :=
  | T_Var: forall cs ds gamma alphas betas x tau,
             length alphas = length betas ->
             Forall (baseEntails cs) (renamecs (combine alphas betas) ds) -> 
             cs; envcons gamma x (Scheme alphas tau ds) |- evar x ;; mono (renamesh (combine alphas betas) tau)
  | T_ConTrue: forall cs gamma ls alpha,
             cs ||= r2full (Atomr Data trueAbs alpha) ->
             cs; gamma |- etrue ls ;; mono (Annvar alpha)
  | T_ConFalse: forall cs gamma ls alpha,
             cs ||= r2full (Atomr Data falseAbs alpha) ->
             cs; gamma |- efalse ls ;; mono (Annvar alpha)
  | T_ConInt: forall cs gamma ls alpha z,
             cs ||= r2full (Atomr Data intAbs alpha) ->
             cs; gamma |- eint ls z ;; mono (Annvar alpha)
  | T_Exn: forall cs gamma tau ls, 
             cs ||= r2full (Atomr Exn ls (outer tau)) ->
             cs; gamma |- ecrash ls ;; mono tau
  | T_App: forall cs gamma e1 e2 tau1 tau2 alpha tau3,
             cs; gamma |- e1 ;; mono (ArrowT tau1 alpha tau2) ->
             cs; gamma |- e2 ;; mono tau3 ->
             cs ||= r2full (Subtf Data tau3 tau1) ->
             cs ||= r2full (Subtf Exn tau3 tau1) ->
             cs ||= r2full (B4 Exn alpha (outer tau2)) ->
             cs ||= c2full (Exst Exn alpha) (B4 Exn (outer tau3) (outer tau2)) ->  
             cs; gamma |- eapp e1 e2;; mono tau2        
  | T_Abs: forall cs gamma x e tau1 tau2 alpha,
             cs; envcons gamma x (mono tau1) |- e ;; mono tau2 ->
             cs; gamma |- eabs x e ;; mono (ArrowT tau1 alpha tau2)
  | T_Let: forall cs ds gamma e1 tau1 x alphas e2 tau2,
             cs ++ ds; gamma |- e1 ;; mono tau1 ->
             cs; envcons gamma x (Scheme alphas tau1 ds) |- e2 ;; mono tau2 ->
             intersect avar alphas (efav gamma) = [] ->
             cs; gamma |- elet x e1 e2 ;; mono tau2
  | T_Fix: forall cs ds alphas (betas : list avar) f tau1 e tau2 gamma,
             length alphas = length betas ->
             Forall (baseEntails cs) (renamecs (combine alphas betas) ds) -> 
             ds; envcons gamma f (Scheme alphas tau1 ds) |- e ;; mono tau2 ->
             ds ||= r2full (Subtf Data tau2 tau1) ->
             ds ||= r2full (Subtf Exn tau2 tau1) ->
             intersect avar alphas (efav gamma) = [] ->
             cs; gamma |- efix f e ;; mono (renamesh (combine alphas betas) tau1) 
  | T_If: forall cs gamma e1 e2 e3 alpha1 tau2 tau3 tau,
             cs; gamma |- e1 ;; mono (Annvar alpha1) ->
             cs; gamma |- e2 ;; mono tau2 ->
             cs; gamma |- e3 ;; mono tau3 ->
             cs ||= c2full (Disj (Atomg Data T alpha1) (Exst Exn alpha1)) (Subtf Data tau2 tau) ->
             cs ||= c2full (Disj (Atomg Data T alpha1) (Exst Exn alpha1)) (Subtf Exn tau2 tau) ->
             cs ||= c2full (Disj (Atomg Data F alpha1) (Exst Exn alpha1)) (Subtf Data tau3 tau) ->
             cs ||= c2full (Disj (Atomg Data F alpha1) (Exst Exn alpha1)) (Subtf Exn tau3 tau) ->
             cs ||= r2full (B4 Exn alpha1 (outer tau)) ->
             cs; gamma |- eif e1 e2 e3 ;; mono tau
  | T_Op: forall alpha1 alpha2 alpha cs gamma e1 e2 anop,
             cs; gamma |- e1 ;; mono (Annvar alpha1) ->
             cs; gamma |- e2 ;; mono (Annvar alpha2) ->
             cs ||= r2full (B4 Exn alpha1 alpha) ->
             cs ||= r2full (B4 Exn alpha2 alpha) ->
             Forall (baseEntails cs) (omega anop alpha1 alpha2 alpha) ->
             opmonotonic anop ->
             cs; gamma |- eop e1 anop e2 ;; mono (Annvar alpha)             
  | T_Pair: forall cs gamma e1 e2 tau1 tau2 alpha,
             cs; gamma |- e1 ;; mono tau1 ->
             cs; gamma |- e2 ;; mono tau2 ->
             cs; gamma |- epair e1 e2 ;; mono (ProdT tau1 alpha tau2)
  | T_Fst: forall cs gamma e tau1 alpha tau2 tau,
             cs; gamma |- e ;; mono (ProdT tau1 alpha tau2) ->
             cs ||= r2full (Subtf Data tau1 tau) ->
             cs ||= r2full (Subtf Exn tau1 tau) ->             
             cs ||= r2full (B4 Exn alpha (outer tau)) ->
             cs; gamma |- efst e ;; mono tau
  | T_Snd: forall cs gamma e tau1 alpha tau2 tau,
             cs; gamma |- e ;; mono (ProdT tau1 alpha tau2) ->
             cs ||= r2full (Subtf Data tau2 tau) ->
             cs ||= r2full (Subtf Exn tau2 tau) -> 
             cs ||= r2full (B4 Exn alpha (outer tau)) ->
             cs; gamma |- esnd e ;; mono tau
  | T_Nil: forall cs gamma alpha tau ls, 
             cs ||= r2full (Atomr Data N alpha) ->
             cs; gamma |- enil ls ;; mono (ListT tau alpha)
  | T_Cons: forall cs gamma e1 tau1 e2 tau2 alpha2 tau alpha,
             cs; gamma |- e1 ;; mono tau1 ->
             cs; gamma |- e2 ;; mono (ListT tau2 alpha2) ->
             cs ||= r2full (Subtf Data tau1 tau) ->
             cs ||= r2full (Subtf Exn tau1 tau) ->
             cs ||= r2full (Subtf Data tau2 tau) ->
             cs ||= r2full (Subtf Exn tau2 tau) ->
             cs ||= r2full (Atomr Data C alpha) ->
             cs ||= r2full (B4 Exn alpha2 alpha) ->
             cs; gamma |- econs e1 e2 ;; mono (ListT tau alpha)
  | T_Case: forall cs gamma e1 e2 e3 x1 x2 alpha1 tau1 tau2 tau3 tau beta,
             cs; gamma |- e1 ;; mono (ListT tau1 alpha1) ->
             cs; gamma |- e2 ;; mono tau2 ->
             cs; envcons (envcons gamma x1 (mono tau1)) x2 (mono (ListT tau1 beta)) |- e3 ;; mono tau3 ->
             cs ||= c2full (Disj (Atomg Data N alpha1) (Exst Exn alpha1)) (Subtf Data tau2 tau) ->
             cs ||= c2full (Disj (Atomg Data N alpha1) (Exst Exn alpha1)) (Subtf Exn tau2 tau) ->
             cs ||= c2full (Disj (Atomg Data C alpha1) (Exst Exn alpha1)) (Subtf Data tau3 tau) ->
             cs ||= c2full (Disj (Atomg Data C alpha1) (Exst Exn alpha1)) (Subtf Exn tau3 tau) ->
             cs ||= r2full (B4 Exn alpha1 (outer tau)) ->
             cs ||= r2full (Atomr Data NC beta) ->
             cs ||= r2full (B4 Exn alpha1 beta) ->
             cs; gamma |- ecase e1 e2 x1 x2 e3 ;; mono tau
  | T_Close: forall cs gamma e sigma delta rho ls,
             cs; delta |- e ;; sigma ->
             consistent cs delta rho ->
             cs; gamma |- eclose ls e rho ;; sigma
  | T_Bind: forall cs gamma e sigma delta rho,
             cs; delta |- e ;; sigma ->
             consistent cs delta rho ->
             cs; gamma |- ebind rho e ;; sigma
where "cs1 ';' env1 '|-' exp1 ';;' tau1" := (hastype cs1 env1 exp1 tau1).

(* We'd like to use this, but the absence of Induction-Recursion in Coq prevents us: 
Definition opconsistent (op : opTp) : Prop :=
  forall alpha1 alpha2 alpha alpha' cs gamma n1 n2 ls1 ls2,
    Forall (baseEntails cs) (omega op alpha1 alpha2 alpha) ->
    cs; gamma |- eint ls1 n1 ;; mono (Annvar alpha1) ->
    cs; gamma |- eint ls2 n2 ;; mono (Annvar alpha2) ->
    (cs; gamma |- interpret op n1 n2 ;; mono (Annvar alpha') /\
     cs ||= r2full (Subtf Data (Annvar alpha') (Annvar alpha)) /\
     cs ||= r2full (Subtf Exn (Annvar alpha') (Annvar alpha)))
.
*)

(* Instead we shall employ the following axiom: *)
Axiom opconsistent : 
  forall op alpha1 alpha2 alpha cs gamma n1 n2 ls1 ls2,
    Forall (baseEntails cs) (omega op alpha1 alpha2 alpha) ->
    cs; gamma |- eint ls1 n1 ;; mono (Annvar alpha1) ->
    cs; gamma |- eint ls2 n2 ;; mono (Annvar alpha2) ->
    (exists alpha', cs; gamma |- interpret op n1 n2 ;; mono (Annvar alpha') /\
     cs ||= r2full (Subtf Data (Annvar alpha') (Annvar alpha)) /\
     cs ||= r2full (Subtf Exn (Annvar alpha') (Annvar alpha)))
.

(* The following lemma is validated by CL-Weak, but we did not take the trouble
   to lift it through the definition of |- and consistent. *)
Lemma EC_Weak : forall cs1 cs2 gamma rho,
  consistent cs1 gamma rho -> consistent (cs1 ++ cs2) gamma rho.
Proof.
Admitted.

(* The following three theorems that would be type rules in the non-syntax 
   directed system. They are necessary to complete the preservation proof. *)

Theorem T_Inst: forall cs gamma e alphas tau ds betas,
   cs; gamma |- e ;; Scheme alphas tau ds /\
   Forall (baseEntails cs) (renamecs (combine alphas betas) ds) ->
   cs; gamma |- e ;; mono (renamesh (combine alphas betas) tau).
Proof.
Admitted.

Theorem T_Gen: forall cs ds e tau alphas gamma,
  cs ++ ds; gamma |- e ;; mono tau /\
  intersect avar alphas (efav gamma) = [] /\
  intersect avar alphas (csetfav cs) = [] ->
  cs; gamma |- e ;; Scheme alphas tau ds.
Proof.
Admitted.

Theorem T_Sub : forall cs gamma e tau tau',
  cs; gamma |- e ;; mono tau ->
  cs ||= r2full (Subtf Data tau tau') ->
  cs ||= r2full (Subtf Exn tau tau') ->
  cs; gamma |- e ;; mono tau'.
Proof.
Admitted.

Ltac admitByCanonicalForms := admit. (* To signal the reason for admitting the fact *)

Hint Constructors step.
Hint Constructors hastype.
Hint Constructors consistent.

Theorem subtyping : forall cs tau1 tau2 i, 
  cs ||= r2full (Subtf i tau1 tau2) -> cs ||= r2full (B4 i (outer tau1) (outer tau2)).
Proof.  
  Admitted.

Theorem progress : forall cs gamma e tau rho,
  cs; gamma |- e ;; mono tau -> 
  consistent cs gamma rho -> 
  value e \/ exists e', rho |-- e \--> e'.
Proof with eauto.
  intros cs gamma e tau rho H CH.
  generalize dependent rho.
  induction H.
  Case "T-Var".
    right.
    inversion CH.
    exists (ebind rho1 e).
    apply E_Var...
    simpl.
    rewrite <- beq_id_refl. 
    reflexivity.
  Case "T-ConTrue"...
  Case "T-ConFalse"...
  Case "T-ConInt"...
  Case "T-Exn"...
  Case "T_App".
    right.
    remember (IHhastype1 rho0 CH) as Ho1.
    remember (IHhastype2 rho0 CH) as Ho2.
    destruct Ho1.
    SCase "Function is a value".
      destruct v.
      admitByCanonicalForms. (* int *)
      SSCase "Function is crash".
        destruct Ho2.
        SSSCase "Arg is a value".
          exists (ecrash (ls ++ locs(e7))).
          apply E_AppExn2...
        SSSCase "Arg can make progress".
          inversion e.
          exists (eapp (ecrash ls) x0).
          apply E_AppExn1.
          assumption.
      admitByCanonicalForms. (* true *)
      admitByCanonicalForms. (* false *)
      admitByCanonicalForms. (* nil *)     
      SSCase "Function is close".
        destruct e.
        admitByCanonicalForms. (* evar *)
        admitByCanonicalForms. (* efalse *) 
        admitByCanonicalForms. (* etrue *)
        admitByCanonicalForms. (* eint *)
        admitByCanonicalForms. (* ecrash *)
        admitByCanonicalForms. (* enil *)
        admitByCanonicalForms. (* eclose *)
        SSSCase "close contains a lambda".
          exists (ebind (rcons r i (ebind rho0 e7)) e).
           apply E_AppAbs.  
        admitByCanonicalForms. (* efix *)
        admitByCanonicalForms. (* eapp *)
        admitByCanonicalForms. (* elet *)
        admitByCanonicalForms. (* eif *)
        admitByCanonicalForms. (* eop *)
        admitByCanonicalForms. (* epair *)
        admitByCanonicalForms. (* efst *)
        admitByCanonicalForms. (* esnd *)
        admitByCanonicalForms. (* econs *)
        admitByCanonicalForms. (* ecase *)
        admitByCanonicalForms. (* ebind *)
    SCase "Function is not a value".
      inversion e.
      exists (eapp x0 e7).
      apply E_App.
      assumption.
  Case "T_Abs".
    right.
    exists (eclose nil (eabs x0 e) rho0).
    apply E_Abs.
  Case "T_Let"...
  Case "T_Fix"...
  Case "T_If".
    right.
    remember (IHhastype1 rho0 CH) as Ho1.
    remember (IHhastype2 rho0 CH) as Ho2.
    remember (IHhastype3 rho0 CH) as Ho3.
    destruct Ho1.
    SCase "condition is a value".
      destruct v.
      admitByCanonicalForms. (* int *)
      SSCase "value is crash".
        destruct Ho2.
        SSSCase "then-part is value".
          destruct Ho3.
          SSSSCase "else part is value". 
            exists (ecrash (ls ++ locs(e7) ++ locs(e8))).
            apply E_IfExn3...
          SSSSCase "else part can make progress".
            inversion e.
            exists (eif (ecrash ls) e7 x0).
            apply E_IfExn2.
            assumption.
        SSSCase "then part can make progress".
          inversion e.
          exists (eif (ecrash ls) x0 e8).
          apply E_IfExn1.
          assumption.
      SSCase "value is true".
        exists (e7).
        apply E_IfTrue.
      SSCase "value is false".
        exists (e8).
        apply E_IfFalse.
      admitByCanonicalForms. (* nil *)
      admitByCanonicalForms. (* close *)
    SCase "condition can make progress".
      inversion e.
      exists (eif x0 e7 e8).
      apply E_If.
      assumption.
  Case "T_Op".
    right.
    remember (IHhastype1 rho0 CH) as Ho1.
    remember (IHhastype2 rho0 CH) as Ho2.
    destruct Ho1.
    SCase "Left op is a value".
      destruct Ho2.
      SSCase "Right op is also a value".
        destruct v.
        SSSCase "v is an int".
          destruct v0.
          SSSSCase "v0 is an int". 
            exists (interpret anop n n0).
            apply E_OpNum.
          SSSSCase "v0 is a crash".
            exists (ecrash ls0).
            apply E_OpExn2.
            admitByCanonicalForms. (* true *)
            admitByCanonicalForms. (* false *)
            admitByCanonicalForms. (* nil *)
            admitByCanonicalForms. (* close *) 
        SSSCase "v is crash".
          destruct v0.
          SSSSCase "v0 is an int". 
            exists (ecrash ls).
            apply E_OpExn1.
          SSSSCase "v0 is a crash".
            exists (ecrash (ls ++ ls0)).
            apply E_OpExn3.
            admitByCanonicalForms. (* true *)
            admitByCanonicalForms. (* false *)
            admitByCanonicalForms. (* nil *)
            admitByCanonicalForms. (* close *) 
        SSSCase "v is true". admitByCanonicalForms. 
        SSSCase "v is false". admitByCanonicalForms. 
        SSSCase "v is nil". admitByCanonicalForms. 
        SSSCase "v is close". admitByCanonicalForms.
      SSCase "Right op is not a value".
        inversion e.
        exists (eop e6 anop x0).
        apply E_Op2.
        assumption.
    SCase "Left op is not a value".
      inversion e.
      exists (eop x0 anop e7).
      apply E_Op1.
      assumption.
  Case "T_Pair".
    right.
    exists (eclose nil (epair e6 e7) rho0).
    apply E_Pair.
  Case "T_Fst".
    right.
    remember (IHhastype rho0 CH) as Ho1.
    destruct Ho1.
    SCase "applied value".
      destruct v.
      admitByCanonicalForms. (* int *)
      SSCase "value is a crash".
        exists (ecrash ls).
        apply E_FstExn.
      admitByCanonicalForms. (* true *)
      admitByCanonicalForms. (* false *)
      admitByCanonicalForms. (* nil *)     
      SSCase "value is a close".
        destruct e.
        admitByCanonicalForms. (* evar *)
        admitByCanonicalForms. (* efalse *) 
        admitByCanonicalForms. (* etrue *)
        admitByCanonicalForms. (* eint *)
        admitByCanonicalForms. (* ecrash *)
        admitByCanonicalForms. (* enil *)
        admitByCanonicalForms. (* eclose *)
        admitByCanonicalForms. (* eabs *)
        admitByCanonicalForms. (* efix *)
        admitByCanonicalForms. (* eapp *)
        admitByCanonicalForms. (* elet *)
        admitByCanonicalForms. (* eif *)
        admitByCanonicalForms. (* eop *)
        SSSCase "expression in the close is a pair".
          exists (ebind r e6).
          apply E_FstPair.
        admitByCanonicalForms. (* efst *)
        admitByCanonicalForms. (* esnd *)
        admitByCanonicalForms. (* econs *)
        admitByCanonicalForms. (* ecase *)
        admitByCanonicalForms. (* ebind *)
    SCase "argument can make progress".
      inversion e0.
      exists (efst x0).
      apply E_Fst.
      assumption.
  Case "T_Snd".
    right.
    remember (IHhastype rho0 CH) as Ho1.
    destruct Ho1.
    SCase "applied value".
      destruct v.
      admitByCanonicalForms. (* int *)
      SSCase "value is a crash".
        exists (ecrash ls).
        apply E_SndExn.
      admitByCanonicalForms. (* true *)
      admitByCanonicalForms. (* false *)
      admitByCanonicalForms. (* nil *)     
      SSCase "value is a close".
        destruct e.
        admitByCanonicalForms. (* evar *)
        admitByCanonicalForms. (* efalse *) 
        admitByCanonicalForms. (* etrue *)
        admitByCanonicalForms. (* eint *)
        admitByCanonicalForms. (* ecrash *)
        admitByCanonicalForms. (* enil *)
        admitByCanonicalForms. (* eclose *)
        admitByCanonicalForms. (* eabs *)
        admitByCanonicalForms. (* efix *)
        admitByCanonicalForms. (* eapp *)
        admitByCanonicalForms. (* elet *)
        admitByCanonicalForms. (* eif *)
        admitByCanonicalForms. (* eop *)
        SSSCase "expression in the close is a pair".
          exists (ebind r e7).
          apply E_SndPair.
        admitByCanonicalForms. (* efst *)
        admitByCanonicalForms. (* esnd *)
        admitByCanonicalForms. (* econs *)
        admitByCanonicalForms. (* ecase *)
        admitByCanonicalForms. (* ebind *)
    SCase "argument can make progress".
      inversion e0.
      exists (esnd x0).
      apply E_Snd.
      assumption.
  Case "T_Nil"...
  Case "T_Cons".
    right.
    exists (eclose nil (econs e6 e7) rho0). (* Is e6 e7 robust? *)
    apply E_Cons.
  Case "T_Case".
    right.
    remember (IHhastype1 rho0 CH) as Ho1.    
    destruct Ho1.
    SCase "case on value".
      destruct v.
      admitByCanonicalForms. (* int *)
      SSCase "value is crash".
        remember (IHhastype2 rho0 CH) as Ho2.    
        destruct Ho2.
        SSSCase "nil case is value".
          remember (IHhastype3 (rcons (rcons rho0 x1 (ecrash nil)) x2 (ecrash nil))) as Ho2.
          assert (consistent cs
        (envcons (envcons gamma x1 (mono tau1)) x2 (mono (ListT tau1 beta)))
        (rcons (rcons rho0 x1 (ecrash [])) x2 (ecrash []))) as K.
          constructor.
          constructor.
          constructor.
          split.
          assumption.
          apply T_Exn with (ls := []).
          apply CL_Botr.
          apply T_Exn with (ls := []).
          apply CL_Botr. 
          remember (Ho2 K) as Ho3.
          destruct Ho3.
          SSSSCase "cons case is a value".
            exists (ecrash (ls ++ locs(e7) ++ locs(e8))).
            apply E_CaseExn3...           
          SSSSCase "cons case can make progress".
            inversion e.
            exists (ecase (ecrash ls) e7 x1 x2 x0).
            apply E_CaseExn2.
            assumption.
        SSSCase "nil case can make progress".
          inversion e.
          exists (ecase (ecrash ls) x0 x1 x2 e8).
          apply E_CaseExn1.
          assumption.
      admitByCanonicalForms. (* true *)
      admitByCanonicalForms. (* false *)
      SSCase "value is nil".
        exists (e7).
        apply E_CaseNil.
      SSCase "value is close".     
        destruct e.
        admitByCanonicalForms. (* evar *)
        admitByCanonicalForms. (* efalse *) 
        admitByCanonicalForms. (* etrue *)
        admitByCanonicalForms. (* eint *)
        admitByCanonicalForms. (* ecrash *)
        admitByCanonicalForms. (* enil *)
        admitByCanonicalForms. (* eclose *)
        admitByCanonicalForms. (* eabs *)
        admitByCanonicalForms. (* efix *)
        admitByCanonicalForms. (* eapp *)
        admitByCanonicalForms. (* elet *)
        admitByCanonicalForms. (* eif *)
        admitByCanonicalForms. (* eop *)
        admitByCanonicalForms. (* epair *)
        admitByCanonicalForms. (* efst *)
        admitByCanonicalForms. (* esnd *)
        SSSCase "expression in close is a cons".
          exists (ebind (rcons (rcons rho0 x1 (ebind r e6)) x2 (ebind r e9)) e8).
          apply E_CaseCons.
        admitByCanonicalForms. (* ecase *)
        admitByCanonicalForms. (* ebind *)
    SCase "case can make progress".
      inversion e.
      exists (ecase x0 e7 x1 x2 e8).
      apply E_Case.
      assumption.
  Case "T_Close"...
  Case "T_Bind".
    right.
    remember (IHhastype rho0 H0) as Ho.
    destruct Ho.
    SCase "Is a value".
      exists (e).
      apply E_Bind2.
      assumption.
    SCase "Is not a value".
      inversion e0.
      exists (ebind rho0 x0).
      apply E_Bind1.
      assumption.
Qed.    

Theorem preservation : forall cs gamma e e' tau1 rho,
  cs; gamma |- e ;; mono tau1 ->
  rho |-- e \--> e' ->
  consistent cs gamma rho ->
  exists tau2, cs; gamma |- e' ;; mono tau2  /\
               (forall i, cs ||= r2full (Subtf i tau2 tau1)).
Proof with eauto.
  intros.
  generalize dependent gamma.
  generalize dependent tau1.
  induction H0.
  Case "E-Var".  
    intros.
    inversion H0...
    subst.
    rename H7 into H48, H0 into H47.
    rename x0 into x.
    rename gamma0 into gamma, rho' into rho.
    exists (renamesh (combine alphas betas) tau).
    split.
    inversion H1...
    subst.
    destruct H7 as [H49 H50]. 
    assert (E: rho1 = rho /\ e0 = e).
    pose H as Tmp.
    unfold lookup in Tmp.
    rewrite <- beq_id_refl in Tmp.
    unfold rcombine in Tmp.
    inversion Tmp...
    destruct E.
    subst.
    pose H49 as H51.
    apply T_Bind with (gamma := gamma) (e := e) (sigma := Scheme alphas tau ds) in H51...
    pose H51 as H52.
    apply T_Inst with (ds := ds).
    split...
    intros. apply S_Refl.
  Case "E-Abs".
    intros.
    exists (tau1).
    split.
    apply T_Close with (delta := gamma)...
    unfold r2full.
    unfold lift.
    intros.
    apply S_Refl.
  Case "E-Fix".
    intros.
    inversion H...
    subst.
    rename H5 into H99, H6 into H100, H9 into H101a, H10 into H101b, H11 into H102.
    rename tau0 into tau1, rho0 into rho.
    exists (renamesh (combine alphas betas) tau1).
    split.
    apply T_Bind with (delta := envcons gamma f (Scheme alphas tau1 ds))...
    admit. (* Left unproven for now *)
    apply EC_Extend.
    split...
    apply T_Bind with (delta := gamma)...
    apply T_Gen.
    split...
    assert (Eq: tau1 = renamesh (combine alphas alphas) tau1).
    rewrite -> renameid4sh...
    rewrite -> Eq.
    apply T_Fix with (cs := cs ++ ds) (ds := ds) (tau2 := tau2)...
    rewrite -> renameid4cs.
    admit. (* Follows from repeated use of CL_Weak *)
    split...
    admit. (* See issue remarked upon under E-Let, below. *)
    intros. apply S_Refl.
  Case "E-App".
    intros.
    rename e6 into e1, e7 into e2, tau1 into tau12.
    inversion H...
    subst.
    rename tau1 into tau11, tau3 into tau13, alpha into alpha1.
    rename H5 into H57, H6 into H58, H7 into H59a, H10 into H59b, H11 into H60, H12 into H61.
    exists (tau12).
    split.
    remember (IHstep (ArrowT tau11 alpha1 tau12) gamma H57 H1) as HInd.
    destruct HInd.
    destruct a.
    remember (b Data) as Ha.
    inversion Ha...
    subst.
    rename H6 into H56a, H10 into H54a, H11 into H55a.
    rename alpha0 into alpha2, tau1 into tau21, tau2 into tau22.
    rename h into H53.
    remember (b Exn) as Hb.
    inversion Hb...
    subst.
    rename H6 into H56b, H12 into H54b, H13 into H55b.
    apply T_App with (e1 := e1') (tau1 := tau21) (alpha := alpha1) 
                     (tau2 := tau12) (tau3 := tau13).
    apply T_Sub with (tau := ArrowT tau21 alpha2 tau22).
    assumption.
    apply CL_SFun...
    apply S_Refl.
    apply CL_SFun...
    apply S_Refl.
    assumption.
    apply S_Trans with (tau2 := tau11)...
    apply S_Trans with (tau2 := tau11)...
    assumption.
    assumption.
    intros. apply S_Refl.
  Case "E-AppAbs".
    intros. 
    inversion H...
    subst.
    rename H4 into H67, H5 into H68, H6 into H69a, H9 into H69b, H10 into H70, H11 into H71.
    rename e6 into e1, e7 into e2.
    rename tau1 into tau2, tau0 into tau1.
    inversion H67...
    subst.
    rename H7 into H72, H8 into H73.
    inversion H72...
    subst.
    rename H4 into H74.
    exists (tau2).
    split.
    apply T_Bind with (delta := envcons delta x0 (mono tau1)) 
                      (rho := rcons rho1 x0 (ebind rho0 e2)).
    assumption.
    apply EC_Extend.
    split.
    assumption.
    apply T_Bind with (delta := gamma) (gamma := delta).
    apply T_Sub with (tau := tau3)...
    assumption.
    intros. apply S_Refl.
  Case "E-AppExn1".
    intros. 
    inversion H...
    subst.
    rename H5 into H77, H6 into H78, H7 into H79a, H10 into H79b, H11 into H80, H12 into H81.
    rename e6 into e2.
    rename tau1 into tau2, tau0 into tau1.    
    remember (IHstep tau3 gamma H78 H1) as HInd.
    destruct HInd.
    destruct a.
    rename h into H75.
    rename b into H76.
    rename x0 into tau4.  
    exists (tau2).
    split.
    apply T_App with (tau1 := tau1) (alpha := alpha) (tau3 := tau4).
    assumption.
    assumption.
    apply S_Trans with (tau3)...
    apply S_Trans with (tau3)...
    assumption.
   (* remember (H76 Data) as H76a.*)
    remember (H76 Exn) as H76b.
    pose H76b as H83.
    apply subtyping in H83.
    pose H83 as H84.
    apply CL_Weak with (cs2 := [Guard (Exst Exn alpha)]) in H84.
    pose H81 as H82.
    apply CL_ImplE in H82.
    apply CL_ImplI.
    unfold r2full.
    apply B4_Trans with (alpha2 := outer tau3)...
    intros. apply S_Refl.
  Case "E-AppExn2".
    intros. 
    inversion H0...
    subst.
    rename H5 into H87, H6 into H88, H7 into H89a, H10 into H89b, H11 into H90, H12 into H91.
    rename tau3 into tau13, alpha into alpha1.
    rename tau1 into tau12, tau0 into tau11.
    inversion H87...
    subst.
    rename H6 into H92.
    unfold outer in H92. 
    rename H92 into H93.
    exists (tau12).
    split.
    apply T_Exn.
    apply CL_B4_ExnConcat.
    apply AtomB4_Trans with (alpha := alpha1)...
    apply CL_ImplE in H91.
    apply AtomB4_Trans with (alpha := outer tau13)...
    inversion H88; solve by inversion.
    assert (Ha: cs ||= r2full (B4 Exn (outer tau13) (outer tau12))).
    apply CL_MP with (c1 := Guard (Exst Exn alpha1))...
    split...
    apply CL_ExI with (val := ls1).
    apply CL_CoerceRG...
    assumption.
    intros. apply S_Refl.
  Case "E-Let".
    intros. 
    inversion H...
    subst.
    rename H7 into H113, H8 into H114, H9 into H115.
    rename e6 into e1, e7 into e2, tau1 into tau2, tau0 into tau1.
    rename x0 into x, rho0 into rho.
    exists (tau2).
    split.
    apply T_Bind with (delta := envcons gamma x (Scheme alphas tau1 ds)).
    assumption.
    apply EC_Extend.
    split.
    assumption.
    apply T_Gen.
    split.
    apply T_Bind with (delta := gamma) (cs := cs ++ ds)...
    apply EC_Weak with (cs2 := ds).
    assumption.
    split...
    admit. (* We expect this to hold, because an implementation of Gen will make sure of that
              but we can't prove it at this point. Having looked at the literature (Smith's 
              POLYMORPHIC TYPE  INFERENCE FOR LANGUAGES WITH OVERLOADING AND SUBTYPING and 
              Hanne Riis Nielson, Flemming Nielson, Torben Amtoft: Polymorphic Subtyping for 
              Effect Analysis, 1996 pages 141-243), we have concluded that this is normally 
              treated as a hidden invariant.
              A similar issue arises in (T-Fix). *)
    intros. apply S_Refl.
  Case "E-If".
    intros.
    inversion H...
    subst.
    rename e6 into e1, e7 into e2, e8 into e3.
    rename tau1 into tau.
    rename H6 into H118, H7 into H119, H8 into H120.
    rename H9 into H121a, H12 into H121b, H13 into H122a, 
           H14 into H122b, H15 into H123.
    remember (IHstep (Annvar alpha1) gamma H118 H1) as HInd.
    destruct HInd.
    destruct a.
    remember (b Data) as Ha.
    inversion Ha...
    subst.
    rename alpha0 into alpha1'.
    rename H4 into H126, h into H124, b into H125.
    exists (tau).
    split.
    apply T_If with (alpha1 := alpha1) (tau2 := tau2) (tau3 := tau3)...
    apply T_Sub with (tau := Annvar alpha1')...
    intros. apply S_Refl.
  Case "E-IfTrue".
    intros.
    inversion H...
    subst.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau, H5 into H127.
    rename H6 into H128, H7 into H129, H8 into H130a, H11 into H130b.
    rename H12 into H131a, H13 into H131b, H14 into H132.
    inversion H127...
    subst.
    rename H5 into H133.
    unfold r2full in H133.
    unfold lift in H133.
    exists (tau2).
    split.
    assumption.
    intros.
    destruct i.
    pose H133 as H134.
    unfold trueAbs in H134.
    pose H134 as H135.
    apply CL_CoerceRG in H135.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H135.
    pose H130a as H136a.
    apply CL_ImplE in H136a.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data T alpha1) (Exst Exn alpha1))).
    split...
    pose H133 as H134.
    unfold trueAbs in H134.
    pose H134 as H135.
    apply CL_CoerceRG in H135.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H135.
    pose H130b as H136b.
    apply CL_ImplE in H136b.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data T alpha1) (Exst Exn alpha1))).
    split...
  Case "E-IfFalse".
    intros.
    inversion H...
    subst.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau, H5 into H127.
    rename H6 into H128, H7 into H129, H8 into H130a, H11 into H130b.
    rename H12 into H131a, H13 into H131b, H14 into H132.
    inversion H127...
    subst.
    rename H5 into H133.
    unfold r2full in H133.

    exists (tau3).
    split.
    assumption.
    intros.
    destruct i.  
    pose H133 as H134.
    unfold falseAbs in H134.
    pose H134 as H135.
    apply CL_CoerceRG in H135.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H135.
    pose H131a as H136a.
    apply CL_ImplE in H136a.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data F alpha1) (Exst Exn alpha1))).
    split...
    pose H133 as H134.
    unfold trueAbs in H134.
    pose H134 as H135.
    apply CL_CoerceRG in H135.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H135.
    pose H131b as H136b.
    apply CL_ImplE in H136b.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data F alpha1) (Exst Exn alpha1))).
    split...
  Case "E-IfExn1".
    intros.
    inversion H...
    subst.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau.
    rename H6 into H138, H7 into H139, H8 into H140, H9 into H141a.
    rename H12 into H141b, H13 into H142a, H14 into H142b, H15 into H143.
    remember (IHstep tau2 gamma H139 H1) as Hind.
    destruct Hind.
    destruct a.
    rename h into H144, b into H145.
    rename x0 into tau2'.
    exists (tau).
    split.
    apply T_If with (tau2 := tau2') (e1 := (ecrash ls1)) (e2 := e2') 
                    (tau3 := tau3) (alpha1 := alpha1)...
    pose (H145 Data) as H145a.
    pose H145a as H147a.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data T alpha1) (Exst Exn alpha1))]) in H147a.
    pose H141a as H148a.
    apply CL_ImplE in H148a.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau2)...

    pose (H145 Exn) as H145b.
    pose H145b as H147b.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data T alpha1) (Exst Exn alpha1))]) in H147b.
    pose H141b as H148b.
    apply CL_ImplE in H148b.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau2)...
    intros. apply S_Refl.
  Case "E-IfExn2".
    intros.
    inversion H...
    subst.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau.
    rename H6 into H138, H7 into H139, H8 into H140, H9 into H141a.
    rename H12 into H141b, H13 into H142a, H14 into H142b, H15 into H143.
    remember (IHstep tau3 gamma H140 H1) as Hind.
    destruct Hind.
    destruct a.
    rename h into H144, b into H145.
    rename x0 into tau3'.
    exists (tau).
    split.
    apply T_If with (tau2 := tau2) (e1 := (ecrash ls1)) (e3 := e3') 
                    (tau3 := tau3') (alpha1 := alpha1)...
    pose (H145 Data) as H145a.
    pose H145a as H147a.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data F alpha1) (Exst Exn alpha1))]) in H147a.
    pose H142a as H148a.
    apply CL_ImplE in H148a.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau3)...

    pose (H145 Exn) as H145b.
    pose H145b as H147b.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data F alpha1) (Exst Exn alpha1))]) in H147b.
    pose H142b as H148b.
    apply CL_ImplE in H148b.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau3)...
    intros. apply S_Refl.
  Case "E-IfExn3".
    intros.
    inversion H0...
    subst.
    rename H6 into H151, H7 into H152, H8 into H153, H9 into H154a, 
           H12 into H154b.
    rename H13 into H155a, H14 into H155b, H15 into H156.
    rename tau1 into tau.
    exists (tau).
    split.
    apply T_Exn with (ls := (ls1 ++ ls2 ++ ls3)).
    inversion H151...
    subst.
    rename H6 into H158.
    unfold outer in H158.
    apply CL_B4_ExnConcat...
    apply AtomB4_Trans with (alpha := alpha1)...
    apply CL_B4_ExnConcat.
    apply CL_ImplE in H154b.
    apply AtomB4_Trans with (alpha := outer tau2)...
    inversion H152; solve by inversion.
    inversion H154b; solve by inversion.
    apply CL_ImplE in H155b.
    apply AtomB4_Trans with (alpha := outer tau2)...
    inversion H153; solve by inversion.
    inversion H155b; solve by inversion.
    intros. apply S_Refl.
  Case "E-Op1".
    intros.
    inversion H...
    subst.
    rename e6 into e1, e7 into e2.
    rename H6 into H163, H7 into H164.
    rename H10 into H165, H11 into H166.
    rename H12 into H167.
    remember (IHstep (Annvar alpha1) gamma H163 H1) as HInd.
    destruct HInd.
    destruct a.
    rename h into H161, b into H162.
    remember (H162 Exn) as H162b.
    inversion H162b...
    subst.
    rename alpha0 into alpha1'.
    exists (Annvar alpha).
    split.
    apply T_Op with (alpha1 := alpha1') (alpha2 := alpha2)...
    apply B4_Trans with (alpha2 := alpha1)...
    intros. apply S_Refl.
  Case "E-Op2".
    intros.
    inversion H...
    subst.
    rename e6 into e1, e7 into e2.
    rename H6 into H163, H7 into H164.
    rename H10 into H165, H11 into H166.
    rename H12 into H167.
    remember (IHstep (Annvar alpha2) gamma H164 H1) as HInd.
    destruct HInd.
    destruct a.
    rename h into H161, b into H162.
    remember (H162 Exn) as H162b.
    inversion H162b...
    subst.
    rename alpha0 into alpha2'.
    exists (Annvar alpha).
    split.
    apply T_Op with (alpha1 := alpha1) (alpha2 := alpha2')...
    apply B4_Trans with (alpha2 := alpha2)...
    intros. apply S_Refl.
  Case "E-OpNum".
    intros.
    inversion H...
    subst.
    rename H5 into H168, H6 into H169, H9 into H170, H10 into H171, H11 into H172.
    apply opconsistent with (op := op0) (alpha1 := alpha1) (alpha := alpha) (alpha2 := alpha2)
                 (n1 := n1) (n2 := n2) (ls2 := ls2) in H168.
    destruct H168.
    rename x0 into alpha'.
    exists (Annvar alpha').
    destruct H0. destruct H2.
    split...
    intros. destruct i...
    assumption.
    assumption.
  Case "E-OpExn1".
    intros.
    inversion H...
    subst.
    rename H5 into H175, H6 into H176, H9 into H177, H10 into H178, H11 into H179.
    inversion H175...
    subst.
    rename H5 into H180.
    exists (Annvar alpha).
    split.
    apply T_Exn with (ls := ls1) (tau := Annvar alpha).
    unfold outer.
    apply AtomB4_Trans with (alpha := alpha1)...
    intros. apply S_Refl.
  Case "E-OpExn2". (* Copy from E-OpExn2 *)
    intros.
    inversion H...
    subst.
    rename H5 into H175, H6 into H176, H9 into H177, H10 into H178, H11 into H179.
    inversion H176...
    subst.
    rename H5 into H180.
    exists (Annvar alpha).
    split.
    apply T_Exn with (ls := ls2) (tau := Annvar alpha).
    unfold outer.
    apply AtomB4_Trans with (alpha := alpha2)...
    intros. apply S_Refl.
  Case "E-OpExn3".
    intros.
    inversion H...
    subst.
    rename H5 into H182, H6 into H183, H9 into H184, H10 into H185, H11 into H186.
    inversion H182...
    subst.
    inversion H183...
    subst.
    rename H5 into H187.
    rename H6 into H188.
    exists (Annvar alpha).
    split. 
    apply T_Exn.
    apply CL_B4_ExnConcat.
    apply AtomB4_Trans with (alpha := alpha1)...
    apply AtomB4_Trans with (alpha := alpha2)...
    intros. apply S_Refl.
  Case "E-Pair".
    intros.
    exists (tau1).
    split.
    apply T_Close with (delta := gamma)...
    unfold r2full.
    unfold lift.
    intros. apply S_Refl.
  Case "E-Cons".
    intros.
    exists (tau1).
    split.
    apply T_Close with (delta := gamma)...
    unfold r2full.
    unfold lift.
    intros. apply S_Refl.
  Case "E-Fst".
    intros.
    inversion H...
    subst.
    rename H4 into H194, H8 into H195b, H9 into H196.
    rename tau1 into tau, tau0 into tau1.
    remember (IHstep (ProdT tau1 alpha tau2) gamma H194 H1) as HInd.
    destruct HInd.
    destruct a.
    remember (b Data) as Ha.
    inversion Ha...
    subst.
    rename H7 into H193a, H11 into H191a, H12 into H192a. 
    (* Now we know we are dealing with a prod type *)
    rename tau0 into tau1', alpha1 into alpha', tau3 into tau2'.
    rename H5 into H195a.
    remember (b Exn) as Hb.
    inversion Hb.
    subst.
    rename H6 into H193b, H12 into H191b, H13 into H192b.
    
    exists (tau).
    split.
    apply T_Fst with (alpha := alpha') (tau2 := tau2') (tau1 := tau1')...
    unfold r2full.
    apply S_Trans with (tau2 := tau1)...
    apply S_Trans with (tau2 := tau1)...
    apply B4_Trans with (alpha2 := alpha)...
    intros. apply S_Refl.
  Case "E-FstPair".
    intros.
    inversion H...
    subst.
    inversion H3...
    subst.
    inversion H11.
    subst.
    rename tau1 into tau, tau0 into tau1.
    rename e6 into e1, e7 into e2, rho' into rho1.
    rename H8 into H200, H10 into H197, H15 into H198.
    rename H12 into H201, H4 into H199a, H7 into H199b.
    exists (tau1).
    split.
    apply T_Bind with (delta := delta)...
    intros. destruct i...
  Case "E-FstExn".
    intros.
    inversion H...
    subst.
    inversion H3...
    subst.
    rename H3 into H202, H4 into H203a, H7 into H203b.
    rename H8 into H204, H9 into H205.
    rename tau1 into tau, tau0 into tau1.
    exists (tau).
    split.
    unfold outer in H205.
    apply T_Exn...
    apply AtomB4_Trans with (alpha := alpha)...    
    intros. apply S_Refl.
  Case "E-Snd". (* Transliterated from E-Fst *)
    intros.
    inversion H...
    subst.
    rename H4 into H194, H8 into H195b, H9 into H196.
    rename tau1 into tau, tau0 into tau1.
    remember (IHstep (ProdT tau1 alpha tau2) gamma H194 H1) as HInd.
    destruct HInd.
    destruct a.
    remember (b Data) as Ha.
    inversion Ha...
    subst.
    rename H7 into H193a, H11 into H191a, H12 into H192a. 
    (* Now we know we are dealing with a prod type *)
    rename tau0 into tau1', alpha1 into alpha', tau3 into tau2'.
    rename H5 into H195a.
    remember (b Exn) as Hb.
    inversion Hb.
    subst.
    rename H6 into H193b, H12 into H191b, H13 into H192b.
    
    exists (tau).
    split.
    apply T_Snd with (alpha := alpha') (tau2 := tau2') (tau1 := tau1')...
    unfold r2full.
    apply S_Trans with (tau2 := tau2)...
    apply S_Trans with (tau2 := tau2)...
    apply B4_Trans with (alpha2 := alpha)...
    intros. apply S_Refl.
  Case "E-SndPair". (* Transliterared from E-FstPair *)
    intros.
    inversion H...
    subst.
    inversion H3...
    subst.
    inversion H11.
    subst.
    rename tau1 into tau, tau0 into tau1.
    rename e6 into e1, e7 into e2, rho' into rho1.
    rename H8 into H200, H10 into H197, H15 into H198.
    rename H12 into H201, H4 into H199a, H7 into H199b.
    exists (tau2).
    split.
    apply T_Bind with (delta := delta)...
    intros. destruct i...
  Case "E-SndExn". (* Copy from E-FstExn *)
    intros.
    inversion H...
    subst.
    inversion H3...
    subst.
    rename H3 into H202, H4 into H203a, H7 into H203b.
    rename H8 into H204, H9 into H205.
    rename tau1 into tau, tau0 into tau1.
    exists (tau).
    split.
    unfold outer in H205.
    apply T_Exn...
    apply AtomB4_Trans with (alpha := alpha)...    
    intros. apply S_Refl.
  Case "E-Case".
    intros.
    inversion H...
    subst.
    rename H8 into H208, H9 into H209, H10 into H210, H11 into H211a,
           H14 into H211b.
    rename H15 into H212a, H16 into H212b, H17 into H213.
    rename H18 into H214, H19 into H215.
    rename e6 into e1, e7 into e2, e8 into e3.
    rename tau1 into tau, tau0 into tau1.
    remember (IHstep (ListT tau1 alpha1) gamma H208 H1) as HInd.
    destruct HInd.
    destruct a.   
    rename h into H216, b into H217.
    remember (H217 Data) as H217a.
    inversion H217a.
    subst.
    rename alpha0 into alpha1', tau0 into tau1'.

    exists (tau).
    split.
    apply T_Case with (alpha1 := alpha1) (tau1 := tau1) (tau2 := tau2) 
                      (tau3 := tau3) (beta := beta)...
    remember (H217 Data) as H217a.
    remember (H217 Exn) as H217b.
    apply T_Sub with (tau := ListT tau1' alpha1')...
    intros. apply S_Refl.
  Case "E-CaseNil".
    intros.
    inversion H...
    subst.
    rename H7 into H219, H8 into H220, H9 into H221, H10 into H222a, 
           H13 into H222b.
    rename H14 into H223a, H15 into H223b, H16 into H224.
    rename H17 into H225, H18 into H226.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau, tau0 into tau1.
    inversion H219...
    subst.
    rename H5 into H227.
    exists (tau2).
    split.
    assumption.
    intros.
    destruct i.
    pose H227 as H228.
    apply CL_CoerceRG in H228.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H228.
    pose H222a as H229a.
    apply CL_ImplE in H229a.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...
    pose H227 as H228.
    apply CL_CoerceRG in H228.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H228.
    pose H222b as H229b.
    apply CL_ImplE in H229b.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...    
  Case "E-CaseCons".
    intros.
    inversion H...
    subst.
    rename H7 into H233, H8 into H234, H9 into H235, H10 into H236a, 
           H13 into H236b.
    rename H14 into H237a, H15 into H237b, H16 into H238.
    rename H17 into H239, H18 into H240.
    inversion H233...
    subst.
    rename H7 into H241, H8 into H242.
    inversion H241...
    subst.
    rename H5 into H243, H6 into H244, H7 into H245a, H8 into H245b.
    rename H11 into H246a, H12 into H246b, H13 into H247, H14 into H248.
    rename alpha2 into alpha12.
    rename tau4 into tau11, tau5 into tau12, tau1 into tau, tau0 into tau1.
    rename e6 into e1, e7 into e2, e8 into e3.
    exists (tau).
    split.
    apply T_Bind with (e := e3) (delta := envcons (envcons gamma x1 (mono tau1)) x2 (mono (ListT tau1 beta)))
                      (sigma := mono tau) (rho := (rcons (rcons rho0 x1 (ebind rho1 e1)) x2 (ebind rho1 e1')))...
    apply T_Sub with (tau := tau3)...
    pose H247 as H249.
    apply CL_CoerceRG in H249.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H249.
    pose H237a as H250a.
    apply CL_ImplE in H250a.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))).
    split...
    pose H247 as H249.
    apply CL_CoerceRG in H249.
    apply CL_OrI with (g2 := Exst Exn alpha1) in H249.
    pose H237b as H250b.
    apply CL_ImplE in H250b.
    apply CL_MP with (c1 := Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))).
    split...
    apply EC_Extend.
    split...
(*(sigma := mono tau1) (gamma := envcons gamma x1 (mono tau1))
                         (x := x2) (e := ebind rho1 e1').*)
    apply EC_Extend.
    split...
    apply T_Sub with (tau := tau11)...
    apply T_Bind with (e := e1') (rho := rho1) (sigma := mono (ListT tau1 beta)) (delta := delta).
    apply T_Sub with (tau := (ListT tau12 alpha12))...
    apply CL_SList...
    apply ListsUnderNC with (tau' := ListT tau12 alpha12) (tau := tau12)... 
    apply CL_SList...
    apply B4_Trans with (alpha2 := alpha1)...
    assumption.
    intros. apply S_Refl.
  Case "E-CaseExn1".
    intros.
    inversion H...
    subst.
    rename H8 into H257, H9 into H258, H10 into H259, H11 into H260a, H14 into H260b.
    rename H15 into H261a, H16 into H261b, H17 into H262.
    rename H18 into H263, H19 into H264.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau, tau0 into tau1.
    inversion H257...
    subst.
    rename H6 into H267.
    remember (IHstep tau2 gamma H258 H1) as HInd.
    destruct HInd.
    destruct a.  
    rename h into H265.
    rename b into H266.
    rename x0 into tau2'.
    unfold outer in H267.
    rename H267 into H268.
    apply CL_CoerceRG in H268.
    apply CL_ExI in H268.
    rename H268 into H269.
    apply CL_OrI with (g2 := Atomg Data N alpha1) in H269.
    rename H269 into H270.
    apply CL_OrC in H270.
    exists (tau).
    split.
    apply T_Case with (e1 := ecrash ls1) (e2 := e2') (e3 := e3)
                      (alpha1 := alpha1) (tau := tau) (tau1 := tau1)
                      (tau2 := tau2') (tau3 := tau3) (beta := beta)...
    pose H260a as H272a.
    apply CL_ImplE in H272a.
    assert (H273a: cs ||= r2full (Subtf Data tau2 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...
    assert (H274a: cs ||= r2full (Subtf Data tau2' tau)).
    apply S_Trans with (tau2 := tau2)...
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))]) in H274a.
    apply CL_ImplI in H274a.
    assumption.
    pose H260b as H272b.
    apply CL_ImplE in H272b.
    assert (H273b: cs ||= r2full (Subtf Exn tau2 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...
    assert (H274b: cs ||= r2full (Subtf Exn tau2' tau)).
    apply S_Trans with (tau2 := tau2)...
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))]) in H274b.
    apply CL_ImplI in H274b.
    assumption.
    intros. apply S_Refl.
  Case "E-CaseExn2".
    intros.
    inversion H...
    subst.
    rename H8 into H286, H9 into H287, H10 into H288, H11 into H289a, H14 into H289b.
    rename H15 into H290a, H16 into H290b, H17 into H291.
    rename H18 into H292, H19 into H293.
    rename e6 into e2, e7 into e3.
    rename tau1 into tau, tau0 into tau1.
    assert (H294: cs; gamma |- ecrash nil ;; mono tau1).
    apply T_Exn.
    apply CL_Botr.
    assert (H295: cs; envcons gamma x1 (mono tau1) |- ecrash nil ;; mono  (ListT tau1 beta)).
    apply T_Exn.
    apply CL_Botr.
    assert (H296: consistent cs 
                  (envcons (envcons gamma x1 (mono tau1)) x2 (mono (ListT tau1 beta)))
                  (rcons (rcons rho0 x1 (ecrash [])) x2 (ecrash []))).
    apply EC_Extend.
    split.
    apply EC_Extend.
    split.
    assumption.
    apply H294.
    apply H295.
    remember (IHstep tau3 (envcons (envcons gamma x1 (mono tau1)) x2 (mono (ListT tau1 beta))) H288 H296) as HInd.
    exists (tau).
    split.
    destruct HInd.
    destruct a.
    rename x0 into tau3', b into H285, h into H284.
    apply T_Case with (alpha1 := alpha1) (tau1 := tau1) (tau2 := tau2) (tau3 := tau3') (beta := beta)...
    remember (H285 Data) as H285a.
    pose H285a as H297a.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))]) in H297a.
    pose H290a as H298a.
    apply CL_ImplE in H298a.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau3)...
    remember (H285 Exn) as H285b.
    pose H285b as H297b.
    apply CL_Weak with (cs2 := [Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))]) in H297b.
    pose H290b as H298b.
    apply CL_ImplE in H298b.
    apply CL_ImplI.
    apply S_Trans with (tau2 := tau3)...
    intros. apply S_Refl.
  Case "E-CaseExn3".
    intros.
    inversion H0...
    subst.
    rename H8 into H301, H9 into H302, H10 into H303, H11 into H304a, H14 into H304b.
    rename H15 into H305a, H16 into H305b, H17 into H306.
    rename H18 into H307, H19 into H308.
    rename tau1 into tau, tau0 into tau1.
    inversion H301...
    subst.
    rename H6 into H309.
    pose H309 as H310.
    unfold outer in H310.
    exists (tau).
    split.
    apply T_Exn.
    pose H310 as H311.
    apply CL_CoerceRG in H311.
    apply CL_ExI in H311.
    apply CL_OrI with (g2 := Atomg Data N alpha1) in H311.
    apply CL_OrC in H311.
    pose H310 as H312.
    apply CL_CoerceRG in H312.
    apply CL_ExI in H312.
    apply CL_OrI with (g2 := Atomg Data C alpha1) in H312.
    apply CL_OrC in H312.
    apply CL_ImplE in H304a.
    apply CL_ImplE in H304b.
    assert (Ha: cs ||= r2full (Subtf Data tau2 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...
    rename Ha into H313a.
    assert (Hb: cs ||= r2full (Subtf Exn tau2 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data N alpha1) (Exst Exn alpha1))).
    split...
    rename Hb into H313b.

    apply CL_ImplE in H305a.
    apply CL_ImplE in H305b.
    assert (Ha: cs ||= r2full (Subtf Data tau3 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))).
    split...
    rename Ha into H314a.
    assert (Hb: cs ||= r2full (Subtf Data tau3 tau)).
    apply CL_MP with (c1 := Guard (Disj (Atomg Data C alpha1) (Exst Exn alpha1))).
    split...
    rename Hb into H314b.
    unfold outer in H309.
    apply CL_B4_ExnConcat...
    apply AtomB4_Trans with (alpha := alpha1)...
    apply CL_B4_ExnConcat.
    apply AtomB4_Trans with (alpha := outer tau2)...
    inversion H302; solve by inversion.
    inversion H313b; solve by inversion.
    apply AtomB4_Trans with (alpha := outer tau3)...
    inversion H303; solve by inversion.
    inversion H314b; solve by inversion.
    intros. apply S_Refl.
  Case "E-Bind1". 
    admit. (* TODO after type schemes are worked into the subtyping relation *)
  Case "E-Bind2".
    admit. (* TODO after type schemes are worked into the subtyping relation *)
Qed.


